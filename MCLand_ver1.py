#!/usr/bin/python3
# The code for changing pages was derived from: http://stackoverflow.com/questions/7546050/switch-between-two-frames-in-tkinter
# License: MCLand is licensed under the GNU General Public License v2.0  

# The load SBML model file and converting SBML model to ODE model code was adapted from Frank Bergmann's Python code posted on sbml-discuss@googlegroups.com
# posted date: 20/10/2016 and the url is https://groups.google.com/forum/#!topic/sbml-discuss/inS4Lzp3Ri8
# Python package to generate list of ODEs from SBML model? -- Question asked by Jk Medley
# 

# Authors: Ket Hing Chong, Xiaomeng Zhang and Jie Zheng
# Last updated: 18 February 2020 (line number 105, 3520 and 3533: To reduce the calculation time and improve the default Waddington's Epigenetic Landscape)
# Biomedical Informatics Lab, School of Computer Science and Engineering
# Nanyang Technological University
# Singapore
# Jie Zheng is now Associate Professor in School of Information Science and Technology
# ShanghaiTech University, Pudong District, Shanghai 201210, China

# This MCLand software is written in Python 3 and it should be run on Anaconda 3 version 4.3.1
# Please refer to https://repo.continuum.io/archive/ to download a copy of the Anaconda 3
# You need to install the python-libsbml by using Anaconda Prompt.
# To install the libsbml package with conda run:
# conda install -c sbmlteam python-libsbml 

# For Linux user you may need to set the logo .ico file into .xbm file
# by commenting the line number 3309: tk.Tk.iconbitmap(self, default="MCL.ico")) and 
# uncommenting the line number 3310: #tk.Tk.wm_iconbitmap(self,bitmap="@ImageMCL.xbm").

from tkinter import simpledialog

# to save variables in Python using pickle module
import pickle 

# for File load model 
import time
from time import strftime, gmtime

import os

from tkinter.filedialog import askopenfilename

from random import randint

from tkinter import messagebox

import matplotlib

import PIL.Image
from PIL import ImageTk
#from PIL import Image, ImageTk

from matplotlib import cm

#from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2TkAgg

#from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg

from matplotlib.figure import Figure
import matplotlib.animation as animation
from matplotlib import style
from scipy.integrate import odeint

import tkinter as tk
from tkinter import ttk

import numpy as np
# To print a numpy array, I get a truncated representation, but I want the full array. So doing this setting will print full array
np.set_printoptions(threshold=np.inf)

from matplotlib import pyplot as plt

from pylab import *
from mpl_toolkits.mplot3d import Axes3D
from tkinter.constants import HORIZONTAL

# import for setting and running of Progressbar
from tkinter.ttk import Progressbar
import threading

from libsbml import *
import sys
from sklearn.decomposition import PCA
from scipy import interpolate

LARGE_FONT= ("Verdana", 12, "bold")
NORMAL_FONT = ("Helvetica", 10)
SMALL_FONT = ("Helvetica", 8)

style.use("ggplot")



class Model():
    def __init__(self):
        self.name = ''
        self.ode_file_name=''
        self.ode_content = ''
        self.type = ''
        self.calculated_U = 'no'
        self.toggle = 0
        
        self.geneName = ['P53','Mdm2']
        self.index_1 = 0 # P53
        self.index_2 = 1 # Zeb
        self.t_start = 0
        self.t_end = 30
        self.min_value = 0.0
        self.max_value = 2.0
        self.num_gene = 2
        self.TrajectoryNumber = 1000 # updated the default TrajectoryNumber to 10000 to get better Potential Landscape
        self.loopNum=0
        self.TempAttractors = np.zeros((self.TrajectoryNumber,self.num_gene))
        self.Attractors = np.zeros((1,1))
        self.gridNumber = 100
        self.X = ''
        self.Y = ''
        self.Z = ''
        # Z_d means Z values for default MCLand method
        self.Z_d = ''
        self.Z_PCA = ''
        self.PCA_Ratio = ''
        self.Smooth_U = ''
        self.SmoothSurfSize = 1
         
        # for ode model
        self.AllParameters=''
        self.ParameterName=[]
        self.ParameterValue=[]
        self.const=[]
        self.GeneDydtList =''
        self.rhsList=''
        self.DataOutputT=''
        self.initDataOutputT=''
        self.ode_initConds={}
        
        # for SBML model
        #self.doc =''
        self.doc_full_path=''
        self.Constants={}
        self.sbml_compartments=''
        self.sbml_reactions=''
        self.sbml_rhs=''
        self.sbml_initConds={}
        
        # set the initial conditions range
        self.fromInitialCondition = np.ones((1,self.num_gene))*self.min_value
        self.toInitialCondition = np.ones((1,self.num_gene))*self.max_value
        
        # set the initial values
        self.y = np.zeros((1,self.num_gene), dtype = 'float')
        # set the fixed time step for numerical integration using Runge-Kutta 4th order method
        self.h = 0.1
        # set initial time in numpy array format
        self.t = np.zeros((1,1))
        # for y values only without storing time
        self.output = self.y
        self.initOutput = self.y
        
        #print('self.t =',self.t)
        #print('self.y =', self.y)
        # for y values with storing time
        self.outputT = np.hstack((self.t, self.y))   
        
        # Timecourse Data without time t
        self.TimecourseData=np.zeros((int((self.t_end-self.t_start)/self.h+1),self.num_gene))
        
        self.PositionProb = np.zeros((self.gridNumber,self.gridNumber))
        self.MCLandPositionProb = np.zeros((self.gridNumber,self.gridNumber))
        
        # set the random initial conditions
        self.InitialConditions=np.zeros((self.TrajectoryNumber,self.num_gene))
 
        # storing number of protein to plot time course
        self.timeCourseToPlot=[]
        self.timeCourseToPlotColor=[]
        self.lineStyle=[]
        self.lineSize=[]

        self.XLabel='time'
        self.YLabel='protein levels'
        
        self.calculation_time=''
       
        #'''This loop get all the random initial conditions in the state space'''  
        for j in range(self.num_gene):
            #print(j)
            self.InitialConditions[:,j][:,None]=np.random.random((self.TrajectoryNumber,1))*(self.toInitialCondition[0,j]-self.fromInitialCondition[0,j])+self.fromInitialCondition[0,j]
            #print(self.InitialConditions)   
            
        
    def Calculate_PositionProb(self):
            # set the number of grid boxes in each axis
            print("Model class Calculate_PositionProb was called")
            global calculation_start 
            calculation_start = time.time()
            
            rowspan=(self.toInitialCondition[0,self.index_1]-self.fromInitialCondition[0,self.index_1])/self.gridNumber
            colspan=(self.toInitialCondition[0,self.index_2]-self.fromInitialCondition[0,self.index_2])/self.gridNumber

            print('calculating probability distribution...')    
            #print(len(self.InitialConditions))
            print('self.index_2:',self.index_2)

            for i in range(len(self.InitialConditions)):
                count_SimNum=i
                model.loopNum=i
              
                print('i=',i)
                #eachInitCond=np.hstack((t,InitialConditions[i,:][:,None].T))
                eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
                #print('eachInitCond=',eachInitCond)                
                
                # Here the self.y assignment is not required
                #self.y=eachInitCond
                self.output=eachInitCond
        
                # Get one trajectory time-course data
                #self.TimecourseData=RungeKutta4thIntVal(odeFunct,self.t_start,self.t_end,self.h,self.y,self.output)
                if model.type == 'ode':
                    self.TimecourseData = simulate_time_course_for_PosProb(self,i)
                    
                if model.type == 'SBML':
                    self.TimecourseData = sbml_simulate_time_course_for_PosProb(self,i)
                
                # to store in numpy array instead of list
                #allTrajectoriesLista.append(output)
                # in case you want to store to matrix
                # to store in a variable name for the matrix output e.g. matrix0 , matrix1, ...
                #foo='matrix'+str(i)
                #exec(foo + " = output")
                # More efficient is calculate the prob distribution without storing the matrix of trajectory
    

                #print('self.output.shape[0]=',self.output.shape[0])
                # for loop for projecting one trajectory into the plane and calculate the probability distribution
                for j in range(self.TimecourseData.shape[0]):
                    
                    if (self.TimecourseData[j,self.index_1]-self.fromInitialCondition[0,self.index_1]) !=NaN:    
                        #print('j',j)
                        row=int(floor((self.TimecourseData[j,self.index_1]-self.fromInitialCondition[0,self.index_1])/rowspan))+1
                        #print(row)
                        col=int(floor((self.TimecourseData[j,self.index_2]-self.fromInitialCondition[0,self.index_2])/colspan))+1
                        #print(col)
    
                        if (row >0 and row < self.gridNumber) and (col > 0 and col < self.gridNumber):
                
                            self.PositionProb[row,col]=self.PositionProb[row,col] + 1
                            #print(i,j)

                #self.output=self.y  
            model.calculated_U = 'yes'
            calculation_end =time.time()
            calculation_time = calculation_end - calculation_start 
            model.calculation_time = calculation_time
            print('Calculation time for potential values: %8.2f seconds' % calculation_time)
            return self.PositionProb

    def Interpolation_Landscape(self,xT,yT,U,XMin,XMax,YMin,YMax):
        f=interpolate.interp2d(xT,yT,U,kind='cubic')
        alpha=10 # factor
        Xnew=linspace(XMin,XMax,self.gridNumber*alpha)
        Ynew=linspace(YMin,YMax,self.gridNumber*alpha)
        Znew=f(Xnew,Ynew)
        [Xnew, Ynew] = meshgrid(Xnew, Ynew)
        return Xnew, Ynew, Znew

    def AverageU(self, AverU, size, stride):
        print("AverageU was called")
        m, n = AverU.shape
        for i in range(0, m - size + 1, stride):
            for j in range(0, n - size + 1, stride):
                avg = sum(sum(AverU[i:i + size, j:j + size])) / (size * size)
                for ii in range(i, i + size):
                    for jj in range(j, j + size):
                        AverU[ii, jj] = avg
        return AverU



    def Plotting_Landscape(self,XMin,XMax,YMin,YMax):
        print('Model object called to Plotting_Landscape')
        #print('self.gridNumber:', self.gridNumber)

        #print("Normalized probability")
        self.PositionProb = self.PositionProb + np.ones(self.PositionProb.shape)
        #m = self.PositionProb
        #ProbT = np.log(m, out=np.zeros_like(m), where=(m!=0))
        ProbT = self.PositionProb  # [0:99,0:99]
        normalized_ProbT = ProbT / (sum(sum(ProbT)))
        U = -np.log(normalized_ProbT)
        #U = -(normalized_ProbT)
        #print("U size:",U.shape)
        
        

        xT = linspace(XMin, XMax, self.gridNumber)
        yT = linspace(YMin, YMax, self.gridNumber)
        [X, Y] = meshgrid(xT, yT)

        # smoothing by interpolation, if need uncomment, if not need, comment this line
        # X, Y, U=self.Interpolation_Landscape(xT,yT,U,XMin,XMax,YMin,YMax)

        # smoothing by average U, if need uncomment, if not need, comment this line
        #Smooth_U=self.AverageU(U,size=4,stride=1)
        

        return X, Y, U
                  

# f for GraphPage (3D Landscape)
#f = Figure(figsize=(10,6), dpi=100)
f = Figure()
a = f.add_subplot(111, projection='3d')

# f2 for TimeCoursePage
f2 = Figure()
a2 = f2.add_subplot(111)

# f3 for PhasePlane_Page
f3 = Figure()
a3 = f3.add_subplot(111)

# f4 for GraphPage2 (Top View Landscape)
f4 = Figure()
a4 = f.add_subplot(111, projection='3d')

f5 = Figure(figsize=(10,0.5))
a5 = f5.text(0.5, 0.5, "phase plane will be plotted", bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)

#TblView= ttk.Treeview()
f6 = Figure(figsize=(7,7))
a6 = f6.text(0.1,0.1, "The zero matrix is the default dummy attractor.", bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
#a6 = f6.text(0.35,0.9, "Attractors", bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)

# f7 for time course plotting with user input initial conditions
f7 = Figure(figsize=(7,7))
a7 = f7.add_subplot(111)

# f8 for time course plotting with user input parameter values
f8 = Figure(figsize=(3.8,3.8))
a8 = f8.add_subplot(111)

# f9 for phase plane plotting with user input initial conditions or parameter values 
# PhasePlane_Page2
f9 = Figure(figsize=(5,5))
a9 = f9.add_subplot(111)

# f10 for initial conditions
f10=Figure(figsize=(7,7))
a10=f10.add_subplot(111)

# f11 for Graph page status
f11=Figure(figsize=(3,3))
a11=f11.add_subplot(111)

# f12 for 3D Graph for PCA
f12 = Figure(figsize=(5,5))
a12 = f12.add_subplot(111, projection='3d')

progressMessage=''

# The add_arrow function is obtained from the url below:
# https://stackoverflow.com/questions/34017866/arrow-on-a-line-plot-with-matplotlib
def add_arrow(line, position=None, direction='right', size=15, color=None):
    """
    add an arrow to a line.

    line:       Line2D object
    position:   x-position of the arrow. If None, mean of xdata is taken
    direction:  'left' or 'right'
    size:       size of the arrow in fontsize points
    color:      if None, line color is taken.
    """
    if color is None:
        color = line.get_color()

    xdata = line.get_xdata()
    ydata = line.get_ydata()

    if position is None:
        #position = xdata.mean()
        position = (xdata.min() + xdata.max() )/2
    # find closest index
    start_ind = np.argmin(np.absolute(xdata - position))
    if direction == 'right':
        end_ind = start_ind + 1
    else:
        end_ind = start_ind - 1

    line.axes.annotate('',
        xytext=(xdata[start_ind], ydata[start_ind]),
        xy=(xdata[end_ind], ydata[end_ind]),
        arrowprops=dict(arrowstyle="->", color=color),
        size=size
    )



def pop_up_msg(msg):
    popup = tk.Tk()
    popup.wm_title("No model loaded!. Please load a model equation first.")
    label = ttk.Label(popup, text=msg, font=NORMAL_FONT)
    label.pack(side="top", fill="x", pady=10, padx=10)
    B1 = ttk.Button(popup, text="Okay", command = popup.destroy)
    B1.pack()
    popup.mainloop()

# Show Page
def show_start_page(self):
    #print('radioBtnVal:',radioBtnVal.get() ) # selected value
    self.show_frame(StartPage)

def show_info_page(self):
    self.show_frame(InfoPage)

def show_ode_editor(self):
    #print('radioBtnVal:',radioBtnVal.get() ) # selected value    
    self.show_frame(NewODEPage)
    
# Show Model Setting
def show_model_setting(self):
    '''Show model setting'''
    self.show_frame(SettingPage)
    pass

def show_method_setting(self):
    self.show_frame(MethodSettingPage)

def show_time_course(self):
    self.show_frame(TimeCoursePage)

def show_phase_plane(self):
    self.show_frame(PhasePlane_Page)
    
def show_landscape(self):
    self.show_frame(Graph_Page)

def show_set_initial_conditions(self):
    print('radioBtnVal:',radioBtnVal.get() ) # selected value    
    self.show_frame(InitConditionsPage2)

def show_set_parameter_values(self):
    self.show_frame(ParameterPage)
    
def show_time_course2(self):
    self.show_frame(InitTimeCoursePage2)

def show_phase_plane2(self):
    self.show_frame(PhasePlane_Page2)
    
# New ode file model
def new_odeFile(self):
    '''create new ode file model'''
    self.show_frame(NewODEPage) 
    pass

#This is where we lauch the file manager bar.
def open_file(self):
    '''loading ode model from filename ends with .ode'''
    model.type ='ode'
    model.const = []
    model.ode_initConds = {}
    model.loopNum=1

    global full_path
    

    full_path = askopenfilename(initialdir="C:/Users/CHONGKETHING/Documents/LiClipse Workspace/TestPython3_MonteCarloLand/",
                           filetypes =(("ode File", "*.ode"),("All Files","*.*")),
                           title = "Choose a file."
                           )
    print (full_path)
        

    #Using try in case user types in unknown file or closes without choosing a file.
    try:
        with open(full_path,'r') as UseFile:
            print(UseFile.read())
                                
            base=os.path.split(full_path)[1]
            
            # filename without .ode extension
            filename=os.path.splitext(base)[0]
            print(filename)
            
            global odeLoad_modelName
            odeLoad_modelName=filename            
            
    except:
        print("No file exists")
    

    fopen =open(full_path,"r")

    lines = fopen.readlines() 
    # exclude the comment line and the setting line that starts with #  and @ respetctively
    #print(type(lines))==>list
    for line in list(lines):
        if line[0]=='#' or line[0]=='@':
            lines.remove(line)
    
    #print('lines=', lines)
    fopen.close()  
    
    global noGene
    global GeneDydtList
    global AllParameters
    global VariableName
    global rhsList
    noGene=0
    GeneDydtList=[]
    VariableNameList=[]
    ParList=[]
    ParValue=[]
    AllParameters=[]
    rhsList=[]

    model.ParameterName=[]
    model.ParameterValue=[]
    for line in list(lines):
        #line=line.lower()
        #print("line=",line,"line.find('par')=",line.find('par'))
        
        if line.find('par') ==0: # or line.find('p') ==0:
            line_in_list=line
            #print(len(line_in_list))
            #par=line.split(' ')[1]
            # if you want the first word only (which means passing 1 as second argument), you can use None as the first argument: s.split(None, 1)
            par=line_in_list.split(None,1)[1]
            
            par1=par.replace(",",";")
            
            # to collect the parameter name and parameter value and store in ParList and ParValue respectively.
            string1=par1.replace(";",'')
            string2 = string1.split()
            for Parstring in string2:
                print('Parstring:',Parstring)
                parName, parValue = Parstring.split("=")
                print('par:',parName, 'value:',parValue)
                ParList.append(parName)
                model.ParameterName.append(parName)
                ParValue.append(parValue)
                model.ParameterValue.append(parValue)
            
            AllParameters.append(par1)
            #print('par1:',par1)
            #f.write(str(par1))
            #print('line=', line)
            
        #if line.find('p') ==0:
        #    #par2=line.split(' ')[1]
        #    par2=line.split(None,1)[1]
        #    par3=par2.replace(",",";")
        #    f.write(str(par3))
        
        #print('find no of variable')
        #print(line.find("'"))
        #print('find no of variable')
        #print(line.find("/dt"))  
        
        # find no of variable and variable name for equation define by x'
        if line.find("'") > 0:
            #print('found one variable.')
            noGene +=1
            GeneDydtList.append(line)
            varName=line.split('=')[0]
            varName2=varName.replace("'",'')
            VariableNameList.append(varName2)
            # rhs
            varName_rhsTemp=line.split('=')[1]
            varName_rhs=varName_rhsTemp.replace("\n",'')
            # replace the '^' with '**' for power symbol in Python
            varName_rhs_2=varName_rhs.replace("^","**")
            rhsList.append(varName_rhs_2)
            #print(varName_rhs_2)
 
        # find no of variable and variable name for eqn define by dx/dt'
        if line.find('/dt') > 0:
            print('found one variable.')
            noGene +=1
            GeneDydtList.append(line)
            # get the LHS of the eqn
            varName3=line.split('=')[0]  
            # get the first part dy of the dy/dt            
            varName4=varName3.split('/')[0]
            # delete the 'd'
            
            #varName5=varName4.replace("d",'')
            temptList=list(varName4)
            # delete the first 'd'
            temptList.pop(0)            
            varName5="".join(temptList)
            
            VariableNameList.append(varName5)
            # get the rhs of the eqn
            varName_rhsTemp=line.split('=')[1] 
            # delete the "\n"
            varName_rhs=varName_rhsTemp.replace("\n",'')
            # replace the '^' with '**' for power symbol in Python
            varName_rhs_2=varName_rhs.replace("^","**")
            rhsList.append(varName_rhs_2)
            print(varName_rhs_2)
            
        # for constants 
        if line.find('const') ==0:
            line_const_list=line
            #print(len(line_in_list))
            #par=line.split(' ')[1]
            # if you want the first word only (which means passing 1 as second argument), you can use None as the first argument: s.split(None, 1)
            constant=line_const_list.split(None,1)[1]            
            model.const.append(constant)
            
        # for initial Conditions 
        if line.find('init') ==0:
            line_init_list=line
            #print(len(line_in_list))
            #par=line.split(' ')[1]
            # if you want the first word only (which means passing 1 as second argument), you can use None as the first argument: s.split(None, 1)
            init=line_init_list.split(None,1)[1]       
            
            # to collect the init variable name and init value and store in ParList and ParValue respectively.
            stringinit1=init.replace(",",'')
            stringinit2 = stringinit1.split()
            for Parstring in stringinit2:
                #print('Parstring:',Parstring)
                initName, initValue = Parstring.split("=")
                model.ode_initConds[initName]=initValue
    print('model.ode_initConds:',model.ode_initConds)            
    print('model.const:',model.const)
    
    VariableName=VariableNameList    
    #print('found no. of %d variable.' % noGene)
    #print('GeneDydtList:',GeneDydtList)
    #print('VariableNameList:',VariableNameList)
    #print('rhsList:',rhsList)
    #print('AllParameters:',AllParameters)
    #print('ParList:',ParList)
    #print('ParValue:',ParValue)

    odeFile_Loaded=True
       
    if odeFile_Loaded==True:
        model.name= odeLoad_modelName
        print("model name updated.") 
        print("model name:", model.name)
        model.num_gene=noGene
        print('model.num_gene:', model.num_gene)
        model.index_1=0
        model.index_2=1
        model.min_value=0
        model.max_value=3
        model.geneName=VariableNameList
        model.AllParameters= AllParameters
        model.GeneDydtList = GeneDydtList
        model.rhsList=rhsList

        #print('VariableNameList:',VariableNameList)
        print('VariableName:',VariableName)

        # update the Window title  
        if model.type =='SBML':
            ModelType='xml'
        if model.type =='ode':
            ModelType='ode'        
        tk.Tk.wm_title(self, '{} - {}'.format(model.name+'.'+ModelType,"MCLand: Waddington's Epigenetic Landscape Drawing App") )
        
        model.fromInitialCondition = np.ones((1,model.num_gene))*model.min_value
        model.toInitialCondition = np.ones((1,model.num_gene))*model.max_value
        
        model.y=np.zeros((1,model.num_gene), dtype = 'float')
        model.t=np.zeros((1,1))
        model.output=model.y
        model.outputT= np.hstack((model.t,model.y))
        
        # for storing simulated results 
        model.TimecourseData=np.zeros((int((model.t_end-model.t_start)/model.h+1),model.num_gene))
        model.PositionProb = np.zeros((model.gridNumber,model.gridNumber))
        model.MCLandPositionProb = np.zeros((model.gridNumber,model.gridNumber))
        model.InitialConditions=np.zeros((model.TrajectoryNumber,model.num_gene))
        model.timeCourseToPlot=[]
        model.timeCourseToPlotColor=[]
        model.lineStyle=[]
        model.lineSize=[]
        
        #'''This loop get all the random initial conditions in the state space'''  
        for j in range(model.num_gene):
            #print(j)
            model.InitialConditions[:,j][:,None]=np.random.random((model.TrajectoryNumber,1))*(model.toInitialCondition[0,j]-model.fromInitialCondition[0,j])+model.fromInitialCondition[0,j]
            #print(model.InitialConditions)   
        
       
        model.TempAttractors=np.zeros((model.TrajectoryNumber,noGene))
        
        # clear 3D landscape graph
        f.clear()
        f.add_subplot(111, projection='3d')
        f.canvas.draw_idle()  
        
        # clear time course graph
        f2.clear()
        f2.add_subplot(111)
        f2.canvas.draw_idle()  

        # clear phase plane graph
        f3.clear()
        f3.add_subplot(111)
        f3.canvas.draw_idle()     
        
        # clear top view graph
        f4.clear()
        f4.add_subplot(111)
        f4.canvas.draw_idle()    

        # clear init time course 2 graph
        f8.clear()
        f8.add_subplot(111)
        f8.canvas.draw_idle()  

        # clear phase plane 2 graph
        f9.clear()
        f9.add_subplot(111)
        f9.canvas.draw_idle()          
        #app.update()
        
        # clear PCA graph
        f12.clear()
        f12.add_subplot(111)
        f12.canvas.draw_idle()         

        app.show_frame(SettingPage)


def open_sbml_file(self):
    '''loading SBML model from filename ends with .xml'''
    model.type ='SBML'
    model.Constants ={}
    model.sbml_initConds = {}
    model.loopNum=1
    # global full_path2
    

    full_path2 = askopenfilename(initialdir="C:/Users/CHONGKETHING/Documents/LiClipse Workspace/TestPython3_MonteCarloLand/",
                           filetypes =(("SBML File", "*.xml"),("All Files","*.*")),
                           title = "Choose a file."
                           )
    print (full_path2)
    
    

    #Using try in case user types in unknown file or closes without choosing a file.
    try:
        with open(full_path2,'r') as UseFile:
            print(UseFile.read())
                                    
            base=os.path.split(full_path2)[1]
            
            # filename without .xml extension
            sbml_filename=os.path.splitext(base)[0]
            print(sbml_filename)
            
            global sbml_Loaded_modelName
            sbml_Loaded_modelName=sbml_filename           
            
    except:
        print("No file exists")   
    
    # The following section of code is adapted from Frank Bergmann Python code for using libSBML to convert SBML model
    # to ODE model for time course integration using scipy odeint
    global doc
    doc = readSBMLFromFile(full_path2)
    
    #model.doc = doc
    model.doc_full_path=full_path2
    
    if doc.getNumErrors(LIBSBML_SEV_FATAL):
        
        print('Encountered serious errors while reading file')
        print(doc.getErrorLog().toString())
        sys.exit(1)


    
    # clear errors
    doc.getErrorLog().clearLog()
  
    #
    # perform conversions
    #
    props = ConversionProperties()
    props.addOption("promoteLocalParameters", True)
  
    if doc.convert(props) != LIBSBML_OPERATION_SUCCESS: 
        print('The document could not be converted')
        print(doc.getErrorLog().toString())
    
    props = ConversionProperties()
    props.addOption("expandInitialAssignments", True)
  
    if doc.convert(props) != LIBSBML_OPERATION_SUCCESS: 
        print('The document could not be converted')
        print(doc.getErrorLog().toString())
    
    props = ConversionProperties()
    props.addOption("expandFunctionDefinitions", True)
  
    if doc.convert(props) != LIBSBML_OPERATION_SUCCESS: 
        print('The document could not be converted')
        print(doc.getErrorLog().toString())

    # Ket use to test if reading SBML model successful
    mod = doc.getModel()    
    
    #global variables_name
    variables_name = []  
    
    for i in range(mod.getNumSpecies()):
        species = mod.getSpecies(i)
        # Ket modified added the following 2 lines for checking correct number of variables by excluding BoundaryCondition=True
        if species.getBoundaryCondition() == True: 
            continue
        variables_name.append(species.getId())
    
    print('variables_name=', variables_name)
    

    # for recording sbml ode
    #global sbml_compartments
    sbml_compartments =[]
    # write out compartment values
    for i in range(mod.getNumCompartments()):
        element = mod.getCompartment(i)
        sbml_compartments.append('{0} = {1}\n'.format(element.getId(), element.getSize()) )   
    
    model.sbml_compartments=sbml_compartments
    
    global sbml_AllParameters
    sbml_AllParameters =[]
    model.ParameterName=[]
    model.ParameterValue=[]    

    # write out parameter values
    #concatenated_code_sbml_ode=''    
    sbml_AllParameters.append('\nglobal parameters\n')
    for i in range(mod.getNumParameters()):
        element = mod.getParameter(i)
        sbml_AllParameters.append('{0} = {1}\n'.format(element.getId(), element.getValue()))
        #concatenated_code_sbml_ode=concatenated_code_sbml_ode + '  {0} = {1}\n'.format(element.getId(), element.getValue())
        
        # add to the parameter name and parameter value
        model.ParameterName.append(element.getId())
        model.ParameterValue.append(element.getValue())
    
    # assign all parameters to model object
    model.AllParameters=sbml_AllParameters
 
    
    #global sbml_rhs 
    sbml_rhs = []
    global sbml_reactions
    sbml_reactions = []
    sbml_reactions.append('\n')

    variables = {}
  
    for i in range(mod.getNumSpecies()): 
        print('i:',i)

        species = mod.getSpecies(i)
        print(species)
        # Ket modified the code below; original species.getBoundaryCondition() == True
        if species.getBoundaryCondition() == True or (species.getId() in variables): # variables.has_key(species.getId()): has_key only can be used in Python 2
            print(species.getId())
            print(species.getBoundaryCondition())
            continue
        variables[species.getId()] = []    
    
    #print('no. reactions',mod.getNumReactions())
    for i in range(mod.getNumReactions()): 
        reaction = mod.getReaction(i)
        kinetics = reaction.getKineticLaw()  
         
        #print('reaction.getId():',reaction.getId())
        #print('kinetics.getFormula():',kinetics.getFormula())
        sbml_reactions.append(str(reaction.getId()) + '=' + str(kinetics.getFormula())+'\n' )

        for j in range(reaction.getNumReactants()): 
            ref = reaction.getReactant(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('-{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('-({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
                print('reaction.getId():',reaction.getId())
        for j in range(reaction.getNumProducts()): 
            ref = reaction.getProduct(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
    
    model.sbml_reactions=sbml_reactions            
    #sbml_reactions.append('\n')
    #sbml_rhs.append('    return array([')
    
    variableList=list(variables.keys())
    #print(len(variables.keys()))
    #print(variables.keys())
    
    correct_variableName=[]
    
    print('Reading reactions...')
    k=0
    for i in range(len(variables.keys())):
        print('i:',i)
        print('variables_name[i]:',variables_name[i])
        sbml_rhs.append('d'+variables_name[i]+'/dt=')
        k=k+1
        for eqn in variables[variableList[i]]:  #         for eqn in variables[variables.keys()[i]]:
            print('eqn:',eqn)
            print(variables[variableList[i]])
            sbml_rhs.append(' + ({0})'.format(eqn) )

            pass

        # For constants where there is ode rhs is empty, set the ode rhs to 0.
        # and we need to set the constant based on their initialConcentration value.
        if len(variables[variableList[i]])==0:
            # first set the ode rhs to 0
            sbml_rhs.append('0')
            
            # set the constant based on their InitialConcentration
            element = mod.getSpecies(i)
            print('element:',element)
            model.Constants[element.getId()]= element.getInitialAmount() 
            #model.Constants[variables[variableList[i]]=
            print(element.getId())
            print(element.getInitialAmount())
            print(variables[variableList[i]])
            
        else:
            correct_variableName.append(variables_name[i])

        if i + 1 < len(variables.keys()):
            pass
               
            sbml_rhs.append('\n')
    #sbml_rhs.append('    ])\n' )   
    model.sbml_rhs=sbml_rhs
    print(model.sbml_rhs)
    print('correct_variableName:',correct_variableName)
 
    variables_name=correct_variableName
    
# Ket modify this for correct constants
    # This loop to add constants to the model object
    for i in range(mod.getNumSpecies()):
        print('Check constants i:',i)

        element = mod.getSpecies(i)
        print(element)
        # Ket modified to True original if element.getBoundaryCondition() == False:
        if element.getBoundaryCondition() == False:
            if element.getId() not in variables_name:
                model.Constants[element.getId()]=element.getInitialConcentration()
            continue 
        if element.isSetInitialConcentration(): 
            model.Constants[element.getId()]=element.getInitialConcentration()
            print(element.getId())
            print(element.getInitialConcentration())
        else:
            model.Constants[element.getId()]= element.getInitialAmount() 
     
    # to extract initial conditions
    print('mod.getNumSpecies():',mod.getNumSpecies())
    for i in range(mod.getNumSpecies()):
        element = mod.getSpecies(i)
        model.sbml_initConds[element.getId()]= element.getInitialConcentration()
        
    print('model.sbml_initConds:',model.sbml_initConds)
       
 
    model.name = sbml_Loaded_modelName 
    model.num_gene = len(variables_name)
    model.index_1=0
    model.index_2=1
    model.min_value = 0
    model.max_value =3
    model.geneName = variables_name
    
    model.timeCourseToPlot=[]
    model.timeCourseToPlotColor=[]
    model.lineStyle=[]
    model.lineSize=[]    
    
    model.fromInitialCondition = np.ones((1,model.num_gene))*model.min_value
    model.toInitialCondition = np.ones((1,model.num_gene))*model.max_value
        
    model.y=np.zeros((1,model.num_gene), dtype = 'float')
    model.t=np.zeros((1,1))
    model.output=model.y
    model.outputT= np.hstack((model.t,model.y))
        
    model.TimecourseData=np.zeros((int((model.t_end-model.t_start)/model.h+1),model.num_gene))
    model.PositionProb = np.zeros((model.gridNumber,model.gridNumber))
    model.InitialConditions=np.zeros((model.TrajectoryNumber,model.num_gene))

    # update the Window title
    if model.type =='SBML':
        ModelType='xml'
    if model.type =='ode':
        ModelType='ode'
    tk.Tk.wm_title(self, '{} - {}'.format(model.name+'.'+ModelType,"MCLand: Waddington's Epigenetic Landscape Drawing App") )
        
    #'''This loop get all the random initial conditions in the state space'''  
    for j in range(model.num_gene):
        #print(j)
        model.InitialConditions[:,j][:,None]=np.random.random((model.TrajectoryNumber,1))*(model.toInitialCondition[0,j]-model.fromInitialCondition[0,j])+model.fromInitialCondition[0,j]
        #print(model.InitialConditions)           
     
    model.TempAttractors=np.zeros((model.TrajectoryNumber,model.num_gene))

    # clear 3D landscape graph
    f.clear()
    f.add_subplot(111,projection='3d')
    f.canvas.draw_idle()

    # clear time course graph
    f2.clear()
    f2.add_subplot(111)
    f2.canvas.draw_idle()     
    # clear phase plane graph
    f3.clear()
    f3.add_subplot(111)
    f3.canvas.draw_idle()  

    # clear top view graph
    f4.clear()
    f4.add_subplot(111)
    f4.canvas.draw_idle()   

    # clear init time course 2 graph
    f8.clear()
    f8.add_subplot(111)
    f8.canvas.draw_idle()  
    
    # clear phase plane 2 graph
    f9.clear()
    f9.add_subplot(111)
    f9.canvas.draw_idle()      
    
    app.show_frame(SettingPage)

def open_mc_land_file(self):
    full_path = askopenfilename(initialdir="C:/Users/CHONGKETHING/Documents/LiClipse Workspace/TestPython3_MonteCarloLand/",
                           filetypes =(("pickle File", "*.pckl"),("All Files","*.*")),
                           title = "Choose a file."
                           )
    print (full_path)
    base=os.path.split(full_path)[1]
    
    # filename without .ode extension
    filename=os.path.splitext(base)[0]
    print(filename)    
    

    #Using try in case user types in unknown file or closes without choosing a file.
    #try:
    #    with open(full_path,'r') as UseFile:
    #        print(UseFile.read())
                        

            
    #        base=os.path.split(full_path)[1]
            
            # filename without .ode extension
    #        filename=os.path.splitext(base)[0]
    #        print(filename)
            
    #        global MC_LandLoaded_modelName
    #        MC_LandLoaded_modelName=filename

            
            
    #except:
    #    print("No file exists")
    

    fopen =open(full_path,'rb')
    #fopen =open(filename+'.pckl','rb')
    #lines = fopen.readlines() 
    global model
    model = pickle.load(fopen)
    
    print(model.name)
    
    # to reload SBML file
    if model.type == 'SBML':
        global doc
        doc = readSBMLFromFile(model.doc_full_path)
        global mod
        mod = doc.getModel()  
        

    
    a = f.add_subplot(111, projection='3d')

    a.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
    #print(model.index_1)
    a.set_xlabel(str(model.geneName[model.index_1]))
    a.set_ylabel(str(model.geneName[model.index_2]))
    #a.set_ylabel('y')
    a.set_zlabel("U")
    f.canvas.draw_idle()

    # to plot top view into f4 GraphPage2

    a4 = f4.add_subplot(111, projection='3d')
    a4.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
    # add contour to the 3D surface plot
    #a.contour(X, Y, Z, zdir='z', offset=0, cmap='jet')
    #print(model.index_1)
    a4.set_xlabel(str(model.geneName[model.index_1]))
    a4.set_ylabel(str(model.geneName[model.index_2]))
    #a.set_ylabel('y')
    a4.set_zlabel("U")    
    a4.view_init(elev=90, azim=-90)
    f4.canvas.draw_idle()    
    #print('lines=', lines)
    
    fopen.close()    
    
    f6.clear()
    a6 = f6.text(0.35,0.9, "Number of Attractors="+str(len(model.Attractors)), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
    #for i in range(len(model.Attractors)):
    #    a6 = f6.text(0.35,0.5, str(model.Attractors[i]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
    a6 = f6.text(0.35,0.5, str(model.Attractors), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
    a6 = f6.text(0.1,0.1, "The zero matrix is the default dummy attractor.", bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
    #f6.canvas.draw_idle

    # update the Window title 
    if model.type =='SBML':
        ModelType='xml'
    if model.type =='ode':
        ModelType='ode'      
    tk.Tk.wm_title(self, '{} - {}'.format(model.name+'.'+ModelType,"MCLand: Waddington's Epigenetic Landscape Drawing App") )
    
    #app.show_frame(Graph_Page)
    app.show_frame(SettingPage)
        

def save_mc_land_file(self):
    
    if model.type == 'ode':
        #mc_filehandler = open(str(odeLoad_modelName)+'.pckl', 'wb')
        #mc_filehandler = open(str(odeLoad_modelName)+strftime("%Y-%m-%d %H %M %S", gmtime())+'.pckl', 'wb')
        pass
    if model.type == 'SBML':
        #mc_filehandler = open(str(sbml_Loaded_modelName)+'.pckl', 'wb')
        #mc_filehandler = open(str(sbml_Loaded_modelName)+strftime("%Y-%m-%d %H %M %S", gmtime())+'.pckl', 'wb')
        pass
    
    save_as()
    
    def write_to_file(self,file_name):
        try:
            #np.savetxt(file_name, model.DataOutputT, delimiter=",", fmt='%10.5f')
            file_nameMCL=open(file_name+'pckl', 'wb')
            pickle.dump(model, file_nameMCL)
            file_nameMCL.close
            
            tk.messagebox.showinfo("Your MCLand model landscape data have been saved.","Your landscape data have been saved into the file name + model_name + current time.pckl.")   
        except IOError:
            tkinter.messagebox.showwarning("Save", "Could not save the file.")


    def save_as(self,event=None):
        input_file_name = tk.filedialog.asksaveasfilename(defaultextension=".csv",
                                                               filetypes=[("CSV file", "*.csv")])
        if input_file_name:
            global file_name
            file_name = input_file_name

            self.write_to_file(file_name)
            #root.title('{} - {}'.format(os.path.basename(file_name), PROGRAM_NAME))
        return "break"
    



def Save_method_setting(self):
    print("Save_method_setting was called.")

def calculate_potential_U(self):
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
    else:
        f.text(0.5,0.5, 'calculating potential landscape ...', bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        model.Calculate_PositionProb() 
#        global X
#        global Y
#        global Z
        model.X, model.Y, model.Z = model.Plotting_Landscape()
        
#        model.X = X
#        model.Y = Y
#        model.Z = Z
        
        Attractors= np.vstack({tuple(row) for row in model.TempAttractors})
        model.Attractors = Attractors
        print('Number of attractors=', len(Attractors))
        print('Attractors:')
        print(Attractors)
 
        # Plot 3D graph
         
        # to plot 3D view into f GraphPage
        f.clear()
       
        a = f.add_subplot(111, projection='3d')
        a.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
        #print(model.index_1)
        a.set_xlabel(str(model.geneName[model.index_2]))
        a.set_ylabel(str(model.geneName[model.index_1]))
        #a.set_ylabel('y')
        a.set_zlabel("U")
        f.canvas.draw_idle()
       
        # to plot top view into f4 GraphPage2
       
        a4 = f4.add_subplot(111, projection='3d')
        a4.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
        # add contour to the 3D surface plot
        #a.contour(X, Y, Z, zdir='z', offset=0, cmap='jet')
        #print(model.index_1)
        a4.set_xlabel(str(model.geneName[model.index_2]))
        a4.set_ylabel(str(model.geneName[model.index_1]))
        #a.set_ylabel('y')
        a4.set_zlabel("U")    
        a4.view_init(elev=90, azim=-90)
        f4.canvas.draw_idle()       
        
      
def plot_3D_graph(self):
    '''Plot 3D graph '''
    print("plot_3D_graph was called")

    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    elif model.calculated_U == 'no':
        tk.messagebox.showinfo("No potential values found.","Please calculate the potential values first.")
    
    else:    
        #model.Calculate_PositionProb() 
        #X, Y, Z=model.Plotting_Landscape()  
        
        # to plot 3D view into f GraphPage
        f.clear()
    
        a = f.add_subplot(111, projection='3d')
    
        model.surf=a.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
        #print(model.index_1)
        a.set_xlabel(str(model.geneName[model.index_2]))
        a.set_ylabel(str(model.geneName[model.index_1]))
        #a.set_ylabel('y')
        a.set_zlabel("U")
        f.canvas.draw_idle()
    
        # to plot top view into f4 GraphPage2
    
        a4 = f4.add_subplot(111, projection='3d')
        a4.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
        # add contour to the 3D surface plot
        #a.contour(X, Y, Z, zdir='z', offset=0, cmap='jet')
        #print(model.index_1)
        a4.set_xlabel(str(model.geneName[model.index_2]))
        a4.set_ylabel(str(model.geneName[model.index_1]))
        #a.set_ylabel('y')
        a4.set_zlabel("U")    
        a4.view_init(elev=90, azim=-90)
        f4.canvas.draw_idle()


    
def plot_topView_graph(self):
    print("plot_topView_graph was called")
    
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    else:
        model.Calculate_PositionProb() 
        model.X, model.Y, model.Z = model.Plotting_Landscape()  
     
        a4 = f4.add_subplot(111, projection='3d')
    
        a4.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
        #print(model.index_1)
        a4.set_xlabel(str(model.geneName[model.index_2]))
        a4.set_ylabel(str(model.geneName[model.index_1]))
        #a.set_ylabel('y')
        a4.set_zlabel("U")
        a4.view_init(elev=90, azim=-90)
        f4.canvas.draw_idle()

        # also plot the 3D view 
        a = f.add_subplot(111, projection='3d')
    
        a.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
        #print(model.index_1)
        a.set_xlabel(str(model.geneName[model.index_1]))
        a.set_ylabel(str(model.geneName[model.index_2]))
        #a.set_ylabel('y')
        a.set_zlabel("U")
        f.canvas.draw_idle()


        
def simulate_time_course(self):
    print("simulate_time_course was called.")
    global random_num_n
    random_num_n = randint(0, model.TrajectoryNumber-1) 
    
    print('Random Initial Condition:', model.InitialConditions[random_num_n,:][:,None].T)
    temp_random_init_d=model.InitialConditions[random_num_n,:][:,None].T
    
    # to get random initial condition in a list
    temp_random_init_c=[]
    for i in range(temp_random_init_d.shape[1]):
        temp_random_init_c.append(temp_random_init_d[0][i])
    
    # to get random initial condition in an array    
    global random_init
    random_init=np.asarray(temp_random_init_c)

    concatenate_code=''
    concatenate_code= concatenate_code + 'def simulateModel(t0, tend, h):\n'
    concatenate_code= concatenate_code + '    def odefunc(Y,t):\n'
#    concatenate_code= concatenate_code + '        x = Y[0]\n'
#    concatenate_code= concatenate_code + '        y = Y[1]\n'
    for i in range(len(model.geneName)):
        concatenate_code= concatenate_code + '        {0} = Y[{1}]\n'.format(model.geneName[i],i)
        #print('        {0} = Y[{1}]\n'.format(VariableName[i],i))
    concatenate_code= concatenate_code + '        dy=np.zeros(({0}), dtype="float")\n'.format(model.num_gene)
#    concatenate_code= concatenate_code + '        dy[0]=-1+9*x-2*x**3+9*y-2*y**3\n'
#    concatenate_code= concatenate_code + '        dy[1]=1-11*x+2*x**3+11*y-2*y**3\n'  

# updated with user key in parameter values
    for i in range(len(model.ParameterName)):
        concatenate_code= concatenate_code + '        {0}={1}\n'.format(model.ParameterName[i],model.ParameterValue[i])

# updated with constants or functions
    for i in range(len(model.const)):
        #print('model.const:',model.const[i])
        concatenate_code= concatenate_code + '        {0}\n'.format(model.const[i])
        #self.ode_Eqn_Text.insert(tk.INSERT, model.const[i])
    concatenate_code= concatenate_code + '        \n'

# original code for parameter values
#    for i in range(len(model.AllParameters)):
#        concatenate_code= concatenate_code + '        {0}\n'.format(model.AllParameters[i])
        #print('        {0}\n'.format(AllParameters[i]))
    for i in range(len(model.rhsList)):
        concatenate_code= concatenate_code + '        dy[{0}]={1}\n'.format(i,model.rhsList[i])
        #print('        dy[{0}]={1}\n'.format(i,rhsList[i]))
    concatenate_code= concatenate_code + '        return dy\n'
    concatenate_code= concatenate_code + '    numPoints = (tend - t0)/h + 1\n'     
    concatenate_code= concatenate_code + '    time = linspace(t0, tend, numPoints)\n'
#    concatenate_code= concatenate_code + '    n = randint(0, model.TrajectoryNumber-1)\n'
    concatenate_code= concatenate_code + '    eachInitCond = random_init\n' #{0}\n'.format(d) #model.InitialConditions[n,:][:,None].T\n                                         
#    concatenate_code= concatenate_code + '    yinit = np.array([1.30535752, 0.44290278])\n' 
    concatenate_code= concatenate_code + '    yinit = eachInitCond\n' #.format(eachInitCond)
    concatenate_code= concatenate_code + '    y = odeint(odefunc, yinit, time)\n'  
    concatenate_code= concatenate_code + '    return random_num_n, time, y\n'                                                        
    # h = 0.1    
    #    yinit = np.array([0.10130762, 2.98803187])    
    
    #h=model.h
    #t0=model.t_start
    #tend=model.t_end
    #n, time1, result1 = simulateModel(t0,tend, h)
    concatenate_code= concatenate_code + 'h={0}\n'.format(model.h)
    concatenate_code= concatenate_code + 't0={0}\n'.format(model.t_start)
    concatenate_code= concatenate_code + 'tend={0}\n'.format(model.t_end)
    concatenate_code= concatenate_code + 'global time1\n' 
    concatenate_code= concatenate_code + 'global result1\n' 
    concatenate_code= concatenate_code + 'random_num_n, time1, result1 = simulateModel(t0,tend, h)\n'            
    exec(concatenate_code)  
    #print('end point result1[-1,:]=',result1[-1,:])
    #print('result1[-2,:]=',result1[-2,:])
    #euclidean_dist = np.linalg.norm(result1[-1,:]-result1[-2,:])
    #print('euclidean_dist',euclidean_dist)  
    
    #TempStableSteadyState=[]

    
#    if euclidean_dist < 1e-5: 
#        if len(StableSteadyState) == 0:
#            global TempAttractors
#            TempAttractors=np.zeros((1,noGene))   
            
#        tempRow=np.array([result1[-1,:]])
#        print('tempRow:',tempRow)
#        print('stable steady state is reached:',result1[-1,:])
 #       if len(StableSteadyState) == 0:
 #           StableSteadyState.append(np.round(result1[-1,:],4))
 #       for i in range(len(StableSteadyState)):
 #           euclidean_dist2 = np.linalg.norm(np.round(result1[-1,:],4)-np.round(StableSteadyState[i],4))
 #           print('euclidean_dist2',euclidean_dist2) 
 #           if euclidean_dist2 !=0:
 #               TempStableSteadyState=(np.round(result1[-1,:],4))
 #           
 #               for j in range(len(StableSteadyState)):
 #                   if np.array_equal(TempStableSteadyState, StableSteadyState[j]):
 #                       pass
 #                   else:
 #                       StableSteadyState.append(TempStableSteadyState)
 #       StableSteadyState.append(TempRow)
#       TempAttractors=np.concatenate((TempAttractors, tempRow),axis=0)
#    print('Attractors:',TempAttractors)
    
    return random_num_n, time1, result1

def initConds_simulate_time_course(self):
    ''' simulate time course data with user input initial conditions'''
    #print("initConds_simulate_time_course was called.")
    
    temp_random_init_d=model.y
    
    # to get random initial condition in a list
    temp_random_init_c=[]
    for i in range(temp_random_init_d.shape[1]):
        temp_random_init_c.append(temp_random_init_d[0][i])
    
    # to get user key in initial condition in an array    
    global user_init
    user_init=np.asarray(temp_random_init_c)

    concatenate_code=''
    concatenate_code= concatenate_code + 'def simulateModel(t0, tend, h):\n'
    concatenate_code= concatenate_code + '    def odefunc(Y,t):\n'

    for i in range(len(model.geneName)):
        concatenate_code= concatenate_code + '        {0} = Y[{1}]\n'.format(model.geneName[i],i)
        #print('        {0} = Y[{1}]\n'.format(VariableName[i],i))
    concatenate_code= concatenate_code + '        dy=np.zeros(({0}), dtype="float")\n'.format(model.num_gene)

    for i in range(len(model.ParameterName)):
        concatenate_code= concatenate_code + '        {0}={1}\n'.format(model.ParameterName[i],model.ParameterValue[i])
#    for i in range(len(model.AllParameters)):
#        concatenate_code= concatenate_code + '        {0}\n'.format(model.AllParameters[i])
        #print('        {0}\n'.format(AllParameters[i]))

# updated with constants or functions
    for i in range(len(model.const)):
        #print('model.const:',model.const[i])
        concatenate_code= concatenate_code + '        {0}\n'.format(model.const[i])
        #self.ode_Eqn_Text.insert(tk.INSERT, model.const[i])
    concatenate_code= concatenate_code + '        \n'

    for i in range(len(model.rhsList)):
        concatenate_code= concatenate_code + '        dy[{0}]={1}\n'.format(i,model.rhsList[i])
        #print('        dy[{0}]={1}\n'.format(i,rhsList[i]))
    concatenate_code= concatenate_code + '        return dy\n'
    concatenate_code= concatenate_code + '    numPoints = (tend - t0)/h + 1\n'     
    concatenate_code= concatenate_code + '    time = linspace(t0, tend, numPoints)\n'

    concatenate_code= concatenate_code + '    yinit = user_init\n' #.format(eachInitCond)
    concatenate_code= concatenate_code + '    y = odeint(odefunc, yinit, time)\n'  
    concatenate_code= concatenate_code + '    return time, y\n'                                                        
    concatenate_code= concatenate_code + 'h={0}\n'.format(model.h)
    concatenate_code= concatenate_code + 't0={0}\n'.format(model.t_start)
    concatenate_code= concatenate_code + 'tend={0}\n'.format(model.t_end)
    concatenate_code= concatenate_code + 'global time1\n' 
    concatenate_code= concatenate_code + 'global result1\n' 
    concatenate_code= concatenate_code + 'time1, result1 = simulateModel(t0,tend, h)\n'  

    exec(concatenate_code)  

    
    return time1, result1    

def PhasePlaneInitConds_simulate_time_course(self,initConds):
    ''' simulate time course data with user input initial conditions'''
    print("initConds_simulate_time_course was called.")
    
    temp_random_init_d=model.y
    
    # to get random initial condition in a list
    temp_random_init_c=[]
    for i in range(temp_random_init_d.shape[1]):
        temp_random_init_c.append(temp_random_init_d[0][i])
    
    # to get user key in initial condition in an array    
    global user_init
    #user_init=np.asarray(temp_random_init_c)
    user_init=initConds

    concatenate_code=''
    concatenate_code= concatenate_code + 'def simulateModel(t0, tend, h):\n'
    concatenate_code= concatenate_code + '    def odefunc(Y,t):\n'

    for i in range(len(model.geneName)):
        concatenate_code= concatenate_code + '        {0} = Y[{1}]\n'.format(model.geneName[i],i)
        #print('        {0} = Y[{1}]\n'.format(VariableName[i],i))
    concatenate_code= concatenate_code + '        dy=np.zeros(({0}), dtype="float")\n'.format(model.num_gene)

    for i in range(len(model.ParameterName)):
        concatenate_code= concatenate_code + '        {0}={1}\n'.format(model.ParameterName[i],model.ParameterValue[i])
#    for i in range(len(model.AllParameters)):
#        concatenate_code= concatenate_code + '        {0}\n'.format(model.AllParameters[i])
        #print('        {0}\n'.format(AllParameters[i]))

# updated with constants or functions
    for i in range(len(model.const)):
        #print('model.const:',model.const[i])
        concatenate_code= concatenate_code + '        {0}\n'.format(model.const[i])
        #self.ode_Eqn_Text.insert(tk.INSERT, model.const[i])
    concatenate_code= concatenate_code + '        \n'

    for i in range(len(model.rhsList)):
        concatenate_code= concatenate_code + '        dy[{0}]={1}\n'.format(i,model.rhsList[i])
        #print('        dy[{0}]={1}\n'.format(i,rhsList[i]))
    concatenate_code= concatenate_code + '        return dy\n'
    concatenate_code= concatenate_code + '    numPoints = (tend - t0)/h + 1\n'     
    concatenate_code= concatenate_code + '    time = linspace(t0, tend, numPoints)\n'

    concatenate_code= concatenate_code + '    yinit = user_init\n' #.format(eachInitCond)
    concatenate_code= concatenate_code + '    y = odeint(odefunc, yinit, time)\n'  
    concatenate_code= concatenate_code + '    return time, y\n'                                                        
    concatenate_code= concatenate_code + 'h={0}\n'.format(model.h)
    concatenate_code= concatenate_code + 't0={0}\n'.format(model.t_start)
    concatenate_code= concatenate_code + 'tend={0}\n'.format(model.t_end)
    concatenate_code= concatenate_code + 'global time1\n' 
    concatenate_code= concatenate_code + 'global result1\n' 
    concatenate_code= concatenate_code + 'time1, result1 = simulateModel(t0,tend, h)\n'            
    exec(concatenate_code)  

    
    return time1, result1   

def simulate_time_course_for_PosProb(self,Traj_Num):
    #print("simulate_time_course_for_PosProb was called.")
    Traj_Number = Traj_Num 
    
    #print('eachInitCond:', model.InitialConditions[Traj_Number,:][:,None].T)
    temp_init_d=model.InitialConditions[Traj_Number,:][:,None].T
    
    # to get initial condition in a list
    temp_init_c=[]
    for i in range(temp_init_d.shape[1]):
        temp_init_c.append(temp_init_d[0][i])
    
    # to get initial condition in an array    
    global initCond
    initCond=np.asarray(temp_init_c)

    concatenate_code=''
    concatenate_code= concatenate_code + 'def simulateModel(t0, tend, h):\n'
    concatenate_code= concatenate_code + '    def odefunc(Y,t):\n'
#    concatenate_code= concatenate_code + '        x = Y[0]\n'
#    concatenate_code= concatenate_code + '        y = Y[1]\n'
    for i in range(len(model.geneName)):
        concatenate_code= concatenate_code + '        {0} = Y[{1}]\n'.format(model.geneName[i],i)
        #print('        {0} = Y[{1}]\n'.format(VariableName[i],i))
    concatenate_code= concatenate_code + '        dy=np.zeros(({0}), dtype="float")\n'.format(model.num_gene)
#    concatenate_code= concatenate_code + '        dy[0]=-1+9*x-2*x**3+9*y-2*y**3\n'
#    concatenate_code= concatenate_code + '        dy[1]=1-11*x+2*x**3+11*y-2*y**3\n'  
    for i in range(len(model.AllParameters)):
        concatenate_code= concatenate_code + '        {0}\n'.format(model.AllParameters[i])
        #print('        {0}\n'.format(AllParameters[i]))

# updated with constants or functions
    for i in range(len(model.const)):
        #print('model.const:',model.const[i])
        concatenate_code= concatenate_code + '        {0}\n'.format(model.const[i])
        #self.ode_Eqn_Text.insert(tk.INSERT, model.const[i])
    concatenate_code= concatenate_code + '        \n'        
        
    for i in range(len(model.rhsList)):
        concatenate_code= concatenate_code + '        dy[{0}]={1}\n'.format(i,model.rhsList[i])
        #print('        dy[{0}]={1}\n'.format(i,rhsList[i]))
    concatenate_code= concatenate_code + '        return dy\n'
    concatenate_code= concatenate_code + '    numPoints = (tend - t0)/h + 1\n'     
    concatenate_code= concatenate_code + '    time = linspace(t0, tend, numPoints)\n'
#    concatenate_code= concatenate_code + '    n = randint(0, model.TrajectoryNumber-1)\n'
    concatenate_code= concatenate_code + '    eachInitCond = initCond\n' #{0}\n'.format(d) #model.InitialConditions[n,:][:,None].T\n                                         
#    concatenate_code= concatenate_code + '    yinit = np.array([1.30535752, 0.44290278])\n' 
    concatenate_code= concatenate_code + '    yinit = eachInitCond\n' #.format(eachInitCond)
    concatenate_code= concatenate_code + '    y = odeint(odefunc, yinit, time)\n'  
    concatenate_code= concatenate_code + '    return y\n'                                                        
    # h = 0.1    
    #    yinit = np.array([0.10130762, 2.98803187])    
    
    #h=model.h
    #t0=model.t_start
    #tend=model.t_end
    #n, time1, result1 = simulateModel(t0,tend, h)
    concatenate_code= concatenate_code + 'h={0}\n'.format(model.h)
    concatenate_code= concatenate_code + 't0={0}\n'.format(model.t_start)
    concatenate_code= concatenate_code + 'tend={0}\n'.format(model.t_end)
    concatenate_code= concatenate_code + 'global time1\n' 
    concatenate_code= concatenate_code + 'global result2\n' 
    concatenate_code= concatenate_code + 'result2 = simulateModel(t0,tend, h)\n'            
    exec(concatenate_code)  
    #print('result2[-1,:]=',result2[-1,:])
    
    
    # store end points
    #print('result1[-1,:]=',result1[-1,:])
    #print('result1[-2,:]=',result1[-2,:])
    euclidean_dist = np.linalg.norm(result2[-1,:]-result2[-2,:])
    #print('euclidean_dist',euclidean_dist)  

    if euclidean_dist < 1e-3:       
        model.TempAttractors[Traj_Number,:]=np.round(result2[-1,:],1)
    
    return result2

def sbml_simulate_time_course(self):
    print('sbml_simulate_sbml_time_course was called.')
            
    # 
    global sbml_random_num_n
    sbml_random_num_n = randint(0, model.TrajectoryNumber-1) 
    
    print('eachInitCond:', model.InitialConditions[sbml_random_num_n,:][:,None].T)
    temp_random_init_d=model.InitialConditions[sbml_random_num_n,:][:,None].T
    
    # to get random initial condition in a list
    temp_random_init_c=[]
    for i in range(temp_random_init_d.shape[1]):
        temp_random_init_c.append(temp_random_init_d[0][i])
    
    # to get random initial condition in an array    
    global sbml_random_init
    sbml_random_init=np.asarray(temp_random_init_c)


    t0 = model.t_start
    tEnd = model.t_end
    numPoints = (tEnd - t0)/model.h +1
    time =linspace(t0,tEnd,numPoints)
    
    #print('model.doc.getNumSpecies():',model.doc.getNumSpecies())
    #
    # figure out which species are variable 
    #
    mod = doc.getModel()

    variables = {}
  
    for i in range(mod.getNumSpecies()): 
        species = mod.getSpecies(i)
        if species.getBoundaryCondition() == True or (species.getId() in variables): # variables.has_key(species.getId()): has_key only can be used in Python 2
            continue
        variables[species.getId()] = []
  
#    print('variables:',variables)
#    print('variables.keys:', variables.keys)

    
    # Ket use concatenated string to be run by exec
    concatenated_code_sbml=''
#    concatenated_code_sbml=concatenated_code_sbml + 'from numpy import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pylab import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pyplot import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from scipy.integrate import odeint \n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + 'def sbml_simulateModel(t0, tend, numPoints):\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #compartments\n'
    # write out compartment values
    for i in range(mod.getNumCompartments()):
        element = mod.getCompartment(i)
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getSize())
    # write out parameter values
    
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #global parameters\n'

#    The 3 lines of code below were replace by codes that use updated parameter values
#    for i in range(mod.getNumParameters()):
#        element = mod.getParameter(i)
#        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getValue())

    for i in range(len(model.ParameterName)):
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(model.ParameterName[i], model.ParameterValue[i])


    # write out boundary species 
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #boundary species\n'
#    for i in range(mod.getNumSpecies()):
#        element = mod.getSpecies(i)
        # Ket modified to True original if element.getBoundaryCondition() == False:
#        if element.getBoundaryCondition() == False: 
#            continue 
#        if element.isSetInitialConcentration(): 
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialConcentration())
#            print(element.getId())
            #print(element.getInitialConcenration())
#        else:
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialAmount()) 

# the above line of code is replace by the following constants from model.Constants
    for key in model.Constants:
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(key, model.Constants[key])

    # write derive function        
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  def ode_fun(__Y__, t):\n'
    # Ket modify code here for running in Python 3
    #variableList=list(variables.keys())
    #print('variableList:',variableList)
    # Now, variableList[i]= variables[variables.keys()[i] 
    #for i in range(len(variables.keys())):    
    for i in range(len(model.geneName)): 
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = __Y__[{1}]\n'.format(model.geneName[i], i)
        #concatenated_code_sbml=concatenated_code_sbml + '    {0} = __Y__[{1}]\n'.format(variableList[i], i)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    for i in range(mod.getNumReactions()): 
        reaction = mod.getReaction(i)
        kinetics = reaction.getKineticLaw()  
    
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = {1}\n'.format(reaction.getId(),  kinetics.getFormula())

        for j in range(reaction.getNumReactants()): 
            ref = reaction.getReactant(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('-{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('-({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
        for j in range(reaction.getNumProducts()): 
            ref = reaction.getProduct(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
                
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '    return array(['
    
    variableList=list(variables.keys())
    #print(len(variables.keys()))
    #print(variables.keys())
    for i in range(len(variables.keys())):
        for eqn in variables[variableList[i]]:  #         for eqn in variables[variables.keys()[i]]:
            #print(eqn)
            #print(variables[variableList[i]])
            concatenated_code_sbml=concatenated_code_sbml + ' + ({0})'.format(eqn)
        if i + 1 < len(variables.keys()) and len(variables[variableList[i]])!=0:
            concatenated_code_sbml=concatenated_code_sbml + ',\n      '
    concatenated_code_sbml=concatenated_code_sbml + '    ])\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    concatenated_code_sbml=concatenated_code_sbml + '  time = linspace(t0, tend, numPoints)\n'

    # get random initial conditions
    concatenated_code_sbml= concatenated_code_sbml + '  eachInitCond = sbml_random_init\n'
    concatenated_code_sbml= concatenated_code_sbml + '  yinit = eachInitCond\n'
  
    # write out initial concentrations   
#    concatenated_code_sbml=concatenated_code_sbml + '  yinit= array(['
#    count = 0
#    for key in variables.keys():
        # get initialValue 
#        element = mod.getElementBySId(key)
#        if element.getTypeCode() == SBML_PARAMETER: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getValue())
#        elif element.getTypeCode() == SBML_SPECIES: 
#            if element.isSetInitialConcentration(): 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialConcentration())
#            else: 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialAmount())
#        else: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getSize())
#        count += 1
#        if count < len(variables.keys()):
#            concatenated_code_sbml=concatenated_code_sbml + ', '
#    concatenated_code_sbml=concatenated_code_sbml + '])\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  y = odeint(ode_fun, yinit, time)\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  return sbml_random_num_n, time, y\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml= concatenated_code_sbml + 'global sbml_time1\n' 
    concatenated_code_sbml= concatenated_code_sbml + 'global sbml_result1\n' 
    
    concatenated_code_sbml=concatenated_code_sbml + 'sbml_random_num_n, sbml_time1, sbml_result1 = sbml_simulateModel({0}, {1}, {2})\n'.format(t0, tEnd, numPoints)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    # write out plotting code 
#    concatenated_code_sbml=concatenated_code_sbml + 'fig = figure()\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ax = subplot(111)\n'
  
#    for i in range(len(variables.keys())): 
#        concatenated_code_sbml=concatenated_code_sbml + 'plot(time,result[:,{0}], label="{1}", lw=1.5)\n'.format(i, variableList[i])  # format(i, variables.keys()[i]))
    
#    concatenated_code_sbml=concatenated_code_sbml + 'box = ax.get_position()\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ax.set_position([box.x0, box.y0, box.width * 0.7, box.height])\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'xlabel("time")\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ylabel("concentration")\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'legend(loc="center left", bbox_to_anchor=(1, 0.5))\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'show()\n'
    print(concatenated_code_sbml)
    exec(concatenated_code_sbml)
    # convert generated code to string 
    # result = str(generated_code);
    #return concatenated_code_sbml   
    print('sbml_result1[-1,:]=',sbml_result1[-1,:])
    model.DataOutputT=sbml_result1
    
    return sbml_random_num_n, sbml_time1, sbml_result1


def initConds_sbml_simulate_time_course(self):
    print('initConds_sbml_simulate_time_course was called.')
            
    # 
    #global sbml_random_num_n
    #sbml_random_num_n = randint(0, model.TrajectoryNumber-1) 
    
    #print('eachInitCond:', model.InitialConditions[sbml_random_num_n,:][:,None].T)
    #temp_random_init_d=model.InitialConditions[sbml_random_num_n,:][:,None].T
    temp_random_init_d=model.y
    
    # to get random initial condition in a list
    temp_random_init_c=[]
    for i in range(temp_random_init_d.shape[1]):
        temp_random_init_c.append(temp_random_init_d[0][i])
    
    # to get random initial condition in an array    
    global sbml_random_init
    sbml_random_init=np.asarray(temp_random_init_c)


    t0 = model.t_start
    tEnd = model.t_end
    numPoints = (tEnd - t0)/model.h +1
    time =linspace(t0,tEnd,numPoints)
    
    #print('model.doc.getNumSpecies():',model.doc.getNumSpecies())
    #
    # figure out which species are variable 
    #
    mod = doc.getModel()
    variables = {}
  
    for i in range(mod.getNumSpecies()): 
        species = mod.getSpecies(i)
        if species.getBoundaryCondition() == True or (species.getId() in variables): # variables.has_key(species.getId()): has_key only can be used in Python 2
            continue
        variables[species.getId()] = []
  
    #print('variables:',variables)
    #print('variables.keys:', variables.keys)

    
    # Ket use concatenated string to be run by exec
    concatenated_code_sbml=''
#    concatenated_code_sbml=concatenated_code_sbml + 'from numpy import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pylab import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pyplot import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from scipy.integrate import odeint \n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + 'def sbml_simulateModel(t0, tend, numPoints):\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #compartments\n'
    # write out compartment values
    for i in range(mod.getNumCompartments()):
        element = mod.getCompartment(i)
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getSize())
    # write out parameter values
    
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #global parameters\n'

    for i in range(len(model.ParameterName)):
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(model.ParameterName[i], model.ParameterValue[i])
        
#    for i in range(mod.getNumParameters()):
#        element = mod.getParameter(i)
#        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getValue())

    # write out boundary species 
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #boundary species\n'
#    for i in range(mod.getNumSpecies()):
#        element = mod.getSpecies(i)
#        if element.getBoundaryCondition() == False: 
#            continue 
#        if element.isSetInitialConcentration():           
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialConcentration())
#        else:
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialAmount()) 
# the above line of code is replace by the following constants from model.Constants
    for key in model.Constants:
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(key, model.Constants[key])

    # write derive function        
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  def ode_fun(__Y__, t):\n'
    # Ket modify code here for running in Python 3
    variableList=list(variables.keys())
    # Now, variableList[i]= variables[variables.keys()[i] 
    for i in range(len(model.geneName)): 
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = __Y__[{1}]\n'.format(model.geneName[i], i)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    for i in range(mod.getNumReactions()): 
        reaction = mod.getReaction(i)
        kinetics = reaction.getKineticLaw()  
    
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = {1}\n'.format(reaction.getId(),  kinetics.getFormula())

        for j in range(reaction.getNumReactants()): 
            ref = reaction.getReactant(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('-{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('-({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
        for j in range(reaction.getNumProducts()): 
            ref = reaction.getProduct(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
                
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '    return array(['
    
    variableList=list(variables.keys())
    #print(len(variables.keys()))
    #print(variables.keys())
    for i in range(len(variables.keys())):
        for eqn in variables[variableList[i]]:  #         for eqn in variables[variables.keys()[i]]:
            #print(eqn)
            #print(variables[variableList[i]])
            concatenated_code_sbml=concatenated_code_sbml + ' + ({0})'.format(eqn)
        if i + 1 < len(variables.keys()) and len(variables[variableList[i]])!=0:
            concatenated_code_sbml=concatenated_code_sbml + ',\n      '
    concatenated_code_sbml=concatenated_code_sbml + '    ])\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    concatenated_code_sbml=concatenated_code_sbml + '  time = linspace(t0, tend, numPoints)\n'

    # get random initial conditions
    concatenated_code_sbml= concatenated_code_sbml + '  eachInitCond = sbml_random_init\n'
    concatenated_code_sbml= concatenated_code_sbml + '  yinit = eachInitCond\n'
  
    # write out initial concentrations   
#    concatenated_code_sbml=concatenated_code_sbml + '  yinit= array(['
#    count = 0
#    for key in variables.keys():
        # get initialValue 
#        element = mod.getElementBySId(key)
#        if element.getTypeCode() == SBML_PARAMETER: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getValue())
#        elif element.getTypeCode() == SBML_SPECIES: 
#            if element.isSetInitialConcentration(): 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialConcentration())
#            else: 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialAmount())
#        else: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getSize())
#        count += 1
#        if count < len(variables.keys()):
#            concatenated_code_sbml=concatenated_code_sbml + ', '
#    concatenated_code_sbml=concatenated_code_sbml + '])\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  y = odeint(ode_fun, yinit, time)\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  return time, y\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml= concatenated_code_sbml + 'global sbml_time1\n' 
    concatenated_code_sbml= concatenated_code_sbml + 'global sbml_result1\n' 
    
    concatenated_code_sbml=concatenated_code_sbml + 'sbml_time1, sbml_result1 = sbml_simulateModel({0}, {1}, {2})\n'.format(t0, tEnd, numPoints)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    # write out plotting code 
#    concatenated_code_sbml=concatenated_code_sbml + 'fig = figure()\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ax = subplot(111)\n'
  
#    for i in range(len(variables.keys())): 
#        concatenated_code_sbml=concatenated_code_sbml + 'plot(time,result[:,{0}], label="{1}", lw=1.5)\n'.format(i, variableList[i])  # format(i, variables.keys()[i]))
    
#    concatenated_code_sbml=concatenated_code_sbml + 'box = ax.get_position()\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ax.set_position([box.x0, box.y0, box.width * 0.7, box.height])\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'xlabel("time")\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ylabel("concentration")\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'legend(loc="center left", bbox_to_anchor=(1, 0.5))\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'show()\n'


    print(concatenated_code_sbml)

    exec(concatenated_code_sbml)
    # convert generated code to string 
    # result = str(generated_code);
    #return concatenated_code_sbml   
    print('sbml_result1[-1,:]=',sbml_result1[-1,:])
    model.initDataOutputT=sbml_result1
    
    return sbml_time1, sbml_result1

def PhasePlaneInitConds_sbml_simulate_time_course(self,initConds):
    print('initConds_sbml_simulate_time_course was called.')
            
    # 
    #global sbml_random_num_n
    #sbml_random_num_n = randint(0, model.TrajectoryNumber-1) 
    
    #print('eachInitCond:', model.InitialConditions[sbml_random_num_n,:][:,None].T)
    #temp_random_init_d=model.InitialConditions[sbml_random_num_n,:][:,None].T
    temp_random_init_d=model.y
    
    # to get random initial condition in a list
    temp_random_init_c=[]
    for i in range(temp_random_init_d.shape[1]):
        temp_random_init_c.append(temp_random_init_d[0][i])
    
    # to get random initial condition in an array    
    global sbml_random_init
    #sbml_random_init=np.asarray(temp_random_init_c)
    sbml_random_init=initConds

    t0 = model.t_start
    tEnd = model.t_end
    numPoints = (tEnd - t0)/model.h +1
    time =linspace(t0,tEnd,numPoints)
    
    #print('model.doc.getNumSpecies():',model.doc.getNumSpecies())
    #
    # figure out which species are variable 
    #
    mod = doc.getModel()
    variables = {}
  
    for i in range(mod.getNumSpecies()): 
        species = mod.getSpecies(i)
        if species.getBoundaryCondition() == True or (species.getId() in variables): # variables.has_key(species.getId()): has_key only can be used in Python 2
            continue
        variables[species.getId()] = []
  
    #print('variables:',variables)
    #print('variables.keys:', variables.keys)

    
    # Ket use concatenated string to be run by exec
    concatenated_code_sbml=''
#    concatenated_code_sbml=concatenated_code_sbml + 'from numpy import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pylab import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pyplot import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from scipy.integrate import odeint \n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + 'def sbml_simulateModel(t0, tend, numPoints):\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #compartments\n'
    # write out compartment values
    for i in range(mod.getNumCompartments()):
        element = mod.getCompartment(i)
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getSize())
    # write out parameter values
    
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #global parameters\n'

    for i in range(len(model.ParameterName)):
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(model.ParameterName[i], model.ParameterValue[i])
        
#    for i in range(mod.getNumParameters()):
#        element = mod.getParameter(i)
#        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getValue())

    # write out boundary species 
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #boundary species\n'
#    for i in range(mod.getNumSpecies()):
#        element = mod.getSpecies(i)
#        # Ket modified to True originial is element.getBoundaryCondition() == False: 
#        if element.getBoundaryCondition() == False: 
#            continue 
#        if element.isSetInitialConcentration(): 
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialConcentration())
#        else:
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialAmount()) 
# the above line of code is replace by the following constants from model.Constants
    for key in model.Constants:
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(key, model.Constants[key])


    # write derive function        
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  def ode_fun(__Y__, t):\n'
    # Ket modify code here for running in Python 3
    variableList=list(variables.keys())
    # Now, variableList[i]= variables[variables.keys()[i] 
    for i in range(len(model.geneName)): 
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = __Y__[{1}]\n'.format(model.geneName[i], i)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    for i in range(mod.getNumReactions()): 
        reaction = mod.getReaction(i)
        kinetics = reaction.getKineticLaw()  
    
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = {1}\n'.format(reaction.getId(),  kinetics.getFormula())

        for j in range(reaction.getNumReactants()): 
            ref = reaction.getReactant(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('-{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('-({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
        for j in range(reaction.getNumProducts()): 
            ref = reaction.getProduct(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
                
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '    return array(['
    
    variableList=list(variables.keys())
    #print(len(variables.keys()))
    #print(variables.keys())
    for i in range(len(variables.keys())):
        for eqn in variables[variableList[i]]:  #         for eqn in variables[variables.keys()[i]]:
            #print(eqn)
            #print(variables[variableList[i]])
            concatenated_code_sbml=concatenated_code_sbml + ' + ({0})'.format(eqn)
        if i + 1 < len(variables.keys()) and len(variables[variableList[i]])!=0:
            concatenated_code_sbml=concatenated_code_sbml + ',\n      '
    concatenated_code_sbml=concatenated_code_sbml + '    ])\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    concatenated_code_sbml=concatenated_code_sbml + '  time = linspace(t0, tend, numPoints)\n'

    # get random initial conditions
    concatenated_code_sbml= concatenated_code_sbml + '  eachInitCond = sbml_random_init\n'
    concatenated_code_sbml= concatenated_code_sbml + '  yinit = eachInitCond\n'
  
    # write out initial concentrations   
#    concatenated_code_sbml=concatenated_code_sbml + '  yinit= array(['
#    count = 0
#    for key in variables.keys():
        # get initialValue 
#        element = mod.getElementBySId(key)
#        if element.getTypeCode() == SBML_PARAMETER: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getValue())
#        elif element.getTypeCode() == SBML_SPECIES: 
#            if element.isSetInitialConcentration(): 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialConcentration())
#            else: 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialAmount())
#        else: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getSize())
#        count += 1
#        if count < len(variables.keys()):
#            concatenated_code_sbml=concatenated_code_sbml + ', '
#    concatenated_code_sbml=concatenated_code_sbml + '])\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  y = odeint(ode_fun, yinit, time)\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  return time, y\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml= concatenated_code_sbml + 'global sbml_time1\n' 
    concatenated_code_sbml= concatenated_code_sbml + 'global sbml_result1\n' 
    
    concatenated_code_sbml=concatenated_code_sbml + 'sbml_time1, sbml_result1 = sbml_simulateModel({0}, {1}, {2})\n'.format(t0, tEnd, numPoints)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    # write out plotting code 
#    concatenated_code_sbml=concatenated_code_sbml + 'fig = figure()\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ax = subplot(111)\n'
  
#    for i in range(len(variables.keys())): 
#        concatenated_code_sbml=concatenated_code_sbml + 'plot(time,result[:,{0}], label="{1}", lw=1.5)\n'.format(i, variableList[i])  # format(i, variables.keys()[i]))
    
#    concatenated_code_sbml=concatenated_code_sbml + 'box = ax.get_position()\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ax.set_position([box.x0, box.y0, box.width * 0.7, box.height])\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'xlabel("time")\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'ylabel("concentration")\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'legend(loc="center left", bbox_to_anchor=(1, 0.5))\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'show()\n'

    exec(concatenated_code_sbml)
    # convert generated code to string 
    # result = str(generated_code);
    #return concatenated_code_sbml   
    print('sbml_result1[-1,:]=',sbml_result1[-1,:])
    model.initDataOutputT=sbml_result1
    
    return sbml_time1, sbml_result1


def sbml_simulate_time_course_for_PosProb(self,Traj_Num):
    #print('simulate_sbml_time_course_for_PosProb was called.')
    Traj_Number = Traj_Num 
    
    #print('eachInitCond:', model.InitialConditions[Traj_Number,:][:,None].T)
    temp_init_d=model.InitialConditions[Traj_Number,:][:,None].T
    
    # to get initial condition in a list
    temp_init_c=[]
    for i in range(temp_init_d.shape[1]):
        temp_init_c.append(temp_init_d[0][i])
    
    # to get initial condition in an array    
    global sbml_initCond
    sbml_initCond=np.asarray(temp_init_c)            


    t0 = model.t_start
    tEnd = model.t_end
    numPoints = (tEnd - t0)/model.h +1
    time =linspace(t0,tEnd,numPoints)
    
    #
    # figure out which species are variable 
    #
    mod = doc.getModel()
    variables = {}
  
    for i in range(mod.getNumSpecies()): 
        species = mod.getSpecies(i)
        if species.getBoundaryCondition() == True or (species.getId() in variables): # variables.has_key(species.getId()): has_key only can be used in Python 2
            continue
        variables[species.getId()] = []
  
    #print('variables:',variables)
    #print('variables.keys:', variables.keys)

    
    # Ket use concatenated string to be run by exec
    concatenated_code_sbml=''
#    concatenated_code_sbml=concatenated_code_sbml + 'from numpy import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pylab import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from matplotlib.pyplot import *\n'
#    concatenated_code_sbml=concatenated_code_sbml + 'from scipy.integrate import odeint \n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + 'def sbml_simulateModel(t0, tend, numPoints):\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #compartments\n'
    # write out compartment values
    for i in range(mod.getNumCompartments()):
        element = mod.getCompartment(i)
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getSize())
    # write out parameter values
    
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #global parameters\n'
#    The 3 lines of code below were replace by codes that use updated parameter values
#    for i in range(mod.getNumParameters()):
#        element = mod.getParameter(i)
#        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getValue())
    for i in range(len(model.ParameterName)):
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(model.ParameterName[i], model.ParameterValue[i])


    # write out boundary species 
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  #boundary species\n'
#    for i in range(mod.getNumSpecies()):
#        element = mod.getSpecies(i)
        # Ket modified to True original is element.getBoundaryCondition() == False: 
#        if element.getBoundaryCondition() == False: 
#            continue 
#        if element.isSetInitialConcentration(): 
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialConcentration())
#        else:
#            concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(element.getId(), element.getInitialAmount()) 
# the above line of code is replace by the following constants from model.Constants
    for key in model.Constants:
        concatenated_code_sbml=concatenated_code_sbml + '  {0} = {1}\n'.format(key, model.Constants[key])


    # write derive function        
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
    concatenated_code_sbml=concatenated_code_sbml + '  def ode_fun(__Y__, t):\n'
    # Ket modify code here for running in Python 3
    variableList=list(variables.keys())
    # Now, variableList[i]= variables[variables.keys()[i] 
    for i in range(len(model.geneName)): 
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = __Y__[{1}]\n'.format(model.geneName[i], i)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    for i in range(mod.getNumReactions()): 
        reaction = mod.getReaction(i)
        kinetics = reaction.getKineticLaw()  
    
        concatenated_code_sbml=concatenated_code_sbml + '    {0} = {1}\n'.format(reaction.getId(),  kinetics.getFormula())

        for j in range(reaction.getNumReactants()): 
            ref = reaction.getReactant(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('-{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('-({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
        for j in range(reaction.getNumProducts()): 
            ref = reaction.getProduct(j)
            species = mod.getSpecies(ref.getSpecies())
            if species.getBoundaryCondition() == True: 
                continue
            if ref.getStoichiometry() == 1.0: 
                variables[species.getId()].append('{0}'.format(reaction.getId()))
            else:
                variables[species.getId()].append('({0})*{1}'.format(ref.getStoichiometry(), reaction.getId()))
                
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '    return array(['
    
    variableList=list(variables.keys())
    #print(len(variables.keys()))
    #print(variables.keys())
    for i in range(len(variables.keys())):
        for eqn in variables[variableList[i]]:  #         for eqn in variables[variables.keys()[i]]:
            #print(eqn)
            #print(variables[variableList[i]])
            concatenated_code_sbml=concatenated_code_sbml + ' + ({0})'.format(eqn)
        if i + 1 < len(variables.keys()) and len(variables[variableList[i]]) != 0:
            concatenated_code_sbml=concatenated_code_sbml + ',\n      '
    concatenated_code_sbml=concatenated_code_sbml + '    ])\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    concatenated_code_sbml=concatenated_code_sbml + '  time = linspace(t0, tend, numPoints)\n'

    # get random initial conditions
    concatenated_code_sbml= concatenated_code_sbml + '  eachInitCond = sbml_initCond\n'
    concatenated_code_sbml= concatenated_code_sbml + '  yinit = eachInitCond\n'
  
    # write out initial concentrations   
#    concatenated_code_sbml=concatenated_code_sbml + '  yinit= array(['
#    count = 0
#    for key in variables.keys():
        # get initialValue 
#        element = mod.getElementBySId(key)
#        if element.getTypeCode() == SBML_PARAMETER: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getValue())
#        elif element.getTypeCode() == SBML_SPECIES: 
#            if element.isSetInitialConcentration(): 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialConcentration())
#            else: 
#                concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getInitialAmount())
#        else: 
#            concatenated_code_sbml=concatenated_code_sbml + '{0}'.format(element.getSize())
#        count += 1
#        if count < len(variables.keys()):
#            concatenated_code_sbml=concatenated_code_sbml + ', '
#    concatenated_code_sbml=concatenated_code_sbml + '])\n'
    concatenated_code_sbml=concatenated_code_sbml + '  \n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  y = odeint(ode_fun, yinit, time)\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
  
    concatenated_code_sbml=concatenated_code_sbml + '  return y\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    concatenated_code_sbml= concatenated_code_sbml + 'global sbml_result2\n' 
    
    concatenated_code_sbml=concatenated_code_sbml + 'sbml_result2 = sbml_simulateModel({0}, {1}, {2})\n'.format(t0, tEnd, numPoints)
    concatenated_code_sbml=concatenated_code_sbml + '\n'
    
    exec(concatenated_code_sbml)
    # convert generated code to string 
    # result = str(generated_code);
    #return concatenated_code_sbml   
    #print('sbml_result2[-1,:]=',sbml_result2[-1,:])
    
    # store end points
    #print('result1[-1,:]=',result1[-1,:])
    #print('result1[-2,:]=',result1[-2,:])
    euclidean_dist = np.linalg.norm(sbml_result2[-1,:]-sbml_result2[-2,:])
    #print('euclidean_dist',euclidean_dist)  

    if euclidean_dist < 1e-3:       
        model.TempAttractors[Traj_Number,:]=np.round(sbml_result2[-1,:],1)
    
    return sbml_result2

def plot_time_course(self):
    '''Plot time course '''
    print("plot_time_course was called")
    
    #self.status_bar_label.config(text="plot_time_course was called.")
    #print('model.name:',model.name)
    #print(dir())
    
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    if model.type == 'ode':
        
        #n, self.outputT=model.calculate_timeCourse() 
        n, time, self.outputT = simulate_time_course(self)
        a2 = f2.add_subplot(111)
        # for Data Viewer
        global DataOutputT
        #print(time1.shape)
        #print(result1.shape)
        time1_row_column = np.array([time])
        time1_r_c_T =time1_row_column.T
        #print(time1_row_column.shape)
        DataOutputT=np.concatenate((time1_r_c_T,self.outputT), axis=1)
        model.DataOutputT=DataOutputT
        #DataOutputT = self.outputT
        
    
        #for i in range(2):
        #    print(i)
        #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
        #    print(eachInitCond)
        #    self.y=eachInitCond
        
        # Get one trajectory time-course data
        #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
        #    print(output)        
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_1+1], color= 'g', linewidth=0.5) #, hold=True)
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_2+1], color= 'b', linewidth=0.5) # , hold=True)
        a2.plot(time, self.outputT[:,model.index_1], color= 'g', linewidth=0.5) #, hold=True)
        a2.plot(time, self.outputT[:,model.index_2], color= 'b', linewidth=0.5) # , hold=True)

        a2.set_xlabel('time')
        a2.set_ylabel('protein levels')
        #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
        #print('model.index_2', model.index_2)
        a2.legend([str(model.geneName[model.index_1]),str(model.geneName[model.index_2])], loc=1) 
        # legend option loc =1 means place the location of the legend in the upper right
        # refers to this url for other options
        # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
    
        #a2.title('n')
        print('n=', n)

        f2.canvas.draw_idle()   
    
    if model.type == 'SBML':
        n, time, self.outputT = sbml_simulate_time_course(self)    
        a2 = f2.add_subplot(111)
        # for Data Viewer
        global sbml_DataOutputT
        #print(time1.shape)
        #print(result1.shape)
        time1_row_column = np.array([time])
        time1_r_c_T =time1_row_column.T
        #print(time1_row_column.shape)
        sbml_DataOutputT=np.concatenate((time1_r_c_T,self.outputT), axis=1)
        model.DataOutputT=sbml_DataOutputT
        #DataOutputT = self.outputT
        
    
        #for i in range(2):
        #    print(i)
        #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
        #    print(eachInitCond)
        #    self.y=eachInitCond
        
        # Get one trajectory time-course data
        #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
        #    print(output)        
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_1+1], color= 'g', linewidth=0.5) #, hold=True)
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_2+1], color= 'b', linewidth=0.5) # , hold=True)
        a2.plot(time, self.outputT[:,model.index_1], color= 'g', linewidth=0.5) #, hold=True)
        a2.plot(time, self.outputT[:,model.index_2], color= 'b', linewidth=0.5) # , hold=True)

        a2.set_xlabel('time')
        a2.set_ylabel('protein levels')
        #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
        #print('model.index_2', model.index_2)
        a2.legend([str(model.geneName[model.index_1]),str(model.geneName[model.index_2])], loc=1) 
        # legend option loc =1 means place the location of the legend in the upper right
        # refers to this url for other options
        # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
    
        #a2.title('n')
        print('n=', n)

        f2.canvas.draw_idle()        

# plot time course with user key in initial Conditions
def initConds_plot_time_course(self):
    '''Plot time course with user key in initial Conditions'''
    print("initConds_plot_time_course was called")
    print(model.type)
    
    #self.status_bar_label.config(text="plot_time_course was called.")
    #print('model.name:',model.name)
    #print(dir())
    
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    if model.type == 'ode':
        
        #n, self.outputT=model.calculate_timeCourse() 
        time, self.initOutputT = initConds_simulate_time_course(self)
        f10.clear()
        a10 = f10.add_subplot(111)

        # for Data Viewer
        global initDataOutputT
        #print(time1.shape)
        #print(result1.shape)
        time1_row_column = np.array([time])
        time1_r_c_T =time1_row_column.T
        #print(time1_row_column.shape)
        initDataOutputT=np.concatenate((time1_r_c_T,self.initOutputT), axis=1)
        model.initDataOutputT=initDataOutputT
        #DataOutputT = self.outputT
        
        a10.plot(time, self.initOutputT[:,model.index_1], color= 'g', linewidth=0.5) #, hold=True)
        a10.plot(time, self.initOutputT[:,model.index_2], color= 'b', linewidth=0.5) # , hold=True)

        a10.set_xlabel('time')
        a10.set_ylabel('protein levels')
        #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
        #print('model.index_2', model.index_2)
        a10.legend([str(model.geneName[model.index_1]),str(model.geneName[model.index_2])], loc=1) 
        # legend option loc =1 means place the location of the legend in the upper right
        # refers to this url for other options
        # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
    
        #a2.title('n')

        f10.canvas.draw_idle()           

    # For SBML model
    if model.type == 'SBML':
        time, self.initOutputT = initConds_sbml_simulate_time_course(self) 
        f10.clear()
        a10 = f10.add_subplot(111)
        # for Data Viewer
        global sbml_DataOutputT
        #print(time1.shape)
        #print(result1.shape)
        time1_row_column = np.array([time])
        time1_r_c_T =time1_row_column.T
        #print(time1_row_column.shape)
        sbml_DataOutputT=np.concatenate((time1_r_c_T,self.initOutputT), axis=1)
        model.initDataOutputT=sbml_DataOutputT
        #DataOutputT = self.outputT
            
        
        #for i in range(2):
        #    print(i)
        #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
        #    print(eachInitCond)
        #    self.y=eachInitCond
            
        # Get one trajectory time-course data
        #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
        #    print(output)        
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_1+1], color= 'g', linewidth=0.5) #, hold=True)
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_2+1], color= 'b', linewidth=0.5) # , hold=True)
        a10.plot(time, self.initOutputT[:,model.index_1], color= 'g', linewidth=0.5) #, hold=True)
        a10.plot(time, self.initOutputT[:,model.index_2], color= 'b', linewidth=0.5) # , hold=True)
    
        a10.set_xlabel('time')
        a10.set_ylabel('protein levels')
        #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
        #print('model.index_2', model.index_2)
        a10.legend([str(model.geneName[model.index_1]),str(model.geneName[model.index_2])], loc=1) 
        # legend option loc =1 means place the location of the legend in the upper right
        # refers to this url for other options
        # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
    
        f10.canvas.draw_idle()      
        
        
        

def initConds_Checked_plot_time_course(self):
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    if model.type == 'ode':
        
        #n, self.outputT=model.calculate_timeCourse() 
        time, self.initOutputT = initConds_simulate_time_course(self)
        # for Data Viewer
        global initDataOutputT
        #print(time1.shape)
        #print(result1.shape)
        time1_row_column = np.array([time])
        time1_r_c_T =time1_row_column.T
        #print(time1_row_column.shape)
        initDataOutputT=np.concatenate((time1_r_c_T,self.initOutputT), axis=1)
        model.initDataOutputT=initDataOutputT
        #DataOutputT = self.outputT
        
        a7.plot(time, self.initOutputT[:,3], color= 'g', linewidth=0.5) #, hold=True)        
        
# plot time course with user key in parameter values
def Parameter_plot_time_course(self):
    '''Plot time course with user key in parameter values'''
    print("Parameter_plot_time_course was called")
    print(model.type)
    
    #self.status_bar_label.config(text="plot_time_course was called.")
    #print('model.name:',model.name)
    #print(dir())
    
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    if model.type == 'ode':
        
        #n, self.outputT=model.calculate_timeCourse() 
        time, self.initOutputT = initConds_simulate_time_course(self)
        f8.clear()
        a8 = f8.add_subplot(111)

        # for Data Viewer
        global initDataOutputT

        time1_row_column = np.array([time])
        time1_r_c_T =time1_row_column.T

        initDataOutputT=np.concatenate((time1_r_c_T,self.initOutputT), axis=1)
        model.initDataOutputT=initDataOutputT
        
        a8.plot(time, self.initOutputT[:,model.index_1], color= 'g', linewidth=0.5) #, hold=True)
        a8.plot(time, self.initOutputT[:,model.index_2], color= 'b', linewidth=0.5) # , hold=True)

        a8.set_xlabel('time')
        a8.set_ylabel('protein levels')

        a8.legend([str(model.geneName[model.index_1]),str(model.geneName[model.index_2])], loc=1)    

        f8.canvas.draw_idle()           

    # For SBML model
    if model.type == 'SBML':
        time, self.initOutputT = initConds_sbml_simulate_time_course(self) 
        f8.clear()
        a8 = f8.add_subplot(111)
        # for Data Viewer
        global sbml_DataOutputT
        #print(time1.shape)
        #print(result1.shape)
        time1_row_column = np.array([time])
        time1_r_c_T =time1_row_column.T
        #print(time1_row_column.shape)
        sbml_DataOutputT=np.concatenate((time1_r_c_T,self.initOutputT), axis=1)
        model.initDataOutputT=sbml_DataOutputT
        #DataOutputT = self.outputT
            
        
        #for i in range(2):
        #    print(i)
        #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
        #    print(eachInitCond)
        #    self.y=eachInitCond
            
        # Get one trajectory time-course data
        #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
        #    print(output)        
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_1+1], color= 'g', linewidth=0.5) #, hold=True)
        #a2.plot(self.outputT[:,0], self.outputT[:,model.index_2+1], color= 'b', linewidth=0.5) # , hold=True)
        a8.plot(time, self.initOutputT[:,model.index_1], color= 'g', linewidth=0.5) #, hold=True)
        a8.plot(time, self.initOutputT[:,model.index_2], color= 'b', linewidth=0.5) # , hold=True)
    
        a8.set_xlabel('time')
        a8.set_ylabel('protein levels')
        #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
        #print('model.index_2', model.index_2)
        a8.legend([str(model.geneName[model.index_1]),str(model.geneName[model.index_2])], loc=1) 
        # legend option loc =1 means place the location of the legend in the upper right
        # refers to this url for other options
        # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
    
        f8.canvas.draw_idle()        


# create a new window for viewing data
def new_window(self):
    print("new_window was called.")
    #print('DataOutputT:',DataOutputT)
    
#if model.name=='':
#        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")    
    self.newWindow = tk.Tk()
    self.app2 = DataViewer(self.newWindow)
    
# create a new window for changing model setting
def new_window_model_setting(self):
    print("new_window was called.")
    self.newWindow3 = tk.Tk()
    self.app3 = ModelSetting(self.newWindow3)

def Get_table_values(self):
    print('Get_table_values was called')
    #DataTable=self.setting_tableView()
    # COLUMNS = ['time', 'P53','Mdm2','Oct4','miR145','Zeb','miR200']
    COLUMNS = ['time2', model.geneName]
    print(COLUMNS)
    # setting column header for the table
    #for column in COLUMNS:
    #    DataTable.heading(column, text=column)
        
    # add data into table
    #for i in range(10):
    #    table.insert('', 'end', values= 

def save_data_to_csv(self):
    if model.type == 'ode':
        np.savetxt("TimeCourseData"+odeLoad_modelName+strftime("%Y-%m-%d %H %M %S", gmtime())+".csv", DataOutputT, delimiter=",", fmt='%10.5f')
        #np.savetxt("foo.csv", DataOutputT_with_heading, delimiter=",")   
        tk.messagebox.showinfo("Save data into csv file","Time course data have been saved into the file named TimeCourseData + model_name + current time.csv.")

    if model.type == 'SBML':
        np.savetxt("TimeCourseData"+sbml_Loaded_modelName+strftime("%Y-%m-%d %H %M %S", gmtime())+".csv", sbml_DataOutputT, delimiter=",", fmt='%10.5f')
        #np.savetxt("foo.csv", DataOutputT_with_heading, delimiter=",")   
        tk.messagebox.showinfo("Save data into csv file","Time course data have been saved into the file named TimeCourseData + model_name + current time.csv.")
     


def plot_phase_plane_graph(self):
    print("plot_phase_plane_graph was called") 
    
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    if model.type == 'ode':
        n, time, self.outputT = simulate_time_course(self)  
        a3 = f3.add_subplot(111)
        line=a3.plot(self.outputT[:,model.index_1], self.outputT[:,model.index_2], color= 'g', linewidth=0.5)[0] #, hold=True)
        a3.set_xlabel(str(model.geneName[model.index_1]))   
        a3.set_ylabel(str(model.geneName[model.index_2]))
        #print('model.index_2', model.index_2)
        #print('model.geneName[model.index_2]:',model.geneName[model.index_2])
        #a3.set_xlabel('protein 1')
        #a3.set_ylabel('protein 2')

        # add an arrow to the line graph
        add_arrow(line)
        f3.canvas.draw_idle()        
        
        #status_bar_label.config(text="Start with loading an ode model.") 
        #a5 = f5.text(0.5, 0.5,"")   
#        a5 = f5.text(0.5, 0.5, "end point:"+str(self.outputT[-1,model.index_1+1])+str(self.outputT[-1,model.index_2+1]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
#        f5.canvas.draw_idle()
        
    if model.type == 'SBML':
           
        #n, self.outputT=model.calculate_timeCourse() 
        n, time, self.outputT = sbml_simulate_time_course(self)
        
        a3 = f3.add_subplot(111)
    
        #for i in range(2):
        #    print(i)
        #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
        #    print(eachInitCond)
        #    self.y=eachInitCond
        
        # Get one trajectory time-course data
        #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
        #    print(output)        
        #a3.plot(self.outputT[:,1], self.outputT[:,5], color= 'g', linewidth=0.5) #, hold=True)
        #a3.plot(self.outputT[:,model.index_1+1], self.outputT[:,model.index_2+1], color= 'g', linewidth=0.5) #, hold=True)
        line=a3.plot(self.outputT[:,model.index_1], self.outputT[:,model.index_2], color= 'g', linewidth=0.5)[0] #, hold=True)
        # 
        a3.set_ylabel(str(model.geneName[model.index_1]))
        a3.set_xlabel(str(model.geneName[model.index_2]))   

        print('model.index_2', model.index_2)
        print('model.geneName[model.index_2]:',model.geneName[model.index_2])
        #a3.set_xlabel('protein 1')
        #a3.set_ylabel('protein 2')
        
        # add an arrow to the line graph
        add_arrow(line)        

        f3.canvas.draw_idle()        
        
        #status_bar_label.config(text="Start with loading an ode model.") 
#        a5 = f5.text(0.5, 0.5,"")   
#        a5 = f5.text(0.5, 0.5, "end point:"+str(self.outputT[-1,model.index_1+1])+str(self.outputT[-1,model.index_2+1]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
#        f5.canvas.draw_idle()


def plot_phase_plane2_graph(self):
    '''This function plot the phase plane with a few initial conditions'''
    print("plot_phase_plane2_graph was called") 
    
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    if model.type == 'ode':
        
        initialConds=[]
        xc=np.linspace(model.min_value, model.max_value, 6)
        yc=np.linspace(model.min_value, model.max_value, 6)
        
        for i in range(len(xc)):
            i
            for j in range(len(yc)):
                j
                if model.num_gene==2:
                    initialConds.append([xc[i], yc[j]])
                else:
                    initCond=[]
                    for k in range(model.num_gene-2):
                        initCond.append(np.random.random()*(model.max_value-model.min_value))
                    Init_prep=[]
                    Init_prep.append(xc[i])
                    Init_prep.append(yc[j])
                    
                    for p in initCond:
                        Init_prep.append(p)
                    #print('Init_prep:',Init_prep)
                    initialConds.append(Init_prep)
        #print(initialConds)  
        #print(len(initialConds))
        
        for i in range(len(initialConds)):
            time, self.initOutputT = PhasePlaneInitConds_simulate_time_course(self,initialConds[i])
            a9 = f9.add_subplot(111)
            line=a9.plot(self.initOutputT[:,model.index_1], self.initOutputT[:,model.index_2], color= 'g', linewidth=0.5)[0] #, hold=True)
            add_arrow(line)
#        concatenate_code1=''

#        for i in range(len(model.geneName)):  
#            concatenate_code1= concatenate_code1 + '{0} = Y[{1}]\n'.format(model.geneName[i],i)
#        concatenate_code1= concatenate_code1 + 'dy=np.zeros(({0}),dtype="float")\n'.format(model.num_gene)
#        for i in range(len(model.geneName)):
#            concatenate_code1= concatenate_code1 + '{0}= np.mgrid[model.min_value:model.max_value:100j, model.min_value:model.max_value:100j]\n'.format(model.geneName[i])
#        for i in range(len(model.AllParameters)):
#            concatenate_code1= concatenate_code1 + '{0}\n'.format(model.AllParameters[i])
        
#        for i in range(len(model.rhsList)):
#            concatenate_code1= concatenate_code1 + 'dy[{0}]={1}\n'.format(i,model.rhsList[i])
#        concatenate_code1= concatenate_code1 + 'ax0 = fig.add_subplot(111)\n'    
#        concatenate_code1= concatenate_code1 + 'ax0.streamplot(Y[{0}],Y[{1}],dy[{0}],dy[{1}],density=[0.5,1])\n'.format(model.index_1,model.index_2,model.index_1,model.index_2)
#        concatenate_code1= concatenate_code1 + 'plt.show()\n'                                                                                                                
#        exec(concatenate_code1)
        
        # Ket changes the y against x ( index_1 Vs index_2)
        a9.set_ylabel(str(model.geneName[model.index_1]))
        a9.set_xlabel(str(model.geneName[model.index_2]))   

        #print('model.index_2', model.index_2)
        #print('model.geneName[model.index_2]:',model.geneName[model.index_2])
        #a3.set_xlabel('protein 1')
        #a3.set_ylabel('protein 2')

        f9.canvas.draw_idle()        
        
        #status_bar_label.config(text="Start with loading an ode model.") 
        #a9 = f9.text(0.5, 0.5,"")   
#        a5 = f5.text(0.5, 0.5, "end point:"+str(self.outputT[-1,model.index_1+1])+str(self.outputT[-1,model.index_2+1]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        f9.canvas.draw_idle()
        
    if model.type == 'SBML':
           
        #n, self.outputT=model.calculate_timeCourse() 
        #n, time, self.outputT = sbml_simulate_time_course(self)
        #time, self.initOutputT = initConds_sbml_simulate_time_course(self) 
        #a9 = f9.add_subplot(111)

        initialConds=[]
        xc=np.linspace(model.min_value, model.max_value, 6)
        yc=np.linspace(model.min_value, model.max_value, 6)
        
        for i in range(len(xc)):
            i
            for j in range(len(yc)):
                j
                if model.num_gene==2:
                    initialConds.append([xc[i], yc[j]])
                else:
                    initCond=[]
                    for k in range(model.num_gene-2):
                        initCond.append(np.random.random()*(model.max_value-model.min_value))
                    Init_prep=[]
                    Init_prep.append(xc[i])
                    Init_prep.append(yc[j])
                    
                    for p in initCond:
                        Init_prep.append(p)
                    #print('Init_prep:',Init_prep)
                    initialConds.append(Init_prep)
        print(initialConds)  
        print(len(initialConds))
        
        for i in range(len(initialConds)):
            time, self.initOutputT = PhasePlaneInitConds_sbml_simulate_time_course(self,initialConds[i])
            a9 = f9.add_subplot(111)
            line=a9.plot(self.initOutputT[:,model.index_1], self.initOutputT[:,model.index_2], color= 'g', linewidth=0.5)[0] #, hold=True)
            add_arrow(line)
    
        #for i in range(2):
        #    print(i)
        #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
        #    print(eachInitCond)
        #    self.y=eachInitCond
        
        # Get one trajectory time-course data
        #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
        #    print(output)        
        #a3.plot(self.outputT[:,1], self.outputT[:,5], color= 'g', linewidth=0.5) #, hold=True)
        #a3.plot(self.outputT[:,model.index_1+1], self.outputT[:,model.index_2+1], color= 'g', linewidth=0.5) #, hold=True)
        a9.plot(self.initOutputT[:,model.index_1], self.initOutputT[:,model.index_2], color= 'g', linewidth=0.5) #, hold=True)
        # Ket changes y Against x (index_1 Vs index_2)
        a9.set_ylabel(str(model.geneName[model.index_1]))        
        a9.set_xlabel(str(model.geneName[model.index_2]))   

        print('model.index_2', model.index_2)
        print('model.geneName[model.index_2]:',model.geneName[model.index_2])
        #a3.set_xlabel('protein 1')
        #a3.set_ylabel('protein 2')

        f9.canvas.draw_idle()        
        
        #status_bar_label.config(text="Start with loading an ode model.") 
#        a9 = f9.text(0.5, 0.5,"")   
#        a5 = f5.text(0.5, 0.5, "end point:"+str(self.outputT[-1,model.index_1+1])+str(self.outputT[-1,model.index_2+1]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        f9.canvas.draw_idle()


#plot_add_phase_plane2_graph
def plot_add_phase_plane2_graph(self):
    '''This function add a trajectory to the phase plane.'''
    print("plot_phase_plane2_graph was called") 
    
    if model.name=='':
        tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
    if model.type == 'ode':
        
        time, self.initOutputT = initConds_simulate_time_course(self)
        a9 = f9.add_subplot(111)
        line=a9.plot(self.initOutputT[:,model.index_1], self.initOutputT[:,model.index_2], color= 'blue', linewidth=1)[0] #, hold=True)
        add_arrow(line)
#        concatenate_code1=''

#        for i in range(len(model.geneName)):  
#            concatenate_code1= concatenate_code1 + '{0} = Y[{1}]\n'.format(model.geneName[i],i)
#        concatenate_code1= concatenate_code1 + 'dy=np.zeros(({0}),dtype="float")\n'.format(model.num_gene)
#        for i in range(len(model.geneName)):
#            concatenate_code1= concatenate_code1 + '{0}= np.mgrid[model.min_value:model.max_value:100j, model.min_value:model.max_value:100j]\n'.format(model.geneName[i])
#        for i in range(len(model.AllParameters)):
#            concatenate_code1= concatenate_code1 + '{0}\n'.format(model.AllParameters[i])
        
#        for i in range(len(model.rhsList)):
#            concatenate_code1= concatenate_code1 + 'dy[{0}]={1}\n'.format(i,model.rhsList[i])
#        concatenate_code1= concatenate_code1 + 'ax0 = fig.add_subplot(111)\n'    
#        concatenate_code1= concatenate_code1 + 'ax0.streamplot(Y[{0}],Y[{1}],dy[{0}],dy[{1}],density=[0.5,1])\n'.format(model.index_1,model.index_2,model.index_1,model.index_2)
#        concatenate_code1= concatenate_code1 + 'plt.show()\n'                                                                                                                
#        exec(concatenate_code1)
        
        
        a9.set_xlabel(str(model.geneName[model.index_1]))   
        a9.set_ylabel(str(model.geneName[model.index_2]))
        #print('model.index_2', model.index_2)
        #print('model.geneName[model.index_2]:',model.geneName[model.index_2])
        #a3.set_xlabel('protein 1')
        #a3.set_ylabel('protein 2')

        f9.canvas.draw_idle()        
        
        #status_bar_label.config(text="Start with loading an ode model.") 
        #a9 = f9.text(0.5, 0.5,"")   
#        a5 = f5.text(0.5, 0.5, "end point:"+str(self.outputT[-1,model.index_1+1])+str(self.outputT[-1,model.index_2+1]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        f9.canvas.draw_idle()
        
    if model.type == 'SBML':
           
        #n, self.outputT=model.calculate_timeCourse() 
        #n, time, self.outputT = sbml_simulate_time_course(self)
        #time, self.initOutputT = initConds_sbml_simulate_time_course(self) 
        #a9 = f9.add_subplot(111)
        time, self.initOutputT = initConds_sbml_simulate_time_course(self) 
        a9 = f9.add_subplot(111)
        line=a9.plot(self.initOutputT[:,model.index_1], self.initOutputT[:,model.index_2], color= 'blue', linewidth=1.0)[0] #, hold=True)
        add_arrow(line)
    
        #for i in range(2):
        #    print(i)
        #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
        #    print(eachInitCond)
        #    self.y=eachInitCond
        
        # Get one trajectory time-course data
        #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
        #    print(output)        
        #a3.plot(self.outputT[:,1], self.outputT[:,5], color= 'g', linewidth=0.5) #, hold=True)
        #a3.plot(self.outputT[:,model.index_1+1], self.outputT[:,model.index_2+1], color= 'g', linewidth=0.5) #, hold=True)
        a9.plot(self.initOutputT[:,model.index_1], self.initOutputT[:,model.index_2], color= 'g', linewidth=0.5) #, hold=True)
        a9.set_xlabel(str(model.geneName[model.index_1]))   
        a9.set_ylabel(str(model.geneName[model.index_2]))
        print('model.index_2', model.index_2)
        print('model.geneName[model.index_2]:',model.geneName[model.index_2])
        #a3.set_xlabel('protein 1')
        #a3.set_ylabel('protein 2')

        f9.canvas.draw_idle()        
        
        #status_bar_label.config(text="Start with loading an ode model.") 
#        a9 = f9.text(0.5, 0.5,"")   
#        a5 = f5.text(0.5, 0.5, "end point:"+str(self.outputT[-1,model.index_1+1])+str(self.outputT[-1,model.index_2+1]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        f9.canvas.draw_idle()


def colorbar():
    print("colorbar was called.")

    f.clear()
    a = f.add_subplot(111, projection='3d')
    surf=a.plot_surface(model.X, model.Y, model.Z, cmap='jet')
    #f.colorbar(surf, shrink=0.5)   
    f.colorbar(surf,shrink=0.7,aspect=5)
    a.set_xlabel(str(model.geneName[model.index_2]))
    a.set_ylabel(str(model.geneName[model.index_1]))
    #a.set_ylabel('y')
    a.set_zlabel("U") 
    f.canvas.draw_idle()  
    

def no_colorbar():
    print("no_colorbar was called.")
    f.clear()
    a = f.add_subplot(111, projection='3d')
    surf=a.plot_surface(model.X, model.Y, model.Z, cmap='jet')

    a.set_xlabel(str(model.geneName[model.index_2]))
    a.set_ylabel(str(model.geneName[model.index_1]))
    #a.set_ylabel('y')
    a.set_zlabel("U") 
    f.canvas.draw_idle()  
    

def defaultSmoothSurface():
    print("defaultSmoothSurface was called.")
    #print("model.Smooth_U", model.Smooth_U)
    #model.Smooth_U = model.Z
    #if model.Smooth_U=='':
    #    tk.messagebox.showinfo("No model landscape plot (default).","Please plot landscape (default) first.") 
    #else:
        #def AverageU(self, AverU, size, stride):

    size=int(float(model.SmoothSurfSize))
    stride=1
    m, n = MCLandscape_U.shape
    
    if model.SmoothSurfSize==1: # when SmoothSurfSize=1 no smoothing apply  
        model.Smooth_U = MCLandscape_U.copy()
        print("model.Smooth_U was updated with default values")
    else:   
        print("AverageU was called")
        model.Smooth_U = MCLandscape_U.copy()  # cannot use model.Smooth_U = MCLandscape_U because MCLandscape_U will be updated when model.Smooth_U[ii, jj] = avg changes      
        for i in range(0, m - size + 1, stride):
            for j in range(0, n - size + 1, stride):
                avg = sum(sum(model.Smooth_U[i:i + size, j:j + size])) / (size * size)
                for ii in range(i, i + size):
                    for jj in range(j, j + size):
                        model.Smooth_U[ii, jj] = avg
                        
    f.clear()
    a = f.add_subplot(111, projection='3d')
    surf=a.plot_surface(model.X, model.Y, model.Smooth_U, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
    #f.colorbar(surf, shrink=0.5)    
    f.colorbar(surf,shrink=0.8,aspect=5)
    a.set_xlabel(str(model.geneName[model.index_2]))
    a.set_ylabel(str(model.geneName[model.index_1]))
    #a.set_ylabel('y')
    a.set_zlabel("U")    
    f.canvas.draw_idle()  

def clearerSurface_no_colorbar():
    print("clearerSurface_no_colorbar was called.")
    f.clear()
    a = f.add_subplot(111, projection='3d')
    surf=a.plot_surface(model.X, model.Y, model.Z, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')

    a.set_xlabel(str(model.geneName[model.index_2]))
    a.set_ylabel(str(model.geneName[model.index_1]))
    #a.set_ylabel('y')
    a.set_zlabel("U")    
    f.canvas.draw_idle()      
        
def clear_graph():
    print("clear_graph was called.")
    f.clear()
    f.add_subplot(111, projection='3d')
    f.canvas.draw_idle()  
    f4.clear()
    f4.add_subplot(111, projection='3d')
    f4.canvas.draw_idle()   
    f12.clear()
    f12.add_subplot(111, projection='3d')
    f12.canvas.draw_idle()     

def clear_top_view_graph():
    print("clear_top_view_graph was called.")
    f4.clear()
    f4.add_subplot(111, projection='3d')
    f4.canvas.draw_idle()  
    
def clear_time_course_graph():
    print("clear_time_course_graph was called.")
    f2.clear()
    f2.add_subplot(111)
    f2.canvas.draw_idle()  
    
def init_clear_time_course_graph():
    print("init_clear_time_course_graph")
    f7.clear()
    f7.add_subplot(111)
    f7.canvas.draw_idle()

def clear_phase_plane_graph():
    print("clear_graph was called.")
    f3.clear()
    f3.add_subplot(111)
    f3.canvas.draw_idle()  
    
def clear_phase_plane2_graph():
    print("clear_graph was called.")
    f9.clear()
    f9.add_subplot(111)
    f9.canvas.draw_idle()  


class MCLapp(tk.Tk):

    def __init__(self, *args, **kwargs):
                      
        tk.Tk.__init__(self, *args, **kwargs)
        
        #img = tk.PhotoImage(file='MCL.gif')
        #tk.Tk.call('wm', 'iconphoto', tk.Tk._w, img)
        tk.Tk.iconbitmap(self, default="MCL.ico")
        #tk.Tk.wm_iconbitmap(self,bitmap="@ImageMCL.xbm")
        tk.Tk.wm_title(self, '{} - {}'.format(os.path.basename(model.name),"MCLand: Waddington's Epigenetic Landscape Drawing App") )
        
        
        # first short cut bar
        shortcut_bar =tk.Frame(self, bd=1, height=30, relief=tk.RAISED, bg='lavender')
        shortcut_bar.pack(expand='no', fill='x')

        # second bar for buttons
        SecondBar=tk.Frame(self, bd=1, height=30, relief=tk.RAISED, bg='lavender')
        SecondBar.pack(expand='no', fill='x')

        # third status bar
        #        ThirdBar = tk.Frame(self, bd=1, height=30, relief=tk.RAISED, bg='lavender')
        #        ThirdBar.pack(expand='no', fill='x')
        
        self.img = PIL.Image.open("new_file.gif")
        eimg = ImageTk.PhotoImage(self.img)

        self.imgOpen = PIL.Image.open("open_file.gif")
        imgOpen = ImageTk.PhotoImage(self.imgOpen)
        
        
        self.imgOpenSBML = PIL.Image.open("open_file.gif")
        imgOpenSBML = ImageTk.PhotoImage(self.imgOpenSBML)
        
        self.imgOpenMCL = PIL.Image.open("open_file.gif")
        imgOpenMCL = ImageTk.PhotoImage(self.imgOpenSBML)
        
        
        self.imgSave = PIL.Image.open("save.gif")
        imgSave = ImageTk.PhotoImage(self.imgSave)
        
        self.imgAbout = PIL.Image.open("about.gif")
        imgAbout = ImageTk.PhotoImage(self.imgAbout)
        
        
#        fileNewButton=tk.Button(shortcut_bar, compound=tk.LEFT, activebackground='skyblue',image=eimg, text="ode Editor", relief=tk.RAISED, command=lambda: new_odeFile(self))
#        fileNewButton.image = eimg
#        fileNewButton.pack(side=tk.LEFT, padx=2, pady=2)  
        #fileNewButton.configure(state="normal", relief="raised", bg="skyblue")
        
        LoadodeModelButton=tk.Button(shortcut_bar,compound=tk.LEFT, activebackground='skyblue',image=imgOpen, text="Open ode", relief=tk.RAISED, command=lambda: open_file(self))
        LoadodeModelButton.image = imgOpen
        LoadodeModelButton.pack(side=tk.LEFT, padx=2, pady=1)
        
        
        LoadSBMLModelButton = tk.Button(shortcut_bar, compound=tk.LEFT, activebackground='skyblue',image=imgOpenSBML, text="Open SBML", relief=tk.RAISED, command=lambda: open_sbml_file(self))
        LoadSBMLModelButton.imgOpenSBML = imgOpenSBML
        LoadSBMLModelButton.pack(side=tk.LEFT, padx=2, pady=1)
        
        LoadMCLModelButton = tk.Button(shortcut_bar, compound=tk.LEFT, activebackground='skyblue',image=imgOpenMCL, text="Open MCL", relief=tk.RAISED, command=lambda: open_mc_land_file(self))
        LoadMCLModelButton.imgOpenMCL = imgOpenMCL
        LoadMCLModelButton.pack(side=tk.LEFT, padx=2, pady=1)        
        
        LoadSaveButton = tk.Button(shortcut_bar, compound=tk.LEFT, activebackground='skyblue', image=imgSave, text="Save As MCL", relief=tk.RAISED, command=self.save_as) #lambda: save_mc_land_file(self))
        LoadSaveButton.imgSave = imgSave
        LoadSaveButton.pack(side=tk.LEFT, padx=2, pady=1)      
        
#        LoadAboutButton = tk.Button(shortcut_bar, activebackground='skyblue', image=imgAbout ,relief=tk.RAISED, command= lambda: self.on_about_menu_clicked())
#        LoadAboutButton.imgAbout = imgAbout
#        LoadAboutButton.pack(side=tk.LEFT, padx=2, pady=1)          
  
#        ButtonInfoPage = tk.Button(shortcut_bar, compound=tk.LEFT, activebackground='skyblue', image=imgAbout,  text='Info Page', relief=tk.RAISED, command=lambda: show_info_page(self))
#        ButtonInfoPage.imgAbout=imgAbout
#        ButtonInfoPage.pack(side=tk.LEFT, padx=1, pady=1)
  

        
        container = tk.Frame(self)
        container.pack(side="top", fill="both", expand = True)
        container.grid_rowconfigure(0, weight=1)
        container.grid_columnconfigure(0, weight=1)
        
        # getting icons for compound menu
        new_file_icon = tk.PhotoImage(file='new_file.gif')
        
        menubar = tk.Menu(container)
        filemenu = tk.Menu(menubar, tearoff=0)
        filemenu.add_command(label="New ode File Model", compound='left', image=eimg, command=lambda: new_odeFile(self))
        filemenu.add_command(label="Load ode Model", compound='left', image=imgOpen, command=lambda: open_file(self))  #popupmsg('Not supported just yet!'))
        filemenu.add_command(label="Load SBML Model", compound='left', image=imgOpen, command=lambda: open_sbml_file(self))
        filemenu.add_command(label="Load MCLand Model", compound='left', image=imgOpen, command=lambda: open_mc_land_file(self))
        
        filemenu.add_separator()
        filemenu.add_command(label="Save As MCLand Model", compound='left', image=imgSave, command=self.save_as)#lambda: save_mc_land_file(self))
 
        filemenu.add_separator()
        filemenu.add_command(label="Exit", command=lambda: on_closing())
        menubar.add_cascade(label="File", menu=filemenu)
        
        about_menu = tk.Menu(menubar, tearoff=0)
        about_menu.add_command(label="About", compound='left', image=imgAbout, command= lambda: self.on_about_menu_clicked())
        menubar.add_cascade(label="About", menu=about_menu)
        #self.config(menu = self.menu_bar)  
        
        canvas_StatusBar = tk.Canvas(container, width=600, height=64, bg='blue')
        canvas_StatusBar.grid()
        status_bar_label = tk.Label(canvas_StatusBar, bg='yellow') #, text="Start with loading an ode model.", bg='yellow',bd=2, relief=tk.SUNKEN, anchor=tk.W)
        status_bar_label.grid(sticky='w')
        status_bar_label.config(text="Start with loading an ode model.")
        
        tk.Tk.config(self, menu=menubar)
        
        self.frames = {}

        for createFrame in (StartPage, InfoPage, NewODEPage, MethodSettingPage, SettingPage, InitConditionsPage2, InitTimeCoursePage, InitTimeCoursePage2, initTimeCourseDataViewer, ParameterPage, ParameterTimeCourseDataViewer, TimeCoursePage, TimeCourseDataViewer, PhasePlane_Page, PhasePlane_Page2, Graph_Page, Graph_Page2, Graph_Page3, PCAInfoPage, AttractorsInfoPage):

            frame = createFrame(container, self)

            self.frames[createFrame] = frame

            frame.grid(row=0, column=0, sticky="nsew")

#        statusBar=tk.Label(ThirdBar, text="Start calculating ...", bd=1, relief= tk.SUNKEN, anchor =tk.W)
#        statusBar.pack(side=tk.BOTTOM, fill =tk.X)    

        # variable for selected value
        global radioBtnVal
        radioBtnVal= tk.IntVar()

        # define the buttons for different page
        ButtonStartPage = tk.Radiobutton(SecondBar, text='Start Page', variable=radioBtnVal, value=1, command=lambda: show_start_page(self))
        ButtonStartPage['indicatoron']= 0 # display button instead of radiobutton
        ButtonStartPage['selectcolor'] = 'lightblue' # color after selection        
        ButtonStartPage.pack(side=tk.LEFT, padx=1, pady=1)
        
        ButtonOdeEditor= tk.Radiobutton(SecondBar, text='Ode Editor', variable=radioBtnVal, value=2, command=lambda: show_ode_editor(self))
        ButtonOdeEditor['indicatoron']= 0 # display button instead of radiobutton
        ButtonOdeEditor['selectcolor'] = 'lightblue' # color after selection          
        ButtonOdeEditor.pack(side=tk.LEFT, padx=1, pady=1)          
        
        ButtonModelSetting= tk.Radiobutton(SecondBar, text='Model Setting', variable=radioBtnVal, value=3, command=lambda: show_model_setting(self))
        ButtonModelSetting['indicatoron']= 0 # display button instead of radiobutton
        ButtonModelSetting['selectcolor'] = 'lightblue' # color after selection   
        ButtonModelSetting.pack(side=tk.LEFT, padx=1, pady=1)   

        ButtonMethodSetting = tk.Radiobutton(SecondBar, text='Monte Carlo Setting', variable=radioBtnVal, value=4, command=lambda: show_method_setting(self))
        ButtonMethodSetting['indicatoron']= 0 # display button instead of radiobutton
        ButtonMethodSetting['selectcolor'] = 'lightblue' # color after selection         
        ButtonMethodSetting.pack(side=tk.LEFT, padx=1, pady=1)
        
        ButtonTimeCourse = tk.Radiobutton(SecondBar, text='Time Course', variable=radioBtnVal, value=5, command=lambda: show_time_course(self))
        ButtonTimeCourse['indicatoron']= 0 # display button instead of radiobutton
        ButtonTimeCourse['selectcolor'] = 'lightblue' # color after selection
        ButtonTimeCourse.pack(side=tk.LEFT, padx=1, pady=1)
        
        ButtonPhasePlane = tk.Radiobutton(SecondBar, text='Phase Plane', variable=radioBtnVal, value=6, command=lambda: show_phase_plane(self))
        ButtonPhasePlane['indicatoron']= 0 # display button instead of radiobutton
        ButtonPhasePlane['selectcolor'] = 'lightblue' # color after selection
        ButtonPhasePlane.pack(side=tk.LEFT, padx=1, pady=1)        

        ButtonLandscape = tk.Radiobutton(SecondBar, text='3D Landscape', variable=radioBtnVal, value=7, command=lambda: show_landscape(self))
        ButtonLandscape['indicatoron']= 0 # display button instead of radiobutton
        ButtonLandscape['selectcolor'] = 'lightblue' # color after selection
        ButtonLandscape.pack(side=tk.LEFT, padx=1, pady=1)  
        
       

        ButtonSetParameterValues = tk.Radiobutton(SecondBar, text='Set Parameter Values', variable=radioBtnVal, value=9, command=lambda: show_set_parameter_values(self))
        ButtonSetParameterValues['indicatoron']= 0 # display button instead of radiobutton
        ButtonSetParameterValues['selectcolor'] = 'lightblue' # color after selection
        ButtonSetParameterValues.pack(side=tk.LEFT, padx=1)    
        
        ButtonTimeCourse2 = tk.Radiobutton(SecondBar, text='Time Course 2 Init', variable=radioBtnVal, value=10, command=lambda: show_time_course2(self))
        ButtonTimeCourse2['indicatoron']= 0 # display button instead of radiobutton
        ButtonTimeCourse2['selectcolor'] = 'lightblue' # color after selection
        ButtonTimeCourse2.pack(side=tk.LEFT, padx=1, pady=1)        
        
        ButtonPhasePlane2 = tk.Radiobutton(SecondBar, text='Phase Plane 2 Init', variable=radioBtnVal, value=11, command=lambda: show_phase_plane2(self))
        ButtonPhasePlane2['indicatoron']= 0 # display button instead of radiobutton
        ButtonPhasePlane2['selectcolor'] = 'lightblue' # color after selection
        ButtonPhasePlane2.pack(side=tk.LEFT, padx=1,pady=1)     

#        ButtonInitialCondition = tk.Radiobutton(SecondBar, text='Set Initial Conditions', variable=radioBtnVal, value=8, command=lambda: show_set_initial_conditions(self))
#        ButtonInitialCondition['indicatoron']= 0 # display button instead of radiobutton
#        ButtonInitialCondition['selectcolor'] = 'lightblue' # color after selection
#        ButtonInitialCondition.pack(side=tk.LEFT, padx=1, pady=1)   


        ButtonInfoPage = tk.Radiobutton(SecondBar, image=imgAbout, text='Info Page', variable=radioBtnVal, value=12, command=lambda: show_info_page(self))
        ButtonInfoPage.imgAbout=imgAbout
        ButtonInfoPage['indicatoron']= 0 # display button instead of radiobutton
        ButtonInfoPage['selectcolor'] = 'lightblue' # color after selection        
        ButtonInfoPage.pack(side=tk.LEFT, padx=1, pady=1)  
        
        ButtonExit = tk.Button(SecondBar, text='Exit', command=lambda: on_closing())
        ButtonExit.pack(side=tk.LEFT, padx=1, pady=1)         

        self.show_frame(StartPage)  
        
    def on_about_menu_clicked(self):
        messagebox.showinfo("About MCLand:", "MCLand: A Python Software package to plot Waddington's Epigenetic Landscape")

#    def method_button_invoke():
#        radioBtnVal=3
        #self.ButtonModelSetting.invoke()

    def show_frame(self, cont):
        #print("show_frame was called.")

        # A method which is run every time a frame is shown in tkinter
        #frame.event_generate("<<ShowFrame>>")
        
        frame = self.frames[cont]
        #print('cont:',cont)
        #print(str(cont) == "<class '__main__.SettingPage'>")
        #print('frame:',frame)
        #print(self)
        #if frame =='.!frame.!settingpage':
        #    print("SettingPage")    
        
        #if cont == 'SettingPage':
        #    print("SettingPage")
        
        # Turn on the StartPage RadioButton for initial start up page
        if str(cont) == "<class '__main__.StartPage'>":
            #print(cont)
            print("We are showing the StartPage")
            radioBtnVal.set(1)  
            
        # Turn on the EditorPage RadioButton for initial start up page        
        if str(cont) == "<class '__main__.NewODEPage'>":
            #print(cont)
            print("We are showing the EditorPage")
            radioBtnVal.set(2)

        # Turn on the SettingPage RadioButton for initial start up page        
        if str(cont) == "<class '__main__.SettingPage'>":
            #print(cont)
            print("We are showing the SettingPage")
            radioBtnVal.set(3)
 
         # Turn on the Monte Carlo Setting RadioButton for initial start up page        
        if str(cont) == "<class '__main__.MethodSettingPage'>":
            #print(cont)
            print("We are showing the Monte Carlo Setting")
            radioBtnVal.set(4)

         # Turn on the Time Course RadioButton for initial start up page        
        if str(cont) == "<class '__main__.TimeCoursePage'>":
            #print(cont)
            print("We are showing the Time Course")
            radioBtnVal.set(5)
            
        # Turn on the 3D Landscape Page RadioButton for initial loading of MCLand file page
        if str(cont) == "<class '__main__.Graph_Page'>":
            #print(cont)
            print("We are showing the Graph_Page 3D Landscape")
            radioBtnVal.set(7)  

         # Turn on the Time Course 2 RadioButton for initial start up page        
        if str(cont) == "<class '__main__.InitTimeCoursePage2'>":
            #print(cont)
            print("We are showing the Time Course 2")
            radioBtnVal.set(10)

         # Turn on the Phase plane 2 RadioButton for initial start up page        
        if str(cont) == "<class '__main__.PhasePlane_Page2'>":
            #print(cont)
            print("We are showing the Phase plane 2")
            radioBtnVal.set(11)
            # The setting of radioBtnVal.set(3) has solved the problem for enabling
            # the RadioButton for SettingPage been selected when opening new model
            # so no need to use the method_button_invoke()
            #self.method_button_invoke()


        
        tk.Tk.update(self)
        #frame.update()
        frame.update_frame()
        #print(frame.update())
        
        #frame.update()
        #frame.update_idletasks()
        #time.sleep(0.02)
        #frame.destroy()
        #frame = self.frames[cont]
        frame.tkraise()

    def write_to_file(self,file_name):
        try:
            #np.savetxt(file_name, model.DataOutputT, delimiter=",", fmt='%10.5f')
            file_nameMCL=open(file_name, 'wb')
            pickle.dump(model, file_nameMCL)
            file_nameMCL.close
            tk.messagebox.showinfo("Your MCLand model landscape data have been saved.","Your MCLand model landscape data (in the model object) have been saved using pickle.")              
            #tk.messagebox.showinfo("Your MCLand model landscape data (in the model object) have been saved using pickle.","Your landscape data have been saved into the file name + model_name + current time.pckl.")   
        except IOError:
            tkinter.messagebox.showwarning("Save", "Could not save the file.")


    def save_as(self,event=None):
        input_file_name = tk.filedialog.asksaveasfilename(defaultextension=".pckl",
                                                               filetypes=[("Pickle file", "*.pckl")])
        if input_file_name:
            global file_name
            file_name = input_file_name
            #model.ode_file_name = input_file_name
            self.write_to_file(file_name)
            #root.title('{} - {}'.format(os.path.basename(file_name), PROGRAM_NAME))
        return "break"

    def plot_landscape(self):
        print("plot_landscape was called.")
        x = linspace(-5,5,200)
        y = x
        X, Y = meshgrid(x,y)
    
        Z = bivariate_normal(X, Y)
    
        a = f.add_subplot(111, projection='3d')
    
        a.plot_surface(X, Y, Z, cmap = 'jet')          
        
    
    def update_model_info(self):
        pass
        
    def updat_count_SimNum(self):
        # update count in graph_page
        
        pass

    def start_progress(self):
        ''' Open modal window '''
        s = ProgressWindow(self, 'MyTest', self.lst)  # create progress window
        self.master.wait_window(s)  # display the window and wait for it to close

class ProgressWindow(simpledialog.Dialog):
    def __init__(self, parent, name, lst,mode):
        ''' Init progress window '''
        print('ProgressWindow was called.')
        tk.Toplevel.__init__(self, master=parent)
        self.name = name
        self.lst = lst
        self.length = 550
        self.mode = mode
        self.pcaNewData = np.empty([0, len(model.geneName)])
        #
        self.create_window()
        self.create_widgets()

    def create_window(self):
        ''' Create progress window '''
        print('create_window was called.')
        self.focus_set()  # set focus on the ProgressWindow
        self.grab_set()  # make a modal window, so all events go to the ProgressWindow
        self.transient(self.master)  # show only one window in the task bar
        #
        self.title(u'Calculate potential landscape for {}'.format(model.name))
        self.resizable(False, False)  # window is not resizable
        # self.close gets fired when the window is destroyed
        self.protocol(u'WM_DELETE_WINDOW', self.close)
        # Set proper position over the parent window
        dx = (self.master.master.winfo_width() >> 1) - (self.length >> 1)
        dy = (self.master.master.winfo_height() >> 1) - 50
        self.geometry(u'+{x}+{y}'.format(x = self.master.winfo_rootx() + dx,
                                         y = self.master.winfo_rooty() + dy))
        self.bind(u'<Escape>', self.close)  # cancel progress when <Escape> key is pressed

    def create_widgets(self):
        ''' Widgets for progress window are created here '''
        print('create_widgets was called.')
        self.var1 = tk.StringVar()
        self.var2 = tk.StringVar()
        self.num = tk.IntVar()
        self.maximum = len(self.lst)
        
        self.tmp_str = ' / ' + str(model.TrajectoryNumber)        
        #self.tmp_str = ' / ' + str(self.maximum)
        #
        # pady=(0,5) means margin 5 pixels to bottom and 0 to top
        ttk.Label(self, textvariable=self.var1).pack(anchor='w', padx=2)
        self.progress = ttk.Progressbar(self, maximum=model.TrajectoryNumber, orient='horizontal',
                                        length=self.length, variable=self.num, mode='determinate')
        #self.progress = ttk.Progressbar(self, maximum=self.maximum, orient='horizontal',
        #                                length=self.length, variable=self.num, mode='determinate')
        self.progress.pack(padx=2, pady=2)
        ttk.Label(self, textvariable=self.var2).pack(side='left', padx=2)
        ttk.Button(self, text='Cancel', command=self.close).pack(anchor='e', padx=1, pady=(0, 1))
        #
        self.next()

    def next(self):
        ''' Take next file from the list and do something with it '''
        n = model.loopNum
        #n = self.num.get()
        self.do_something_with_file(n+1, model.loopNum)  # some useful operation
        #self.do_something_with_file(n+1, self.lst[n])  # some useful operation
        self.var1.set('Trajectory number: ')
        n += 1

        #if n < self.maximum:
        if n < model.TrajectoryNumber:  
            # updated: 18 Feb 2020
            # reduce the 500 to smaller value to decrease the calculation time
            # self.after(500, self.next)  # call itself after some time
            self.after(1, self.next)  # call itself after some time
            self.var2.set(str(n) + self.tmp_str)
            self.num.set(n)            
            #calculate_potential_U(model)
        else:
            print('Potential Landscape calculation finished! The Landscape was plotted.')
            self.close()  # close window

    def do_something_with_file(self, number, name):
        #print("do_something_with_file was called.")
        model.loopNum = number

        i = number - 1
        eachInitCond = model.InitialConditions[i, :][:, None].T  # to ensure the same dimension of the matrix

        # Get one trajectory time-course data
        if model.type == 'ode':
            model.TimecourseData = simulate_time_course_for_PosProb(self, i)

        if model.type == 'SBML':
            model.TimecourseData = sbml_simulate_time_course_for_PosProb(self, i)
        # for loop for projecting one trajectory into the plane and calculate the probability distribution
        XMin, XMax, YMin, YMax = 0, 0, 0, 0
        if self.mode == "pca":  # do pca for each of trajectory
            #print('Calculate PCA Plot')
            self.pcaNewData = np.vstack((self.pcaNewData, model.TimecourseData))
            if number == model.TrajectoryNumber:
                pca = PCA(n_components=2)
                pca.fit(self.pcaNewData)
                newData = pca.transform(self.pcaNewData)
                print("PCA variance ratio:", pca.explained_variance_ratio_)
                XMin, XMax = min(newData[:, 0]), max(newData[:, 0])
                YMin, YMax = min(newData[:, 1]), max(newData[:, 1])
                # get union
                XMin = min(XMin, model.fromInitialCondition[0, 0])
                XMax = max(XMax, model.toInitialCondition[0, 0])
                YMin = min(YMin, model.fromInitialCondition[0, 0])
                YMax = max(YMax, model.toInitialCondition[0, 0])
                rowspan = (XMax - XMin) / model.gridNumber
                colspan = (YMax - YMin) / model.gridNumber
                print(newData.shape)
                for j in range(newData.shape[0]):  # for each sample get row and column position
                    row = int(floor((newData[j, 0] - XMin) / rowspan)) + 1
                    col = int(floor((newData[j, 1] - YMin) / colspan)) + 1
                    if (row > 0 and row < model.gridNumber) and (col > 0 and col < model.gridNumber):
                        model.PositionProb[row, col] += 1
        else:  # default
            #print('Calculate MCLand Plot')
            rowspan = (model.toInitialCondition[0, model.index_1] - model.fromInitialCondition[
                0, model.index_1]) / model.gridNumber
            colspan = (model.toInitialCondition[0, model.index_2] - model.fromInitialCondition[
                0, model.index_2]) / model.gridNumber
            for j in range(model.TimecourseData.shape[0]):  # for each sample get row and column position

                if (model.TimecourseData[j, model.index_1] - model.fromInitialCondition[0, model.index_1]) != NaN:
                    # print('j',j)
                    row = int(floor((model.TimecourseData[j, model.index_1] - model.fromInitialCondition[
                        0, model.index_1]) / rowspan)) + 1
                    # print(row)
                    col = int(floor((model.TimecourseData[j, model.index_2] - model.fromInitialCondition[
                        0, model.index_2]) / colspan)) + 1
                    # print(col)

                    if (row > 0 and row < model.gridNumber) and (col > 0 and col < model.gridNumber):
                        # update MCLandPositionProb
                        model.MCLandPositionProb[row, col] += 1
                       
            #print('Calculate PCA Plot')
            self.pcaNewData = np.vstack((self.pcaNewData, model.TimecourseData))
            if number == model.TrajectoryNumber:
                pca = PCA(n_components=2)
                pca.fit(self.pcaNewData)
                newData = pca.transform(self.pcaNewData)
                #print("PCA variance ratio:", pca.explained_variance_ratio_)
                model.PCA_Ratio = pca.explained_variance_ratio_
                XMin, XMax = min(newData[:, 0]), max(newData[:, 0])
                YMin, YMax = min(newData[:, 1]), max(newData[:, 1])
                # get union
                XMin = min(XMin, model.fromInitialCondition[0, 0])
                XMax = max(XMax, model.toInitialCondition[0, 0])
                YMin = min(YMin, model.fromInitialCondition[0, 0])
                YMax = max(YMax, model.toInitialCondition[0, 0])
                rowspan = (XMax - XMin) / model.gridNumber
                colspan = (YMax - YMin) / model.gridNumber
                #print(newData.shape)
                for j in range(newData.shape[0]):  # for each sample get row and column position
                    row = int(floor((newData[j, 0] - XMin) / rowspan)) + 1
                    col = int(floor((newData[j, 1] - YMin) / colspan)) + 1
                    if (row > 0 and row < model.gridNumber) and (col > 0 and col < model.gridNumber):
                        # update MCLandPositionProb
                        model.PositionProb[row, col] += 1                        
                        
            XMin, XMax = model.fromInitialCondition[0, model.index_1], model.toInitialCondition[0, model.index_1]
            YMin, YMax = model.fromInitialCondition[0, model.index_2], model.toInitialCondition[0, model.index_2]
        number += 1

        if number == model.TrajectoryNumber + 1:
            if self.mode == "pca":  # do pca for each of trajectory 
                model.X, model.Y, model.Z_PCA= model.Plotting_Landscape(XMin, XMax, YMin, YMax)
                #print("In ProgressWindow model.Z_PCA was updated")
                
                f.clear() 
                a = f.add_subplot(111, projection='3d')
                #a.plot_surface(model.X, model.Y, model.Z, cmap='jet')
                surf=a.plot_surface(model.X, model.Y, model.Z_PCA, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
                f.colorbar(surf,shrink=0.8,aspect=5)
                
                a.set_xlabel("PC 1")
                a.set_ylabel("PC 2")     
                a.set_zlabel("U")
                f.canvas.draw_idle()     
                
                # to plot top view into f4 GraphPage2
                f4.clear() 
                a4 = f4.add_subplot(111, projection='3d')
                a4.plot_surface(model.X, model.Y, model.Z_PCA, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
                f4.colorbar(surf,shrink=0.8,aspect=5)
                # add contour to the 3D surface plot
                # a.contour(X, Y, Z, zdir='z', offset=0, cmap='jet')
                # print(model.index_1)
                if self.mode == "pca":
                    a4.set_xlabel("PC 1")
                    a4.set_ylabel("PC 2")
                else:
                    a4.set_xlabel(str(model.geneName[model.index_2]))
                    a4.set_ylabel(str(model.geneName[model.index_1]))
                # a.set_ylabel('y')
                a4.set_zlabel("U")
                a4.view_init(elev=90, azim=-90)
                f4.canvas.draw_idle()                
                
            # MCLand Calculate and Plot Landscape    
            else:
                #model.X, model.Y, model.Z_d= model.Plotting_Landscape(XMin, XMax, YMin, YMax)
                # Normalized probability
                print("In ProgressWindow MCLand Calculate and Plot Landscape")
                model.MCLandPositionProb = model.MCLandPositionProb + np.ones(model.MCLandPositionProb.shape)

                MCLand_ProbT = model.MCLandPositionProb  # [0:99,0:99]
                MCLand_normalized_ProbT = MCLand_ProbT / (sum(sum(MCLand_ProbT)))
                #MCLand_U = -(MCLand_normalized_ProbT)
                MCLand_U = -np.log(MCLand_normalized_ProbT)
                #print("MCLand_U size:", MCLand_U.shape)
                               
        
                xT = linspace(XMin, XMax, model.gridNumber)
                yT = linspace(YMin, YMax, model.gridNumber)
                [ MCLand_X,  MCLand_Y] = meshgrid(xT, yT)                
                
                #model.Z=model.Z_d
                global MCLandscape_U 
                MCLandscape_U = MCLand_U               
                #model.Z=MCLandscape_U
                model.X =  MCLand_X
                model.Y =  MCLand_Y
                #print("In ProgressWindow MCLandscape_U was updated") 

                
                f.clear()
                a = f.add_subplot(111, projection='3d')
                surf=a.plot_surface(model.X, model.Y, MCLandscape_U, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
                f.colorbar(surf,shrink=0.8,aspect=5)
                
                a.set_xlabel(str(model.geneName[model.index_2]))
                a.set_ylabel(str(model.geneName[model.index_1]))  
                a.set_zlabel("U")
                f.canvas.draw_idle()      
                
                # to plot top view into f4 GraphPage2
                f4.clear() 
                a4 = f4.add_subplot(111, projection='3d')
                a4.plot_surface(model.X, model.Y, MCLandscape_U, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
                f4.colorbar(surf,shrink=0.8,aspect=5)
                # add contour to the 3D surface plot
                # a.contour(X, Y, Z, zdir='z', offset=0, cmap='jet')
                # print(model.index_1)
                if self.mode == "pca":
                    a4.set_xlabel("PC 1")
                    a4.set_ylabel("PC 2")
                else:
                    a4.set_xlabel(str(model.geneName[model.index_2]))
                    a4.set_ylabel(str(model.geneName[model.index_1]))
                # a.set_ylabel('y')
                a4.set_zlabel("U")
                a4.view_init(elev=90, azim=-90)
                f4.canvas.draw_idle()                
                
                # PCA Calculation and Plotting
                model.X, model.Y, model.Z_PCA= model.Plotting_Landscape(XMin, XMax, YMin, YMax)
                #print("In ProgressWindow model.Z_PCA was updated")
                
                f12.clear() 
                a12 = f12.add_subplot(111, projection='3d')
                #a.plot_surface(model.X, model.Y, model.Z, cmap='jet')
                # for clearer surface use below plot
                surf=a12.plot_surface(model.X, model.Y, model.Z_PCA, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
                f12.colorbar(surf,shrink=0.8,aspect=5)
                
                a12.set_xlabel("PC 1")
                a12.set_ylabel("PC 2")     
                a12.set_zlabel("U")
                f12.canvas.draw_idle()                    


            Attractors = np.vstack({tuple(row) for row in model.TempAttractors})
            model.Attractors = Attractors
            #print('Number of attractors=', len(Attractors))
            #print('Attractors:')
            #print(Attractors)

            # Plot 3D graph

            # to plot 3D view into f GraphPage
            #f.clear()  # clear first of all
            #f.add_subplot(111, projection='3d')
            #f.canvas.draw_idle()

            #a = f.add_subplot(111, projection='3d')
            #a.plot_surface(model.X, model.Y, model.Z, cmap='jet')
            # for clearer surface use below plot
            #surf=a.plot_surface(model.X, model.Y, model.Z, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
            #f.colorbar(surf,shrink=0.8,aspect=5)

            #if self.mode == "pca":
            #    a.set_xlabel("PC 1")
            #    a.set_ylabel("PC 2")
            #else:
            #    a.set_xlabel(str(model.geneName[model.index_2]))
            #    a.set_ylabel(str(model.geneName[model.index_1]))
            # a.set_ylabel('y')
            #a.set_zlabel("U")
            #f.canvas.draw_idle()

            # to plot top view into f4 GraphPage2
            #f4.clear() 
            #a4 = f4.add_subplot(111, projection='3d')
            #a4.plot_surface(model.X, model.Y, model.Z, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
            #f4.colorbar(surf,shrink=0.8,aspect=5)
            # add contour to the 3D surface plot
            # a.contour(X, Y, Z, zdir='z', offset=0, cmap='jet')
            # print(model.index_1)
            #if self.mode == "pca":
            #    a4.set_xlabel("PC 1")
            #    a4.set_ylabel("PC 2")
            #else:
            #    a4.set_xlabel(str(model.geneName[model.index_2]))
            #    a4.set_ylabel(str(model.geneName[model.index_1]))
            # a.set_ylabel('y')
            #a4.set_zlabel("U")
            #a4.view_init(elev=90, azim=-90)
            #f4.canvas.draw_idle()


    def close(self, event=None):
        ''' Close progress window '''
        print('Close progress window')
        #print(self.progress['value'])
        if (self.progress['value']+1) == model.TrajectoryNumber:
            print('Ok: process finished successfully')
        else:
            print('Cancel: process is cancelled')
        self.master.focus_set()  # put focus back to the parent window
        self.destroy()  # destroy progress window
    def start_progress(self):
        ''' Open modal window '''
        print('start_progress was called.')
        s = ProgressWindow(self, model.name, self.lst)  # create progress window
        #s = ProgressWindow(self, 'MyTest', self.lst)  # create progress window
        self.master.wait_window(s)  # display the window and wait for it to close



        

# A method which is run every time a frame is shown in tkinter     
class UpdatePage(tk.Frame):
    def __init__(self, parent, controller):
        
        self.bind("<<ShowFrame>>", self.on_show_frame)
        
    def on_show_frame(self, event):
        print("I am being shown ...")
        
        
class StartPage(tk.Frame):

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self,parent)
        
        label = tk.Label(self, text="Start Page", font=LARGE_FONT)
        label.pack(pady=5)
        
        labelMCLandTitle = tk.Label(self, text="MCLand: A Python program for drawing emerging shapes of Waddington's epigenetic landscape by Monte Carlo simulations", font="Verdana 10 bold")
        labelMCLandTitle.pack(pady=5)

        info_Text =tk.Text(self, wrap='word', bg='lavender',font='Arial 10', height=12)
        info_Text.pack(pady=1)
        info_Text.insert(1.0,"Welcome to MCLand!\n\nYou can load a model in XPPAUT ode file format or in SBML .xml file format.\nFor example, using File --> Load ode model.\nThe ode model file requires the ordinary differential equation and parameter values defined by 'par' list.\nYou can use the ode Editor to create your model file.\nPlease refer to the examples on how to prepare an ode model file which ends with '.ode' file extension.")
        info_Text.config(state=tk.DISABLED)

#        label=tk.Label(self, text="Main Window", font=LARGE_FONT)
#        label.pack(pady=2)    

#        canvas=tk.Canvas(self, width=400, height=400, bg='wheat', bd=2, highlightthickness=1, highlightbackground="black")
#        canvas.pack(pady=5,padx=20,ipadx=1, ipady=5)        
        
#        label = tk.Label(canvas, text=("""Waddington's Epigenetic Landscape Drawing Application
#        using Monte Carlo Method."""), font=LARGE_FONT, relief=tk.SUNKEN, bg='tomato', foreground='white')
#        label.pack(pady=2,padx=10,ipadx=20, ipady=10)
        

        
        #canvas_landImage = tk.Canvas(self, width=600, height=600, bg='lavender')
        #canvas_landImage.pack(side='left', expand=True)
        #photo = tk.PhotoImage(file =r'C:/ket_image/MCL_Artistic.gif')
        #photo = tk.PhotoImage(file =r'../MCL_Artistic.gif')
              
        
        #filename='MCL_Artistic.gif'
        #photoArtistic = tk.PhotoImage(file =filename)
        #label =tk.Label(image=photoArtistic)
        #label.image = photoArtistic # keep a reference!
        # Why do my Tkinter images not appear? http://effbot.org/pyfaq/why-do-my-tkinter-images-not-appear.htm
        #label.pack() not to show the label as a trick to get the image appear

        #canvas_landImage.create_image(300, 300, image=photoArtistic, tags=("occupied"), anchor='c')
        #canvas_landImage.update()

        #buttonModelSetting = ttk.Button(self, text="Model Setting")
        #buttonModelSetting.pack(pady=2,padx=50, ipadx=5)   
        #buttonModelSetting.bind("<Button>", new_window_model_setting)                
        
#        buttonNewODEmodel = ttk.Button(canvas, text="ode Editor",
#                            command=lambda: controller.show_frame(NewODEPage))
#        buttonNewODEmodel.pack(pady=2,padx=50, ipadx=5, ipady=5)   


#        button5 = ttk.Button(canvas, text="Model Setting",
#                            command=lambda: controller.show_frame(SettingPage))
#        button5.pack(pady=2,padx=50, ipadx=5, ipady=5)   
        
#        button5 = ttk.Button(canvas, text="Monte Carlo Setting",
#                            command=lambda: controller.show_frame(MethodSettingPage))
#        button5.pack(pady=2,padx=50, ipadx=5, ipady=5)  
        
        #button6 = ttk.Button(self, text="Time Course Data",
        #                    command=lambda: controller.show_frame(DataPage))
        #button6.pack(pady=2,padx=50, ipadx=5)        

#        button1 = ttk.Button(canvas, text="Time Course",
#                            command=lambda: controller.show_frame(TimeCoursePage))
#        button1.pack(pady=2,padx=50, ipadx=5, ipady=5)
                               
#        button4 = ttk.Button(canvas, text="Phase Plane",
#                            command=lambda: controller.show_frame(PhasePlane_Page))
#        button4.pack(pady=2,padx=50, ipadx=5, ipady=5)        
        
#        button2 = ttk.Button(canvas, text="3D Landscape",
#                            command=lambda: controller.show_frame(Graph_Page))
#        button2.pack(pady=2,padx=50, ipadx=5, ipady=5)
        
        #button6 = ttk.Button(self, text="Top View",
        #                    command=lambda: controller.show_frame(Graph_Page2))
        #button6.pack(pady=2,padx=50, ipadx=5)        

#        canvasNormalSimulator = tk.Canvas(self, width=300, height=300, bg= 'lavender', highlightthickness=1, highlightbackground="black")
#        canvasNormalSimulator.pack(pady=5,padx=20,ipadx=1, ipady=5)

#        labelSimulator = tk.Label(canvasNormalSimulator, text=("""Normal Simulator 
#        with user key in initial conditions or parameter values"""), font=('Verdana', 12), bg= 'royalblue', relief=tk.SUNKEN, foreground='white')
#        labelSimulator.pack(pady=2,padx=10,ipadx=20, ipady=10)
            
#        buttonInit2 = ttk.Button(canvasNormalSimulator, text="Set Initial Conditions", command=lambda: controller.show_frame(InitConditionsPage2))
#        buttonInit2.pack(pady=2,padx=50, ipadx=5, ipady=5)
        
#        buttonParam = ttk.Button(canvasNormalSimulator, text="Set Parameter Values", command=lambda: controller.show_frame(ParameterPage))
#        buttonParam.pack(pady=2,padx=50, ipadx=5, ipady=5)
        
#        buttonInitTimeCoursePage = ttk.Button(canvasNormalSimulator, text="Time Course 2", command=lambda: controller.show_frame(InitTimeCoursePage2))
#        buttonInitTimeCoursePage.pack(pady=2,padx=50, ipadx=5, ipady=5)

#        buttonPhasePlane2 = ttk.Button(canvasNormalSimulator, text="Phase Plane 2", command=lambda: controller.show_frame(PhasePlane_Page2))
#        buttonPhasePlane2.pack(pady=2,padx=50, ipadx=5, ipady=5)

#        button3 = ttk.Button(self, text="Exit",
#                            command=lambda: on_closing())
#        button3.pack(pady=5,padx=50, ipadx=5, ipady=5)
        
        status_bar_label = tk.Label(self, text="Start with loading an ode or a SBML model.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)

    def update_frame(self):
        
        print("update_frame was called.")

class InfoPage(tk.Frame):

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self,parent)
        
        label = tk.Label(self, text="Info Page", font=LARGE_FONT)
        label.pack(pady=5)
        
        labelMCLandTitle = tk.Label(self, text="MCLand: A Python program for drawing emerging shapes of Waddington's epigenetic landscape by Monte Carlo simulations", font="Verdana 10 bold")
        labelMCLandTitle.pack(pady=5)

        labelMCLandAuthor = tk.Label(self, text="Author: Ket Hing Chong\u00B9, Xiaomeng Zhang\u00B9, Lin Zhu\u00B2 & Jie Zheng\u00B2", font=('Verdana', 12), justify=tk.LEFT)
        #labelMCLandAuthor = tk.Label(self, text="Author: Ket Hing Chong\u00B9, Xiaomeng Zhang\u00B9 & Jie Zheng\u00B9\u22C5\u00B2", font=('Verdana', 12), justify=tk.LEFT)
        labelMCLandAuthor.pack(pady=5)
        
        # Affiliation
        labelMCLandAffiliationLine1= tk.Label(self, text="\u00B9 Biomedical Informatics Lab,\n  School of Computer Science and Engineering \n  Nanyang Technological University, Singapore", font=('Verdana', 12), justify=tk.LEFT)
        labelMCLandAffiliationLine1.pack(pady=5)  
        
        labelMCLandAffiliationLine1= tk.Label(self, text="\u00B2 School of Information Science and Technology,\n   ShanghaiTech University, Pudong District, Shanghai 201210, China", font=('Verdana', 12), justify=tk.LEFT)
        labelMCLandAffiliationLine1.pack(pady=5)        
                
        # Information for citation of the work         
        labelCitationInfo = tk.Label(self, text="\n\n\n\n\n\nIf you are using this software for your research work, please cite the two papers listed below:\n1. Zhang, X., Chong, K.H., Zhu, L. & Zheng, J. (2020). A Monte Carlo method for in silico modeling and visualization of Waddington's epigenetic landscape with intermediate details. \n    Biosystems. doi: https://doi.org/10.1016/j.biosystems.2020.104275  \n2. Chong, K.H., Zhang, X., Zhu, L. & Zheng, J. (2022). MCLand: A Python program for drawing emerging shapes of Waddington's epigenetic landscape by Monte Carlo simulations", font=('Verdana', 10), justify=tk.LEFT)
        labelCitationInfo.pack(pady=5)
 
        # About the license 
        labelMCLandLicenseName = tk.Label(self, text="MCLand is licensed under the GNU General Public License v2.0", font="Verdana 10 bold", justify=tk.LEFT)
        labelMCLandLicenseName.pack(pady=5)        
        labelMCLandLicense = tk.Label(self, text="About the License", font="Verdana 10 bold", justify=tk.LEFT)
        labelMCLandLicense.pack(pady=5)
        
        labelLicenseInfo = tk.Label(self, text="GNU General Public License v2.0", font="Verdana 10 bold", justify=tk.LEFT)
        labelLicenseInfo.pack(pady=2)
        labelLicenseInfo2=tk.Label(self, text="The GNU GPL is the most widely used free software license and has a strong copyleft requirement.\nWhen distributing derived works, the source code of the work must be made available under the same license.\nThere are multiple variants of the GNU GPL, each with different requirements.", justify=tk.LEFT)
        labelLicenseInfo2.pack(pady=2)
        
        status_bar_label = tk.Label(self, text="Start with loading an ode or a SBML model.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)
        
         

    def update_frame(self):
        
        print("update_frame was called.")
    
    


class NewODEPage(tk.Frame):
    '''This page allow user to create new XPPAUT model file that can be saved as .ode'''

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        
        label = tk.Label(self, text="ode Editor", font=LARGE_FONT)
        label.grid(row=0,column=1,pady=2,padx=10,sticky=tk.N+tk.E+tk.S+tk.W)
        
#        button1 = ttk.Button(self, text="Back to Main Window",
#        command=lambda: controller.show_frame(StartPage))
#        button1.grid(row=1,column=1)       
        
        label_Header2=tk.Label(self, text="Create new XPPAUT .ode model file by using the editor below:",  font="Verdana 10 bold")
        label_Header2.grid(row=3, column=1, pady=2, padx=2)
        #labelCurrentValues = tk.Label(self, text="Below is the editor for ode file:")
        #labelCurrentValues.grid(row=5,column=0, pady=2, padx=2)
 
        self.ode_content=tk.Text(self, wrap='word', font=("Helvetica", 12), width=100, height=30, borderwidth=2, relief=tk.GROOVE)
        self.ode_content.grid(row=7,column=1, ipadx=10,pady=5, padx=20)
        
        #self.ode_content.columnconfigure(0, weight=3)
        #self.ode_content.columnconfigure(1, weight=1)
        # add a vertical scrollbar to Text widget
        #self.canvas=tk.Canvas(self, borderwidth=0, bg='lavender', width=100, height=100)
        #self.frame = tk.Frame(self.canvas, bg='lavender', width=100, height=100)
        
        
        #self.vs = tk.Scrollbar(self.ode_content, orient="vertical", command = self.canvas.yview)
 
        #self.canvas.configure(yscrollcommand=self.vs.set)
        #self.vs.grid()
        #self.vs.pack(side="right", fill="y")    
        
        #self.canvas.grid()
        #self.canvas.pack(side='left', fill='both',expand=True)
        #self.canvas.create_window((4,4), window=self.frame, anchor='nw',tags='self.frame')
        
        #self.frame.bind("<Configure>", self.onFrameConfigure)
        
        #self.ode_content.config(yscrollcommand=self.vs.set)        
        #self.vs.config(command=self.ode_content.yview)
        
        
        # User control buttons
        buttonNew = ttk.Button(self, text="New", command=self.new)
        buttonNew.grid(row=0,column=0)
        
        buttonOpen = ttk.Button(self, text="Open", command=self.open)
        buttonOpen.grid(row=1,column=0)        
        
        buttonSave = ttk.Button(self, text="Save", command=self.save)
        buttonSave.grid(row=2,column=0)
                        
        buttonSaveAs = ttk.Button(self, text="Save As", command=self.save_as)
        buttonSaveAs.grid(row=3,column=0)


        

        #buttonPlot.bind("<Button>", Save_method_setting(controller)) 
        
    def onFrameConfigure(self, event):
        '''Reset the scroll region to encompass the inner frame'''
        self.canvas.configure(scrollregion=self.canvas.bbox('all'))    
        
    def write_to_file(self,file_name):
            try:
                content = self.ode_content.get(1.0, 'end')
                with open(file_name, 'w') as the_file:
                    the_file.write(content)
            except IOError:
                tkinter.messagebox.showwarning("Save", "Could not save the file.")
        
        
    def save_as(self,event=None):
            input_file_name = tk.filedialog.asksaveasfilename(defaultextension=".ode",
                                                                   filetypes=[("XPPAUT model file", "*.ode")])
            if input_file_name:
                global file_name
                file_name = input_file_name
                model.ode_file_name = input_file_name
                self.write_to_file(file_name)
                #root.title('{} - {}'.format(os.path.basename(file_name), PROGRAM_NAME))
            return "break"
        
    def save(self,event=None):
        global file_name

        # if ode file already save
        #if model.ode_file_name !='':
        if model.ode_file_name =='':
            self.save_as()
        else:
            self.write_to_file(file_name)
        #else:
        #    self.write_to_file(file_name)
        return "break"
    
        
    def new(self):
        self.ode_content.delete(1.0, 'end')

        
    def open(self,event=None):
        input_file_name = tk.filedialog.askopenfilename(defaultextension=".ode",
                                                         filetypes=[("ode file", "*.ode")])
        if input_file_name:
            global file_name
            file_name = input_file_name
            model.ode_file_name = file_name
            #self.title('{} - {}'.format(os.path.basename(file_name), PROGRAM_NAME))
            self.ode_content.delete(1.0, 'end')
            with open(file_name) as _file:
                self.ode_content.insert(1.0, _file.read())



    def save_method_setting(self):
#        #self.controller=controller
        print("save_model_setting was called.")
        self.stepSize_h.set(self.entryStepSize.get())
        if self.stepSize_h.get() !='':
            setattr( model,'h', float(self.stepSize_h.get()) )
            self.label_h.config(text=model.h) # to update the label text for h
        
        self.TrajNumber.set(self.entryTrajNumber.get())
        if self.entryTrajNumber.get() != '':
            setattr( model, 'TrajectoryNumber', int(self.TrajNumber.get()) )
            self.labelTrajNumber.config(text=model.TrajectoryNumber)
            
            # re-initialise the size of these two matrices
            model.InitialConditions=np.zeros((model.TrajectoryNumber,model.num_gene))
            model.TempAttractors=np.zeros((model.TrajectoryNumber,model.num_gene))
            
            #'''This loop get all the random initial conditions in the state space'''  
            for j in range(model.num_gene):
                #print(j)
                model.InitialConditions[:,j][:,None]=np.random.random((model.TrajectoryNumber,1))*(model.toInitialCondition[0,j]-model.fromInitialCondition[0,j])+model.fromInitialCondition[0,j]
                #print(model.InitialConditions.shape)           

        
        self.TimeEnd.set(self.entryTimeEnd.get())
        if self.TimeEnd.get() !='':
            setattr( model, 't_end', float(self.TimeEnd.get()) )
            self.labelTimeEnd.config(text=model.t_end)
        
        self.GridNumber.set(self.entryGridNumber.get())
        if self.GridNumber.get() !='':
            setattr( model, 'gridNumber', int(self.GridNumber.get()) )
            self.labelGridNumber.config(text=model.gridNumber)
           

    def update_frame(self):
        self.update()    
 
        

class SettingPage(tk.Frame):
    '''This page shows the model equations and setting of the two variables for plotting the Waddington's epigenetic landscape. User can change the two variables and it's maximum value. '''
    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
                
#        label = tk.Label(self, text="Model setting page", font=LARGE_FONT)
#        label.grid(row=0,column=2,pady=10,padx=10)
        
#         label_Header1=tk.Label(self, text="model information",  font="Verdana 10 bold")
#         label_Header1.grid(row=2, column=1, pady=2, padx=2)
        
        # from ModelSetting
        #self.frame = tk.Frame(self)
        self.table_frame= tk.Frame(self, bg='lavender', width=1800, height=1000)
        self.table_frame.grid(row=0,column=0,pady=5,padx=10, sticky="EWNS")  
    
        
        label = tk.Label(self.table_frame, text="Model Setting", font=LARGE_FONT)
        label.grid(row=0,column=2,pady=5,padx=10)

        # refresh radio button to 3 for SettingPage
        #radioBtnVal= 3
 
#        button1 = ttk.Button(self.table_frame, text="Back to Main Window", command=lambda: controller.show_frame(StartPage))
#        button1.grid(row=1,column=2)       
        
        label_Header1=tk.Label(self.table_frame, text="Model Information",  font="Verdana 10 bold")
        label_Header1.grid(row=2, column=1, pady=2, padx=2)
                           
        #self.RefreshButton = ttk.Button(self.table_frame, text='Refresh model setting', width =25, command= self.refresh_model_setting)
        #self.RefreshButton.grid(row=2, column=2, padx=10, pady=10) 
        
        labelP1 = tk.Label(self.table_frame, text="Model Name:", width=20, font=NORMAL_FONT)
        labelP1.grid(row=3, column=1, pady=2, padx=2)
        self.labelP1A = tk.Label(self.table_frame, width=60, text=model.name, font=NORMAL_FONT)
        self.labelP1A.grid(row=3, column=2)  
        self.labelP1A.config(text=model.name)
        
        labelModelType = tk.Label(self.table_frame, text="Model Type:", font=NORMAL_FONT)
        labelModelType.grid(row=2, column=3, pady=2, padx=2)
        self.labelModelTypeA = tk.Label(self.table_frame, width=20, text=model.type, font=NORMAL_FONT)
        self.labelModelTypeA.grid(row=3, column=3)
        self.labelModelTypeA.config(text=model.type)
       
        #labelP2 = tk.Label(table_frame, text="gene names:", font=NORMAL_FONT)
        #labelP2.grid(row=4, column=1, pady=2, padx=2)
        #labelP2A = tk.Label(table_frame, width=60, wraplength=50,text=model.geneName, font=NORMAL_FONT)
        #labelP2A.grid(row=4, column=2)   
        
        labelCurrentValue = tk.Label(self.table_frame, text="Current Values", font=NORMAL_FONT)
        labelCurrentValue.grid(row=5, column=2)          
        
        labelNewValue = tk.Label(self.table_frame, text="Set New Values:", font=NORMAL_FONT)
        labelNewValue.grid(row=5, column=3)   
 
        self.labelP5 = tk.Label(self.table_frame, text="Min. Value:", width=20, font=NORMAL_FONT)
        self.labelP5.grid(row=7, column=1, pady=2, padx=2)
        self.labelP5A = tk.Label(self.table_frame, width=60, text=model.min_value, font=NORMAL_FONT)
        self.labelP5A.grid(row=7, column=2)  
        
        #global minValue
        self.minValue=tk.StringVar()
        #self.DisplayMinValue=tk.StringVar()
        #self.DisplayMinValue.set('0')
        #self.minValue.set(model.min_value)
        self.entryP5 = tk.Entry(self.table_frame, width=10, textvariable=self.minValue)
        self.entryP5.grid(row=7, column=3)    

 
        self.labelP6 = tk.Label(self.table_frame, text="Max. Value:", width=20, font=NORMAL_FONT)
        self.labelP6.grid(row=8, column=1, pady=2, padx=2)
        self.labelP6A = tk.Label(self.table_frame, width=60, text=model.max_value, font=NORMAL_FONT)
        self.labelP6A.grid(row=8, column=2)          

        #global maxValue
        self.maxValue=tk.StringVar()
        #self.maxValue=tk.IntVar()
        self.entryP6 = tk.Entry(self.table_frame, width=10, textvariable=self.maxValue)
        self.entryP6.grid(row=8, column=3)  
        
        labelP3 = tk.Label(self.table_frame, text="Gene 1 (index 1):", width=20, font=NORMAL_FONT)
        labelP3.grid(row=9, column=1, pady=2, padx=2)  
        self.labelP3A = tk.Label(self.table_frame, width=60, text=model.index_1, font=NORMAL_FONT)
        self.labelP3A.grid(row=9, column=2)           
        # create an entry for user to key in the index_1
        self.SV_index_1 = tk.StringVar()
        self.entry3B = tk.Entry(self.table_frame, width=15, textvariable=self.SV_index_1)
        #self.entry3B.grid(row=9, column=3)
        
        

        labelP4 = tk.Label(self.table_frame, text="Gene 2 (index 2):", width=20, font=NORMAL_FONT)
        labelP4.grid(row=10, column=1, pady=2, padx=2)  
        self.labelP4A = tk.Label(self.table_frame, width=60, text=model.index_2, font=NORMAL_FONT)
        self.labelP4A.grid(row=10, column=2)          
        # create an entry for user to key in the index_2
        self.SV_index_2 = tk.StringVar()
        self.entry4B = tk.Entry(self.table_frame, width=5, textvariable=self.SV_index_2)
        #self.entry4B.grid(row=10, column=3)        
        



        #self.labelxMin = tk.Label(self.table_frame, text="x Min. Value:", width=20, font=NORMAL_FONT)
        #self.labelxMin.grid(row=11, column=1, pady=2, padx=2)
        #self.labelxMinA = tk.Label(self.table_frame, width=60, text=model.min_value, font=NORMAL_FONT)
        #self.labelxMinA.grid(row=11, column=2)      
 
        #global maxValue
        #  self.xmaxValue=tk.StringVar()
        #self.maxValue=tk.IntVar()
        #  self.entryP7 = tk.Entry(self.table_frame, width=10, textvariable=self.xmaxValue)
        #  self.entryP7.grid(row=11, column=3)  
        
        
        # create comboboxes
        #labelP3 = tk.Label(self, text="gene 1 (index 1):")
        #labelP3.grid(row=5, column=0, pady=2, padx=2)
        
        #self.controller.app_data["index_1"]=model.index_1
        #self.entryP3A = tk.Entry(self, width=5, textvariable=self.controller.app_data["index_1"])
        #self.entryP3A.grid(row=5, column=2)           

#        self.Combobox_Gene1 = ttk.Combobox(self.table_frame, values=model.geneName, width=15,textvariable=self.SV_index_1)
#        self.Combobox_Gene1.grid(row=9, column=3)   
#        self.Combobox_Gene1.current(model.index_1)
        #Combobox_Gene1.bind('<Return>', self._update_values)


        #labelP4 = tk.Label(self, text="gene 2 (index 2):")
        #labelP4.grid(row=6, column=0, pady=2, padx=2)
        
#        self.controller.app_data["index_2"]=model.index_2        
#        self.entryP4A = tk.Entry(self, width=5, textvariable=self.controller.app_data["index_2"])
#        self.entryP4A.grid(row=6, column=2)        

        
        
        self.SaveButton = ttk.Button(self.table_frame, text='Save Model Setting', width =25, command= self.save_model_setting)
        self.SaveButton.grid(row=11, column=3)    
        
        # to display the ode model equations
        label_ODE_model_Eqns = tk.Label(self, text='ODE Model Equations:', font="Verdana 10 bold", pady=2, padx=20)    
        label_ODE_model_Eqns.grid(row=13, column=0)
        
        #self.ode_Eqn_Text = tk.Text(self) 

        #self.ode_Eqn_Text.grid(row=14, column=0)
        #if model.type == 'ode':
        #    for i in range(len(GeneDydtList)):
        #        self.ode_Eqn_Text.insert(tk.INSERT, GeneDydtList[i])
            
        #    for j in range(len(AllParameters)):
        #        self.ode_Eqn_Text.insert(tk.INSERT, AllParameters[j]) 
                
        #if model.type == 'SBML':
        #    for i in range(len(sbml_AllParameters)):
        #        self.ode_Eqn_Text.insert(tk.INSERT, sbml_AllParameters[i])
        
        #self.ode_Eqn_Text.config(font="Verdana 10", state=tkSettingPage.DISABLED)
 
        # Adding a vertical scrollbar
        myframe=tk.Frame(self, bg='blue', width=1800, height=1000, bd=1)
        myframe.grid(row=14,column=0 )
                    
        self.mycanvas=tk.Canvas(myframe, bg='blue',width=1800, height=1000)
        self.myscrollbar = tk.Scrollbar(myframe,orient="vertical", command=self.mycanvas.yview)

        self.myscrollbar.pack(side="right",fill="y")
        
        self.myhorizontalscrollbar=tk.Scrollbar(myframe,orient="horizontal",command=self.mycanvas.xview)
        self.myhorizontalscrollbar.pack(side="bottom",fill="x")
        
        self.mycanvas.configure(yscrollcommand=self.myscrollbar.set,xscrollcommand=self.myhorizontalscrollbar.set)
        self.mycanvas.pack(side="top")                            

        #self.ode_Eqn_Text = tk.Text(self.mycanvas, height=1000, width=800,wrap=tk.NONE, yscrollcommand=self.myscrollbar.set, xscrollcommand=self.myhorizontalscrollbar.set)         
        #info_label.config(state=tk.DISABLED)
        #info_label.configure(text="You can load a model in ode file format. Using File --> Load ode model. The ode model file requires the ordinary differential equation and parameter values define by 'par' list. ")
                
        # end of from ModelSetting    
        
    
#    def refresh_model_setting(self):
#        '''this function may be redundant or not in use anymore. '''
#        print("refresh_model_setting was called.")
                
#        self.labelP1A.config(text=model.name)
#        self.labelModelTypeA.config(text=model.type)
#        self.labelP5A.config(text=model.min_value)
#        self.labelP6A.config(text=model.max_value)
#        self.labelP3A.config(text=model.index_1)
#        self.labelP4A.config(text=model.index_2)
        
#        seSettingPagelf.Combobox_Gene1 = ttk.Combobox(self.table_frame, values=model.geneName, width=25,textvariable=self.SV_index_1)
#        self.Combobox_Gene1.grid(row=11, column=3)   
#        self.Combobox_Gene1.current(model.index_1)
#        print(model.index_1)
        
#        self.Combobox_Gene2 = ttk.Combobox(self.table_frame, values=model.geneName, width=25,textvariable=self.SV_index_2)
#        self.Combobox_Gene2.grid(row=10, column=3) 
#        self.Combobox_Gene2.current(model.index_2)     
        
#       self.ode_Eqn_Text = tk.Text(self.mycanvas, width=650, height=400, wrap=tk.NONE, yscrollcommand=self.myscrollbar.set, xscrollcommand=self.myhorizontalscrollbar.set) 
        

#        self.ode_Eqn_Text.grid(row=14, column=0)        
#        if model.type == 'ode':
#            print(model.type)
#            for j in range(len(model.AllParameters)):
#                self.ode_Eqn_Text.insert(tk.INSERT, model.AllParameters[j]) 
#            self.ode_Eqn_Text.insert(tk.INSERT,'\n')
#            for i in range(len(model.GeneDydtList)):
#                self.ode_Eqn_Text.insert(tk.INSERT, model.GeneDydtList[i])


#        if model.type == 'SBML':
#            for i in range(len(model.sbml_compartments)):
#                self.ode_Eqn_Text.insert(tk.INSERT, model.sbml_compartments[i])
            # the 2 lines below were replaced by code that use updated parameter values
            #for i in range(len(sbml_AllParameters)):
            #    self.ode_Eqn_Text.insert(tk.INSERT, sbml_AllParameters[i])
           
            # To display constants as model information
#            for key in model.Constants:
#                self.ode_Eqn_Text.insert(tk.INSERT, key+'='+str(model.Constants[key]))

#            for j in range(len(model.AllParameters)):
#                self.ode_Eqn_Text.insert(tk.INSERT, model.AllParameters[j])
#            for i in range(len(sbml_reactions)):
#                self.ode_Eqn_Text.insert(tk.INSERT, sbml_reactions[i])
#                self.ode_Eqn_Text.insert(tk.INSERT, '\n')
#            for i in range(len(model.sbml_rhs)):
                #self.ode_Eqn_Text.insert(tk.INSERT, 'd'+variables_name[i]+'/dt=')
#                self.ode_Eqn_Text.insert(tk.INSERT, model.sbml_rhs[i])
        
#        self.ode_Eqn_Text.config(font="Verdana 10", state=tk.DISABLED)        
        
    
    def save_model_setting(self):
        #self.controller=controller
        print("save_model_setting was called.")
        
        self.maxValue.set(self.entryP6.get())
        self.minValue.set(self.entryP5.get())
        print("minValue.get():", self.minValue.get())        
        print("maxValue.get():", self.maxValue.get())
        # use built in function setter and gettattr: https://stackoverflow.com/questions/2627002/whats-the-pythonic-way-to-use-getters-and-setters
        # setattr(object, 'property_name', value)
        # getattr(object, 'property_name', default_value)  # default is optional
        # setattr(model,'max_value',10) ==>model.max_value=10
        # getattr(model,'index_2') ==>model.index_2=4
        if self.minValue.get()!='':
            setattr(model,'min_value',float(self.minValue.get()))
            self.labelP5A.config(text=model.min_value)  # update the label text     
        if self.maxValue.get() !='':
            setattr(model,'max_value',float(self.maxValue.get()))
            self.labelP6A.config(text=model.max_value) # update the label text

        #model.min_value = self.minValue.get()
        #model.max_value = self.maxValue.get()
        #model.index_1 =
        #model.index_2 = 
        #print(app.app_data["max_value"].get())
        self.SV_index_1.set(self.entry3B.get())
        if self.SV_index_1.get() !='':
            #setattr(model,'index_1',int(self.SV_index_1.get()))
            setattr(model,'index_1',int(model.geneName.index(self.SV_index_1.get()) ) )
            self.labelP3A.config(text=model.index_1) # update the label text 
        self.SV_index_2.set(self.entry4B.get())
        if self.SV_index_2.get() !='':
            #setattr(model,'index_2',int(self.SV_index_2.get())) 
            setattr(model,'index_2',int(model.geneName.index(self.SV_index_2.get()) ) )            
            self.labelP4A.config(text=model.index_2) # update the label text 
        print('model.min_value:', model.min_value)
        print('model.max_value:', model.max_value)
        print('model.index_1:',model.index_1)
        print('model.index_2:',model.index_2)

        # popup message to say the setting has been saved
        #tk.messagebox.showinfo("Saving Model settting", "The model setting you entered was saved.") 
        #model.index_1 = .get()
        #model.index_2 = .get() 
        #app.show_frame(SettingPage)    
        
        model.fromInitialCondition = np.ones((1,model.num_gene))*model.min_value
        model.toInitialCondition = np.ones((1,model.num_gene))*model.max_value
        
        model.y=np.zeros((1,model.num_gene), dtype = 'float')
        model.t=np.zeros((1,1))
        model.output=model.y

        model.outputT= np.hstack((model.t,model.y))
        
        model.TimecourseData=np.zeros((int((model.t_end-model.t_start)/model.h+1),model.num_gene))
        model.PositionProb = np.zeros((model.gridNumber,model.gridNumber))
        model.InitialConditions=np.zeros((model.TrajectoryNumber,model.num_gene))
               
        #'''This loop get all the random initial conditions in the state space'''  
        for j in range(model.num_gene):
            #print(j)
            model.InitialConditions[:,j][:,None]=np.random.random((model.TrajectoryNumber,1))*(model.toInitialCondition[0,j]-model.fromInitialCondition[0,j])+model.fromInitialCondition[0,j]
            #print(model.InitialConditions)
            
    def update_frame(self):
        
        print("update_frame was called for model setting page.")
        
        # Adding vertical scrollbar to Text widgets 
        def myfunction(event):
            self.mycanvas.configure(scrollregion=self.mycanvas.bbox("all"),width=570, height=320)         
            #self.mycanvas.configure(scrollregion=self.mycanvas.bbox("all"),width=645, height=390)   

        
        self.labelP1A.config(text=model.name)
        self.labelModelTypeA.config(text=model.type)       
        self.labelP5A.config(text=model.min_value)
        self.labelP6A.config(text=model.max_value)
        self.labelP3A.config(text=model.index_1)
        self.labelP4A.config(text=model.index_2)
        
        self.Combobox_Gene1 = ttk.Combobox(self.table_frame, values=model.geneName, width=25,textvariable=self.SV_index_1)
        self.Combobox_Gene1.grid(row=9, column=3)   
        self.Combobox_Gene1.current(model.index_1)
        print(model.index_1)
        
        self.Combobox_Gene2 = ttk.Combobox(self.table_frame, values=model.geneName, width=25,textvariable=self.SV_index_2)
        self.Combobox_Gene2.grid(row=10, column=3) 
        self.Combobox_Gene2.current(model.index_2)     
        
        #self.ode_Eqn_Text = tk.Text(self.mycanvas) 
        self.ode_Eqn_Text = tk.Text(self.mycanvas, wrap=tk.NONE, yscrollcommand=self.myscrollbar.set, xscrollcommand=self.myhorizontalscrollbar.set)         
        #self.ode_Eqn_Text.config(height=1000, width=800)         

        self.ode_Eqn_Text.grid(row=14, column=0)        
        #self.ode_Eqn_Text.grid(columnspan=1800, rowspan=800,row=14, column=0)
        #setting vertical scrollbar to Text Widget
        self.myscrollbar.config(command=self.ode_Eqn_Text.yview)
        self.myhorizontalscrollbar.config(command=self.ode_Eqn_Text.xview)
        self.mycanvas.create_window((1,0),window=self.ode_Eqn_Text,anchor='e')
        self.ode_Eqn_Text.bind("<Configure>", myfunction)         
        
        if model.type == 'ode':
            print(model.type)
            
            if len(model.AllParameters)>0:
                self.ode_Eqn_Text.insert(tk.INSERT,'\nparameters:\n')
                
            for j in range(len(model.AllParameters)):
                self.ode_Eqn_Text.insert(tk.INSERT, model.AllParameters[j]) 
            self.ode_Eqn_Text.insert(tk.INSERT,'\n')
            
            if len(model.const) > 0:
                self.ode_Eqn_Text.insert(tk.INSERT, '\n')
            for i in range(len(model.const)):
                print('model.const:',model.const[i])
                self.ode_Eqn_Text.insert(tk.INSERT, model.const[i])
            self.ode_Eqn_Text.insert(tk.INSERT,'\n')
            
            for i in range(len(model.GeneDydtList)):
                self.ode_Eqn_Text.insert(tk.INSERT, model.GeneDydtList[i])
            
    


        if model.type == 'SBML':
            for i in range(len(model.sbml_compartments)):
                self.ode_Eqn_Text.insert(tk.INSERT, model.sbml_compartments[i])

            # the 2 lines below were replaced by code that used updated parameter values
            #for i in range(len(sbml_AllParameters)):
            #    self.ode_Eqn_Text.insert(tk.INSERT, sbml_AllParameters[i])
            for j in range(len(model.AllParameters)):
                self.ode_Eqn_Text.insert(tk.INSERT, model.AllParameters[j])

            # To display constants as model information
            if len(model.Constants)>0:
                self.ode_Eqn_Text.insert(tk.INSERT,'\n')
                #self.ode_Eqn_Text.insert(tk.INSERT,'\nConstants\n')
            for key in model.Constants:
                self.ode_Eqn_Text.insert(tk.INSERT, key+'='+str(model.Constants[key]))
                self.ode_Eqn_Text.insert(tk.INSERT,'\n')
                
            for i in range(len(model.sbml_reactions)):
                self.ode_Eqn_Text.insert(tk.INSERT, model.sbml_reactions[i])
                self.ode_Eqn_Text.insert(tk.INSERT, '\n')
            for i in range(len(model.sbml_rhs)):
                #self.ode_Eqn_Text.insert(tk.INSERT, 'd'+variables_name[i]+'/dt=')
                self.ode_Eqn_Text.insert(tk.INSERT, model.sbml_rhs[i])
        
        self.ode_Eqn_Text.config(font="Verdana 10", state=tk.DISABLED)   
        self.update()
        
class MethodSettingPage(tk.Frame):
    '''This page show the Monte Carlo method's parameter setting so that user can change the parameter as needed'''

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Monte Carlo Method Parameter", font=LARGE_FONT)
        label.grid(row=0,column=2,pady=10,padx=10)
        
#        button1 = ttk.Button(self, text="Back to Main Window",
#        command=lambda: controller.show_frame(StartPage))
#        button1.grid(row=1,column=2)
                         
        label_Header2=tk.Label(self, text="Method Parameter",  font="Verdana 10 bold")
        label_Header2.grid(row=4, column=1, pady=2, padx=2)
        labelCurrentValues = tk.Label(self, text="Current Values:")
        labelCurrentValues.grid(row=4,column=2, pady=2, padx=2)
        labelNewValues = tk.Label(self, text="Set New Values:")
        labelNewValues.grid(row=4,column=3, pady=2, padx=2)        
        
        labelS1 = tk.Label(self, text="Time Step, h (default =0.1):", font=NORMAL_FONT)
        labelS1.grid(row=6,column=1,pady=2,padx=2) 
        
        # declare a tkinter string variable for h
        self.stepSize_h=tk.StringVar() 
        self.label_h = tk.Label(self, text=model.h)
        self.label_h.grid(row=6, column=2)
        

        self.entryStepSize = tk.Entry(self, width=10, textvariable=self.stepSize_h)
        self.entryStepSize.grid(row=6,column=3)
        
        labelS2= tk.Label(self, text= "Trajectory Number (default =10000):", font = NORMAL_FONT)
        labelS2.grid(row=7, column=1, pady=2, padx=2)
        self.labelTrajNumber=tk.Label(self, text=model.TrajectoryNumber)
        self.labelTrajNumber.grid(row=7, column=2)
        # declare a tkinter string variable for TrajectoryNumber
        self.TrajNumber=tk.StringVar()
        self.entryTrajNumber = tk.Entry(self, width=10, textvariable=self.TrajNumber)
        self.entryTrajNumber.grid(row=7, column=3)
        
        labelS3 = tk.Label(self, text="Time Duration (default =30):", font=NORMAL_FONT)
        labelS3.grid(row=8,column=1,pady=2,padx=2) 
        self.labelTimeEnd=tk.Label(self, text=model.t_end)
        self.labelTimeEnd.grid(row=8,column=2)
        # declare a tkinter string variable for t_end
        self.TimeEnd=tk.StringVar()       
        self.entryTimeEnd = tk.Entry(self, width=10, textvariable=self.TimeEnd)
        self.entryTimeEnd.grid(row=8,column=3)
        
              
        labelS4 = tk.Label(self, text="Grid Number (default =100):", font=NORMAL_FONT)
        labelS4.grid(row=9,column=1,pady=2,padx=2) 
        self.labelGridNumber = tk.Label(self, text=model.gridNumber)
        self.labelGridNumber.grid(row=9, column=2)
        # declare a tkinter string variable for gridNumber
        self.GridNumber=tk.StringVar()  
        self.entryGridNumber = tk.Entry(self, width=10, textvariable=self.GridNumber)
        self.entryGridNumber.grid(row=9,column=3)
 
        #labelS5 = tk.Label(self, text="Smooth surface size (default =3):", font=NORMAL_FONT)
        #labelS5.grid(row=10,column=1,pady=2,padx=2) 
        #self.labelSmoothSurfSize = tk.Label(self, text=model.SmoothSurfSize)
        #self.labelSmoothSurfSize.grid(row=10, column=2)
        # declare a tkinter string variable for SmoothSurfSize
        #self.SmoothSurfSize=tk.StringVar()  
        #self.entrySmoothSurfSize = tk.Entry(self, width=10, textvariable=self.SmoothSurfSize)
        #self.entrySmoothSurfSize.grid(row=10,column=3)               
        
        # User control buttons
        buttonPlot = ttk.Button(self, text="Save", command=self.save_method_setting)
        buttonPlot.grid(row=12,column=3)
        #buttonPlot.bind("<Button>", Save_method_setting(controller)) 
        
    def save_method_setting(self):
#        #self.controller=controller
        print("save_model_setting was called.")
        self.stepSize_h.set(self.entryStepSize.get())
        if self.stepSize_h.get() !='':
            setattr( model,'h', float(self.stepSize_h.get()) )
            self.label_h.config(text=model.h) # to update the label text for h
        
        self.TrajNumber.set(self.entryTrajNumber.get())
        if self.entryTrajNumber.get() != '':
            setattr( model, 'TrajectoryNumber', int(self.TrajNumber.get()) )
            self.labelTrajNumber.config(text=model.TrajectoryNumber)
            
            # re-initialise the size of these two matrices
            model.InitialConditions=np.zeros((model.TrajectoryNumber,model.num_gene))
            model.TempAttractors=np.zeros((model.TrajectoryNumber,model.num_gene))
            
            #'''This loop get all the random initial conditions in the state space'''  
            for j in range(model.num_gene):
                #print(j)
                model.InitialConditions[:,j][:,None]=np.random.random((model.TrajectoryNumber,1))*(model.toInitialCondition[0,j]-model.fromInitialCondition[0,j])+model.fromInitialCondition[0,j]
                #print(model.InitialConditions.shape)           

        
        self.TimeEnd.set(self.entryTimeEnd.get())
        if self.TimeEnd.get() !='':
            setattr( model, 't_end', float(self.TimeEnd.get()) )
            self.labelTimeEnd.config(text=model.t_end)
        
        self.GridNumber.set(self.entryGridNumber.get())
        if self.GridNumber.get() !='':
            setattr( model, 'gridNumber', int(self.GridNumber.get()) )
            self.labelGridNumber.config(text=model.gridNumber)
            print('model.gridNumber:',model.gridNumber)   
            print('model.PositionProb.shape:',model.PositionProb.shape)
            model.PositionProb = np.zeros((model.gridNumber,model.gridNumber))
            print('model.PositionProb.shape:',model.PositionProb.shape)
            
            
        self.GridNumber.set(self.entryGridNumber.get())
        if self.GridNumber.get() !='':
            setattr( model, 'gridNumber', int(self.GridNumber.get()) )
            self.labelGridNumber.config(text=model.gridNumber)
            print('model.gridNumber:',model.gridNumber)   
         
        # updating the SmoothSurfSize
        #self.SmoothSurfSize.set(self.entrySmoothSurfSize.get())
        #if self.SmoothSurfSize.get() !='':
        #    setattr( model, 'SmoothSurfSize', int(self.SmoothSurfSize.get()) )
        #    self.labelSmoothSurfSize.config(text=model.SmoothSurfSize)
        #    print('model.SmoothSurfSize:',model.SmoothSurfSize)           
        
#        model.min_value = self.controller.app_data["min_value"].get()
#        model.max_value = self.controller.app_data["max_value"].get()
#        model.index_1 = self.controller.app_data["index_1"].get()
#        model.index_2 = self.controller.app_data["index_2"].get()    

    def update_frame(self):
        self.update()    


class TimeCoursePage(tk.Frame):

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        
        label = tk.Label(self, text=("""Time-Course Simulation 
        using Random Initial Conditions"""), font=LARGE_FONT)
        label.pack(pady=2,padx=10)

#        button1 = ttk.Button(self, text="Back to Main Window",
#                            command=lambda: controller.show_frame(StartPage))
#        button1.pack(pady=2,padx=10, ipadx=5)
        
        canvas = FigureCanvasTkAgg(f2, self)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        #toolbar = NavigationToolbar2Tk(canvas, self)
        toolbar = NavigationToolbar2TkAgg(canvas, self)
        toolbar.update()
        toolbar.pack(side=tk.TOP, pady=2,padx=5, ipadx=5)
        canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        
        # User control buttons
      
        buttonPlot = ttk.Button(self, text="Plot Time Course")
        buttonPlot.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)
        buttonPlot.bind("<Button>", plot_time_course)
        

        
        
        #buttonDataViewer = ttk.Button(self, text="Data Viewer")
        #buttonDataViewer.pack(pady=2,padx=10, ipadx=5)   
        #buttonDataViewer.bind("<Button>", new_window)   
        
        buttonTimeCourseDataViewer = ttk.Button(self, text="Data Viewer",  command=lambda: controller.show_frame(TimeCourseDataViewer))
        buttonTimeCourseDataViewer.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)   
         

        button2 = ttk.Button(self, text="Clear Graph", command= lambda: clear_time_course_graph())
        button2.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)

        Info_label= tk.Label(self, text="Please click the 'Plot Time Course' button for more trajectories.")
        Info_label.pack(pady=5,padx=10, ipadx=5)  
        
#        legend_frame= tk.Frame(self, bg='yellow')
#        legend_frame.pack()
#        legend_label = tk.Label(legend_frame, text='legend', bg='yellow')
#        legend_label.pack()
        
#        self.status_bar_label = tk.Label(self, text="After loaded with an ode or a SBML model, start with plotting one trajectory.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
#        self.status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)
        
    def update_frame(self):
        self.update()
        

class Example(tk.Frame):
    def __init__(self, root):

        tk.Frame.__init__(self, root)
        self.canvas = tk.Canvas(root, borderwidth=0, background="#ffffff")
        self.frame = tk.Frame(self.canvas, background="#ffffff")
        self.vsb = tk.Scrollbar(root, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)

        self.vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.canvas.create_window((4,4), window=self.frame, anchor="nw", 
                                  tags="self.frame")

        self.frame.bind("<Configure>", self.onFrameConfigure)

        self.populate()

    def populate(self):
        '''Put in some fake data'''
        for row in range(100):
            tk.Label(self.frame, text="%s" % row, width=3, borderwidth="1", 
                     relief="solid").grid(row=row, column=0)
            t="this is the second column for row %s" %row
            tk.Label(self.frame, text=t).grid(row=row, column=1)

    def onFrameConfigure(self, event):
        '''Reset the scroll region to encompass the inner frame'''
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))


class InitConditionsPage2(tk.Frame):
    
    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        
        self.update_n = 1
        
        self.canvas=tk.Canvas(self, borderwidth=0, bg='lavender', width=50, height=100)# background='#ffffff')
        
        self.frame = tk.Frame(self.canvas, bg='lavender', width=50, height=100)
        self.vsb = tk.Scrollbar(self, orient='vertical',command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        
        self.vsb.pack(side='right',fill='y')
        self.canvas.pack(side='left',fill='both',expand=True)
        self.canvas.create_window((4,4), window=self.frame,anchor='nw',tags='self.frame')
        self.frame.bind("<Configure>",self.onFrameConfigure)
        
        # start of labeling the interface
        
        labelPage = tk.Label(self.frame, text="Initial Conditions Setting", font=LARGE_FONT)
        labelPage.grid(row=0, column=0, pady=10, padx=10)
        
#        button1 =ttk.Button(self.frame, text="Back to Main Window",
#                                 command=lambda: controller.show_frame(StartPage))
#        button1.grid(row=1, column=0, pady=10,padx=10, ipadx=5)
        #button1.pack(pady=2,padx=10, ipadx=5)

        # Back to
        BackToTimeCourse2Init=ttk.Button(self.frame, text="Back to 'Time Course 2 Init'", width=25, 
                                              command=lambda: controller.show_frame(InitTimeCoursePage2) )
        BackToTimeCourse2Init.grid(row=1, column=0)
        
        BackToPhasePlane2Init = ttk.Button(self.frame, text="Back to 'Phase Plane 2 Init'", width=25,
                                           command=lambda:controller.show_frame(PhasePlane_Page2) )
        BackToPhasePlane2Init.grid(row=2, column=0)

        labelheader= tk.Label(self.frame, text="You can set the Initial Conditions")
        labelheader.grid(row=3, column=0,pady=10,padx=10)        

        self.initialValue=dict()
        self.entryInit=dict()
        
        self.is_checkedValue=dict()
        self.CheckButton=dict()
        
        self.labelGeneName=dict()
        self.LabelCurrent=dict()
        
        self.myframeNumber=dict()

        # to create a dictionary for the number of frame for each variable
        self.initConds_frameNumber=dict()          
        
        # Save Button 
        self.SaveButton=ttk.Button(self.frame,text="Save Initial Conditions", width=22,command=self.save_initial_conditions)
        self.SaveButton.grid(row=5, column=1)
        

        
#        self.PlotButton=ttk.Button(self,text="Plot Time Course")
#        self.PlotButton.pack(pady=2,padx=2, ipadx=5)
        
#        self.PlotButton.bind("<Button>", initConds_plot_time_course)
        
#        self.DataViewerButton=ttk.Button(self,text="Data Viewer",  command=lambda: controller.show_frame(initTimeCourseDataViewer))
#        self.DataViewerButton.pack(pady=2,padx=2, ipadx=5)
        
        # plotting of the time course graph
#        canvas = FigureCanvasTkAgg(f10,self)
#        canvas.show()
#        canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True) 
        
#        toolbar = NavigationToolbar2TkAgg(canvas,self)
#        toolbar.update()
#        toolbar.pack(side=tk.TOP)
#        canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)        
    
        # to turn geometry propagation on or off
        self.frame.pack_propagate(0)
    
    def save_initial_conditions(self):
        print("save_initial_conditions was called")       
        
        # for model.type=ode
        if model.type=='ode':
            for i in range(model.num_gene):
                print("init value:",self.entryInit['r'+str(i)].get())
                print("self.initialValue.get():",self.initialValue['r'+str(i)].get())  


                self.initialValue['r'+str(i)].set(self.entryInit['r'+str(i)].get())
                if self.initialValue['r'+str(i)].get() !='':
                    # update the user input initial value
                    model.ode_initConds[model.geneName[i]]=float(self.entryInit['r'+str(i)].get())
                
                    print('y[0,'+str(i)+']',model.y[0,i])
                    model.y[0,i]=float(self.initialValue['r'+str(i)].get())
                    setattr(model,'y[0,'+str(i)+']', float(self.initialValue['r'+str(i)].get()))
                    print('y[0,'+str(i)+']',model.y[0,i])
                    self.LabelCurrent['l'+str(i)].config(text=float(self.initialValue['r'+str(i)].get()))
                    #self.LabelCurrent['l'+str(i)].config(text=model.y[0,i])
                
                # update the initial value when user did not key in any initial value
                if self.initialValue['r'+str(i)].get() =='':
                    # update the user input initial value
                    model.ode_initConds[model.geneName[i]]=model.y[0,i]
                
                    print('y[0,'+str(i)+']',model.y[0,i])
                    #model.y[0,i]=float(self.initialValue['r'+str(i)].get())
                    #setattr(model,'y[0,'+str(i)+']', float(self.initialValue['r'+str(i)].get()))
                    #print('y[0,'+str(i)+']',model.y[0,i])
                    #self.LabelCurrent['l'+str(i)].config(text=float(self.initialValue['r'+str(i)].get()))                
                
            #print(self.vars[0])
            print(model.y)
            
        # for model.type=SBML
        if model.type=='SBML':        
            for i in range(model.num_gene):
                print("init value:",self.entryInit['r'+str(i)].get())
                print("self.initialValue.get():",self.initialValue['r'+str(i)].get())  
    
    
                self.initialValue['r'+str(i)].set(self.entryInit['r'+str(i)].get())
                if self.initialValue['r'+str(i)].get() !='':
                    # update the user input initial value
                    model.sbml_initConds[model.geneName[i]]=float(self.entryInit['r'+str(i)].get())
                    
                    print('y[0,'+str(i)+']',model.y[0,i])
                    model.y[0,i]=float(self.initialValue['r'+str(i)].get())
                    setattr(model,'y[0,'+str(i)+']', float(self.initialValue['r'+str(i)].get()))
                    print('y[0,'+str(i)+']',model.y[0,i])
                    self.LabelCurrent['l'+str(i)].config(text=float(self.initialValue['r'+str(i)].get()))
                    #self.LabelCurrent['l'+str(i)].config(text=model.y[0,i])

                # update the initial value when user did not key in any initial value
                if self.initialValue['r'+str(i)].get() =='':
                    # update the user input initial value
                    model.sbml_initConds[model.geneName[i]]=model.y[0,i]
                
                    print('y[0,'+str(i)+']',model.y[0,i])

                #print(self.vars[0])
                print(model.y)        
        
    def onFrameConfigure(self, event):
        '''Reset the scroll region to encompass the inner frame'''
        self.canvas.configure(scrollregion=self.canvas.bbox('all'))
 
    def update_frame(self):
        print('update_frame was called in Initial Conditions page')   
        self.update_n=self.update_n + 1
        print("self.update_n=", self.update_n)        

        # to destroy the previous frame
        # for checking how many frame and the frame number(FN)
        # print(self.myframeNumber) 
        if self.update_n > 2:
            self.myframeNumber['FN'+str(self.update_n-1)].destroy()  

        # create a new frame
        self.myframeNumber['FN'+str(self.update_n)]=tk.Frame(self.frame, bg='lavender', width=400, height=400, bd=1)
        self.myframeNumber['FN'+str(self.update_n)].grid()

        # Labeling of current and new value 
        tk.Label(self.myframeNumber['FN'+str(self.update_n)],text="Current Value:", font=NORMAL_FONT).grid(row=3,column=2,pady=2,padx=2)
        tk.Label(self.myframeNumber['FN'+str(self.update_n)],text="New Value:", font=NORMAL_FONT).grid(row=3,column=3,pady=2,padx=2)
#        tk.Label(self.myframeNumber['FN'+str(self.update_n)],text="Choose Protein to plot:", font=NORMAL_FONT).grid(row=3,column=4,pady=2,padx=2)
       
        # for model.type=ode
        if model.type=='ode':
            # for ode init Conds from ode model loaded  
            print(model.ode_initConds)
            print(model.y)
            if len(model.ode_initConds) !=0:
                for i in range(model.num_gene):
                    print(model.geneName[i])
                    print(model.ode_initConds[model.geneName[i]])
                    model.y[0,i]=model.ode_initConds[model.geneName[i]]
               
                

        # for model.type=SBML
        if model.type=='SBML':
            # for sbml init Conds from SBML model loaded
            if len(model.sbml_initConds) !=0:
                for i in range(model.num_gene):
                    model.y[0,i]=model.sbml_initConds[model.geneName[i]]
   

        for i in range(model.num_gene):
            self.initialValue['r'+str(i)]=tk.StringVar()
            #self.vars.append(self.initialValue)
            
            # To associate the Checkbox with a variable
            self.is_checkedValue['CV'+str(i)]=tk.IntVar()

            self.labelGeneName['GN'+str(i)]=tk.Label(self.myframeNumber['FN'+str(self.update_n)],text=model.geneName[i], width=20, font=NORMAL_FONT)
            self.labelGeneName['GN'+str(i)].grid(row=i+4,column=1,pady=2,padx=2)
            self.LabelCurrent['l'+str(i)]=tk.Label(self.myframeNumber['FN'+str(self.update_n)],text=round(model.y[0,i],4), width=20,font=NORMAL_FONT)
            self.LabelCurrent['l'+str(i)].grid(row=i+4,column=2,pady=2,padx=2)
            self.entryInit['r'+str(i)]=tk.Entry(self.myframeNumber['FN'+str(self.update_n)],width=20,textvariable=self.initialValue['r'+str(i)])
            self.entryInit['r'+str(i)].grid(row=i+4,column=3,pady=2,padx=2)
            
            print('model.y:',model.y)
#            self.CheckButton['RB'+str(i)]=tk.Checkbutton(self.myframeNumber['FN'+str(self.update_n)], variable=self.is_checkedValue['CV'+str(i)], onvalue = True, offvalue = False)
#            self.CheckButton['RB'+str(i)].grid(row=i+4,column=4)
            #self.labelGeneName['GN'+str(i)]=tk.Label(self.frame,text=model.geneName[i], font=NORMAL_FONT)
            #self.labelGeneName['GN'+str(i)].grid(row=i+4,column=1,pady=2,padx=2)
         


class InitTimeCoursePage(tk.Frame):

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Time course simulation from user key in initial conditions", font=LARGE_FONT)
        label.pack(pady=10,padx=10)

        button1 = ttk.Button(self, text="Back to Home",
                            command=lambda: controller.show_frame(StartPage))
        button1.pack(pady=2,padx=10, ipadx=5)

        self.table_frame= tk.Frame(self, bg='lavender', width=900, height=600)
        self.table_frame.pack(pady=10,padx=10) 


        self.canvas=tk.Canvas(self, borderwidth=0, bg='lavender', width=50, height=100)# background='#ffffff')
        
        self.frame = tk.Frame(self.canvas, bg='lavender', width=50, height=100)
#        self.vsb = tk.Scrollbar(self, orient='vertical',command=self.canvas.yview)
#        self.canvas.configure(yscrollcommand=self.vsb.set)

#        self.vsb.pack(side='right',fill='y')
        self.canvas.pack(side='left',expand=True)
 
        self.SelectedGene=tk.StringVar()
        self.SelectedColor=tk.StringVar()

        Label_ChooseProtein=tk.Label(self.canvas,text="Choose Protein to add to the plot:", font=NORMAL_FONT)
        Label_ChooseProtein.pack(pady=5,padx=10, ipadx=5)
        
        label_GeneName=tk.Label(self.canvas, text='Protein name:')
        label_GeneName.pack(pady=5, padx=10, ipadx=5)
        

#        self.vsb.pack(side='right',fill='y')

        
        canvas = FigureCanvasTkAgg(f7, self)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        #toolbar = NavigationToolbar2Tk(canvas, self)
        toolbar = NavigationToolbar2TkAgg(canvas, self)
        toolbar.update()
        toolbar.pack(side=tk.TOP,pady=2,padx=5, ipadx=5)
        canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        


        
        
        # User control buttons
        #Info_label= tk.Label(self, text="Please click the Plot time course button for more trajectories.")
        #Info_label.pack(pady=2,padx=10, ipadx=5)        
#        buttonPlot = ttk.Button(self, text="Plot time course")
#        buttonPlot.pack(pady=2,padx=10, ipadx=5)
#        buttonPlot.bind("<Button>", plot_time_course)
        
        buttonPlot = ttk.Button(self, text="Plot time course", command= self.add_plot_time_course)
        buttonPlot.pack(pady=5,padx=10, ipadx=5)           

        
        
        #buttonDataViewer = ttk.Button(self, text="Data Viewer")
        #buttonDataViewer.pack(pady=2,padx=10, ipadx=5)   
        #buttonDataViewer.bind("<Button>", new_window)   

        buttonTimeCourseDataViewer = ttk.Button(self, text="Data Viewer",  command=lambda: controller.show_frame(initTimeCourseDataViewer))
        buttonTimeCourseDataViewer.pack(pady=2,padx=10, ipadx=5)   
         

        button2 = ttk.Button(self, text="Clear graph", command= lambda: init_clear_time_course_graph())
        button2.pack(pady=2,padx=10, ipadx=5)
        
#        legend_frame= tk.Frame(self, bg='yellow')
#        legend_frame.pack()
#        legend_label = tk.Label(legend_frame, text='legend', bg='yellow')
#        legend_label.pack()
        
#        self.status_bar_label = tk.Label(self, text="After loaded with an ode or a SBML model, start with plotting one trajectory.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
#        self.status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)
        
    def add_plot_time_course(self):
        '''Add more plots to time course '''
        print("add_plot_time_course was called")
        
        #self.status_bar_label.config(text="plot_time_course was called.")
        #print('model.name:',model.name)
        #print(dir())
        
        if model.name=='':
            tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
            
        if model.type == 'ode':
            
            #n, self.outputT=model.calculate_timeCourse() 
            n, time, self.outputT = simulate_time_course(self)
            a7 = f7.add_subplot(111)
            # for Data Viewer
            global DataOutputT
            #print(time1.shape)
            #print(result1.shape)
            time1_row_column = np.array([time])
            time1_r_c_T =time1_row_column.T
            #print(time1_row_column.shape)
            DataOutputT=np.concatenate((time1_r_c_T,self.outputT), axis=1)
            model.DataOutputT=DataOutputT
            #DataOutputT = self.outputT
            
        
            #for i in range(2):
            #    print(i)
            #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
            #    print(eachInitCond)
            #    self.y=eachInitCond
            
            # Get one trajectory time-course data
            #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
            #    print(output)        
            #a2.plot(self.outputT[:,0], self.outputT[:,model.index_1+1], color= 'g', linewidth=0.5) #, hold=True)
            #a2.plot(self.outputT[:,0], self.outputT[:,model.index_2+1], color= 'b', linewidth=0.5) # , hold=True)
            a7.plot(time, self.outputT[:,model.index_1], color=self.SelectedColor.get() , linewidth=0.5) #, hold=True)

    
            a7.set_xlabel('time')
            a7.set_ylabel('protein levels')
            #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
            #print('model.index_2', model.index_2)
            a7.legend([str(model.geneName[int(model.geneName.index(self.SelectedGene.get()))])], loc=1) 
            # legend option loc =1 means place the location of the legend in the upper right
            # refers to this url for other options
            # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
        
            #a2.title('n')
            print('n=', n)
    
            f7.canvas.draw_idle()   
        
        if model.type == 'SBML':
            n, time, self.outputT = sbml_simulate_time_course(self)    
            a2 = f2.add_subplot(111)
            # for Data Viewer
            global sbml_DataOutputT
            #print(time1.shape)
            #print(result1.shape)
            time1_row_column = np.array([time])
            time1_r_c_T =time1_row_column.T
            #print(time1_row_column.shape)
            sbml_DataOutputT=np.concatenate((time1_r_c_T,self.outputT), axis=1)
            model.DataOutputT=sbml_DataOutputT
            #DataOutputT = self.outputT
            
        
            #for i in range(2):
            #    print(i)
            #    eachInitCond=self.InitialConditions[i,:][:,None].T  # to ensure the same dimension of the matrix
            #    print(eachInitCond)
            #    self.y=eachInitCond
            
            # Get one trajectory time-course data
            #    self.outputT=RungeKutta4thInt(Model.Funct,self.t,self.t_end,self.h,self.y,self.outputT)  
            #    print(output)        
            #a2.plot(self.outputT[:,0], self.outputT[:,model.index_1+1], color= 'g', linewidth=0.5) #, hold=True)
            #a2.plot(self.outputT[:,0], self.outputT[:,model.index_2+1], color= 'b', linewidth=0.5) # , hold=True)
            a2.plot(time, self.outputT[:,model.index_1], color= 'g', linewidth=0.5) #, hold=True)
            a2.plot(time, self.outputT[:,model.index_2], color= 'b', linewidth=0.5) # , hold=True)
    
            a2.set_xlabel('time')
            a2.set_ylabel('protein levels')
            #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
            #print('model.index_2', model.index_2)
            a2.legend([str(model.geneName[model.index_1]),str(model.geneName[model.index_2])], loc=1) 
            # legend option loc =1 means place the location of the legend in the upper right
            # refers to this url for other options
            # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
        
            #a2.title('n')
            print('n=', n)
    
            f2.canvas.draw_idle()        
        
        
    def update_frame(self):      
        self.Combobox_Gene2 = ttk.Combobox(self.table_frame, values=model.geneName, width=15, textvariable=self.SelectedGene)
        self.Combobox_Gene2.pack(pady=5,padx=10, ipadx=5,fill='both',expand=True) 
        self.Combobox_Gene2.current(model.index_1)   # set selection         
        

        label_Color=tk.Label(self.table_frame, text='Color:')
        label_Color.pack(pady=5, padx=10, ipadx=5)
        
        colorList=['black', 'red', 'gray', 'blue', 'green', 'limegreen', 'blueviolet', 'deeppink', 'olive', 'magenta', 'brown']
        
        self.Combobox_Color = ttk.Combobox(self.table_frame, values=colorList , width=15, textvariable=self.SelectedColor)
        self.Combobox_Color.pack(pady=5, padx=10, ipadx=5, fill='both', expand=True)
        self.Combobox_Color.current(model.index_1)



        self.update()


class InitTimeCoursePage2(tk.Frame):
    '''This is initial Time course page for the normal simulator time course page '''
    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Time course simulation from user key in initial conditions", font=LARGE_FONT)
        label.grid(row=0,column=2,pady=2,padx=10)

#        button1 = ttk.Button(self, text="Back to Home",
#                            command=lambda: controller.show_frame(StartPage))
#        button1.grid(row=1,column=2,pady=2,padx=10, ipadx=5)

        self.table_frame= tk.Frame(self, bg='lavender', width=900, height=400)
        self.table_frame.grid(row=3,column=2,pady=2,padx=10) 

#        self.canvas=tk.Canvas(self, borderwidth=0, bg='yellow', width=50, height=100)# background='#ffffff')
        
#        self.frame = tk.Frame(self.canvas, bg='lavender', width=100, height=100)
#        self.frame.pack()
#        self.vsb = tk.Scrollbar(self, orient='vertical',command=self.canvas.yview)
#        self.canvas.configure(yscrollcommand=self.vsb.set)

#        self.vsb.pack(side='right',fill='y')
#        self.canvas.grid()
 
        self.SelectedGene=tk.StringVar()
        self.SelectedColor=tk.StringVar()
        self.SelectedLineStyle=tk.StringVar()
        self.SelectedLineSize=tk.StringVar()

        Label_ChooseProtein=tk.Label(self.table_frame,text="Choose Protein to add to the plot:", font=NORMAL_FONT)
        Label_ChooseProtein.grid(row=5,column=2,pady=2,padx=2, ipadx=5)
        
        label_GeneName=tk.Label(self.table_frame, text='Protein Name:')
        label_GeneName.grid(row=6,column=1,pady=2,padx=2, ipadx=5)
        
        label_Color=tk.Label(self.table_frame, text='Color:')
        label_Color.grid(row=7,column=1,pady=2,padx=2, ipadx=5)
#        self.vsb.pack(side='right',fill='y')

        label_LineStyle=tk.Label(self.table_frame, text='Line-style:')
        label_LineStyle.grid(row=7, column=3, pady=2,padx=3, ipadx=5)
        
        label_LineSize=tk.Label(self.table_frame, text='Line width:')
        label_LineSize.grid(row=7, column=5, pady=2,padx=3, ipadx=5)
        

        self.f=f8 #Figure(figsize=(4.5,4.5), dpi=100)
        self.a=self.f.add_subplot(111)
        self.canvas = FigureCanvasTkAgg(self.f, master=self)
        self.canvas.draw()
        self.canvas.get_tk_widget().grid(row=12, column=1, rowspan=10, columnspan=6, pady=(10,10), padx=(25,25), sticky=tk.N+tk.S+tk.E+tk.W)
        self.canvas._tkcanvas.grid()

        
        buttonPlot = ttk.Button(self.table_frame, text="Add and Plot time course", 
                                command= self.add_plot_time_course)
        buttonPlot.grid(row=6,column=7,pady=5,padx=10, ipadx=5)                  
        
        buttonReset = ttk.Button(self.table_frame, text="Reset", command = self.reset)
        buttonReset.grid(row=6, column=8, pady=5, padx=10, ipadx=5)
        #buttonDataViewer = ttk.Button(self, text="Data Viewer")
        #buttonDataViewer.pack(pady=2,padx=10, ipadx=5)   
        #buttonDataViewer.bind("<Button>", new_window)   

        buttonInitSetting = ttk.Button(self.table_frame, text="Setting Initial Conds", 
                                       command=lambda: controller.show_frame(InitConditionsPage2) )
        buttonInitSetting.grid(row=7,column=7,pady=2,padx=10, ipadx=5)

        buttonTimeCourseDataViewer = ttk.Button(self.table_frame, text="Data Viewer 2",  
                                                command=lambda: controller.show_frame(initTimeCourseDataViewer))
        buttonTimeCourseDataViewer.grid(row=8,column=7,pady=2,padx=10, ipadx=5)   
         

        button2 = ttk.Button(self.table_frame, text="Clear graph", command= self.init_clear_time_course_graph)
        button2.grid(row=7,column=8,pady=2,padx=10, ipadx=5)
        
        # x Label and y Label
        Label_ChooseProtein=tk.Label(self.table_frame,text="Change the x label and y label:", font=NORMAL_FONT)
        Label_ChooseProtein.grid(row=8,column=2,pady=2,padx=2, ipadx=5)
        
        label_xlabel = tk.Label(self.table_frame, text='x label:')
        label_xlabel.grid(row=9, column=1, pady=2, padx=3, ipadx=5)
                          
        label_ylabel = tk.Label(self.table_frame, text='y label:')
        label_ylabel.grid(row=9, column=3, pady=2, padx=3, ipadx=5)

        # declare a tkinter string variable for xlabel
        self.XlabelVar=tk.StringVar()       
        self.entryXlabel = tk.Entry(self.table_frame, width=30, textvariable=self.XlabelVar)
        self.entryXlabel.grid(row=9,column=2)        
        
        self.YlabelVar=tk.StringVar()       
        self.entryYlabel = tk.Entry(self.table_frame, width=30, textvariable=self.YlabelVar)
        self.entryYlabel.grid(row=9,column=4)           
        
        mytoolbar_frame=tk.Frame(self, width=10, height=400, bd=1)
        mytoolbar_frame.grid(row=25, column=2)
        
        #self.mycanvas=FigureCanvasTkAgg(self.f,mytoolbar_frame)
        #self.toolbar=NavigationToolbar2Tk(self.canvas,mytoolbar_frame)
        self.toolbar=NavigationToolbar2TkAgg(self.canvas,mytoolbar_frame)
        self.toolbar.update()

        self.toolbar.pack(side=tk.LEFT,fill=tk.X)
        
        # User control buttons
        buttonPlot = ttk.Button(self.table_frame, text="Save Labels", command=self.save_label_setting)
        buttonPlot.grid(row=9,column=5)

        
    def save_label_setting(self):
#        #self.controller=controller
        print("save_label_setting was called.")
        self.XlabelVar.set(self.entryXlabel.get())
        if self.entryXlabel.get() !='':
            setattr( model,'XLabel', str(self.entryXlabel.get()) )
            #self.label_h.config(text=model.h) # to update the label text for h     
            print('model.XLabel:',model.XLabel)

        self.YlabelVar.set(self.entryYlabel.get())
        if self.entryYlabel.get() !='':
            setattr( model,'YLabel', str(self.entryYlabel.get()) )
            #self.label_h.config(text=model.h) # to update the label text for h     
            print('model.YLabel:',model.YLabel)     
            
        self.a.set_xlabel(model.XLabel)
        self.a.set_ylabel(model.YLabel)        
#        legend_frame= tk.Frame(self, bg='yellow')
#        legend_frame.pack()
#        legend_label = tk.Label(legend_frame, text='legend', bg='yellow')
#        legend_label.pack()
        
#        self.status_bar_label = tk.Label(self, text="After loaded with an ode or a SBML model, start with plotting one trajectory.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
#        self.status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)
        
    def add_plot_time_course(self):
        '''Add more plots to time course '''
        print("add_plot_time_course was called")
        
        #self.status_bar_label.config(text="plot_time_course was called.")
        #print('model.name:',model.name)
        #print(dir())
        
        if model.name=='':
            tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
            
        if model.type == 'ode':
            
            if model.geneName.index(self.SelectedGene.get()) not in model.timeCourseToPlot:
                model.timeCourseToPlot.append(model.geneName.index(self.SelectedGene.get()))
                model.timeCourseToPlotColor.append(self.SelectedColor.get())
                model.lineStyle.append(self.SelectedLineStyle.get())
                model.lineSize.append(self.SelectedLineSize.get())
            print('model.timeCourseToPlot:', model.timeCourseToPlot)
            print('model.timeCourseToPlotColor:', model.timeCourseToPlotColor)
            #n, self.outputT=model.calculate_timeCourse() 
            #n, self.outputT=model.calculate_timeCourse() 
            time, self.initOutputT = initConds_simulate_time_course(self)

            #f7.clear()

            #a7 = f7.add_subplot(111)
            self.f.clear()         
            self.a=self.f.add_subplot(111)   
            # for Data Viewer
            global initDataOutputT
            #print(time1.shape)
            #print(result1.shape)
            time1_row_column = np.array([time])
            time1_r_c_T =time1_row_column.T
            #print(time1_row_column.shape)
            initDataOutputT=np.concatenate((time1_r_c_T,self.initOutputT), axis=1)
            model.initDataOutputT=initDataOutputT
            #DataOutputT = self.outputT
        
            print('len(model.timeCourseToPlot):',len(model.timeCourseToPlot))
            for i in range(len(model.timeCourseToPlot)):
                print('i: ',i)
                self.a.plot(time,model.initDataOutputT[:,model.timeCourseToPlot[i]+1], color=model.timeCourseToPlotColor[i], linestyle=model.lineStyle[i], linewidth=float(model.lineSize[i]))
            #a7.plot(time, self.initOutputT[:,i], color= 'r', linewidth=0.5) #, hold=True)  
            #a7.plot(time, model.initDataOutputT[:,model.geneName.index(self.SelectedGene.get())+1], color=self.SelectedColor.get() , linewidth=0.5, label=self.SelectedGene.get()) #, hold=True)
            #print(model.geneName.index(self.SelectedGene.get()))
            #print(time)
            #print(model.initDataOutputT[:,model.geneName.index(self.SelectedGene.get())+1])
    
            self.a.set_xlabel(model.XLabel)
            self.a.set_ylabel(model.YLabel)
            #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
            #print('model.index_2', model.index_2)
            legendProteinName=[]
            for j in range(len(model.timeCourseToPlot)):
                print('j:',j)
                legendProteinName.append(model.geneName[model.timeCourseToPlot[j]])
 
            self.a.legend(legendProteinName, loc=1)
 
            print('legendProteinName:',legendProteinName)
            
            #a7.legend([str(model.geneName[int(model.geneName.index(self.SelectedGene.get()))])], loc=1) 
            # legend option loc =1 means place the location of the legend in the upper right
            # refers to this url for other options
            # https://matplotlib.org/api/pyplot_api.html#matplotlib.pyplot.legend
        

            self.f.canvas.draw_idle()   
        
        if model.type == 'SBML':
            #n, time, self.outputT = sbml_simulate_time_course(self)    
            if model.geneName.index(self.SelectedGene.get()) not in model.timeCourseToPlot:
                model.timeCourseToPlot.append(model.geneName.index(self.SelectedGene.get()))
                model.timeCourseToPlotColor.append(self.SelectedColor.get())
                model.lineStyle.append(self.SelectedLineStyle.get())
                model.lineSize.append(self.SelectedLineSize.get())
            print('model.timeCourseToPlot:', model.timeCourseToPlot)
            print('model.timeCourseToPlotColor:', model.timeCourseToPlotColor)
            #n, self.outputT=model.calculate_timeCourse() 
            #n, self.outputT=model.calculate_timeCourse() 
            time, self.initOutputT = initConds_sbml_simulate_time_course(self)

            #f7.clear()

            #a7 = f7.add_subplot(111)
            self.f.clear()         
            self.a=self.f.add_subplot(111)   
            # for Data Viewer
            #global initDataOutputT
            #print(time1.shape)
            #print(result1.shape)
            time1_row_column = np.array([time])
            time1_r_c_T =time1_row_column.T
            #print(time1_row_column.shape)
            initDataOutputT=np.concatenate((time1_r_c_T,self.initOutputT), axis=1)
            model.initDataOutputT=initDataOutputT
            #DataOutputT = self.outputT
        
            print('len(model.timeCourseToPlot):',len(model.timeCourseToPlot))
            for i in range(len(model.timeCourseToPlot)):
                print('i: ',i)
                self.a.plot(time,model.initDataOutputT[:,model.timeCourseToPlot[i]+1], color=model.timeCourseToPlotColor[i], linestyle=model.lineStyle[i], linewidth=float(model.lineSize[i]))
            #a7.plot(time, self.initOutputT[:,i], color= 'r', linewidth=0.5) #, hold=True)  
            #a7.plot(time, model.initDataOutputT[:,model.geneName.index(self.SelectedGene.get())+1], color=self.SelectedColor.get() , linewidth=0.5, label=self.SelectedGene.get()) #, hold=True)
            #print(model.geneName.index(self.SelectedGene.get()))
            #print(time)
            #print(model.initDataOutputT[:,model.geneName.index(self.SelectedGene.get())+1])
    
            self.a.set_xlabel(model.XLabel)
            self.a.set_ylabel(model.YLabel)
            #a2.legend([str(model.geneName[model.index_1]),'Zeb'])
            #print('model.index_2', model.index_2)
            legendProteinName=[]
            for j in range(len(model.timeCourseToPlot)):
                print('j:',j)
                legendProteinName.append(model.geneName[model.timeCourseToPlot[j]])
 
            self.a.legend(legendProteinName, loc=1)
            
    
            self.f.canvas.draw_idle()        

    def reset(self):
        model.timeCourseToPlot=[]
        model.timeCourseToPlotColor=[]
        model.lineStyle=[]
        model.lineSize=[]       
        self.f.clear()
        self.f.add_subplot(111)
        self.f.canvas.draw_idle()        

    def init_clear_time_course_graph(self):
        self.f.clear()
        self.f.add_subplot(111)
        self.f.canvas.draw_idle()
        
    def update_frame(self):      
        self.Combobox_Gene2 = ttk.Combobox(self.table_frame, values=model.geneName, width=15, textvariable=self.SelectedGene)
        self.Combobox_Gene2.grid(row=6,column=2,pady=2,padx=2, ipadx=5) 
        self.Combobox_Gene2.current(model.index_1)   # set selection         
        


        
        colorList=['black', 'blue', 'blueviolet', 'brown', 'cyan', 'darkorange', 'deeppink', 'gold', 'green', 'grey', 'lightblue', 'limegreen', 'magenta', 'olive', 'pink', 'plum', 'red', 'skyblue', 'steelblue', 'yellow']
        lineStyle=['-', '--', '-.',':']
        lineSize=[0.5, 1, 1.5, 2, 2.5, 3, 3.5, 4]
        
        self.Combobox_Color = ttk.Combobox(self.table_frame, values=colorList, width=15, textvariable=self.SelectedColor)
        self.Combobox_Color.grid(row=7,column=2,pady=2,padx=2, ipadx=5)
        self.Combobox_Color.current(0)

        self.Combobox_LineStyle = ttk.Combobox(self.table_frame, values=lineStyle, width=15, textvariable=self.SelectedLineStyle)
        self.Combobox_LineStyle.grid(row=7, column=4, pady=2,padx=5, ipadx=5)
        self.Combobox_LineStyle.current(0)
        
        self.Combobox_LineSize = ttk.Combobox(self.table_frame, values=lineSize, width=15, textvariable=self.SelectedLineSize)
        self.Combobox_LineSize.grid(row=7, column=6, pady=2,padx=5, ipadx=5)
        self.Combobox_LineSize.current(0)
        


        self.update()

class Example(tk.Frame):
    def __init__(self, root):

        tk.Frame.__init__(self, root)
        self.canvas = tk.Canvas(root, borderwidth=0, background="#ffffff")
        self.frame = tk.Frame(self.canvas, background="#ffffff")
        self.vsb = tk.Scrollbar(root, orient="vertical", command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)

        self.vsb.pack(side="right", fill="y")
        self.canvas.pack(side="left", fill="both", expand=True)
        self.canvas.create_window((4,4), window=self.frame, anchor="nw", 
                                  tags="self.frame")

        self.frame.bind("<Configure>", self.onFrameConfigure)

        self.populate()

    def populate(self):
        '''Put in some fake data'''
        for row in range(100):
            tk.Label(self.frame, text="%s" % row, width=3, borderwidth="1", 
                     relief="solid").grid(row=row, column=0)
            t="this is the second column for row %s" %row
            tk.Label(self.frame, text=t).grid(row=row, column=1)

    def onFrameConfigure(self, event):
        '''Reset the scroll region to encompass the inner frame'''
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))


class ParameterPage(tk.Frame):
    
    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        
        self.update_n = 1
        
        self.canvas=tk.Canvas(self, borderwidth=0, bg='lavender', width=100, height=100)# background='#ffffff')
        
        self.frame = tk.Frame(self.canvas, bg='lavender', width=100, height=100)
        self.vsb = tk.Scrollbar(self, orient='vertical',command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.vsb.set)
        
        self.vsb.pack(side='right',fill='y')
        self.canvas.pack(side='left',fill='both',expand=True)
        self.canvas.create_window((4,4), window=self.frame,anchor='nw',tags='self.frame')
        self.frame.bind("<Configure>",self.onFrameConfigure)
        
        # start of labeling the interface
        
        labelPage = tk.Label(self.frame, text="Parameter Setting", font=LARGE_FONT)
        labelPage.grid(row=0, column=2, pady=10, padx=10)

        # note to user
        self.labelNote = tk.Label(self.frame, text=("""Note: New parameter value will be used for calculating
              time-course simulation and potential landscape."""))
        self.labelNote.grid(row=2,column=2,pady=5,padx=5)
        #self.labelNote.grid(row=len(model.ParameterName)+6,column=0,pady=5,padx=5)
        
#        button1 =ttk.Button(self.frame, text="Back to Main Window",
#                                 command=lambda: controller.show_frame(StartPage))
#        button1.grid(row=1, column=2, pady=10,padx=10, ipadx=5)
        #button1.pack(pady=2,padx=10, ipadx=5)
        labelheader= tk.Label(self.frame, text="You can set the parameter values")
        labelheader.grid(row=4, column=0,pady=10,padx=10)        

        self.parameterValue=dict()
        self.entryPara=dict()
        
        self.labelParaName=dict()
        self.LabelCurrent=dict()
        
        self.myframeNumber=dict()

        # to create a dictionary for the number of frame for each variable
        self.initConds_frameNumber=dict()          
        
        # Save Button 
        self.SaveButton=ttk.Button(self.frame,text="Save Parameter Values", width=25,command=self.save_parameter_values)
        self.SaveButton.grid(row=5, column=2)

        
#        self.PlotButton=ttk.Button(self,text="Plot time course")
#        self.PlotButton.pack(pady=2,padx=2, ipadx=5)
        
#        self.PlotButton.bind("<Button>", Parameter_plot_time_course)
        
#        self.DataViewerButton=ttk.Button(self,text="Data Viewer",  command=lambda: controller.show_frame(ParameterTimeCourseDataViewer))
#        self.DataViewerButton.pack(pady=2,padx=2, ipadx=5)
        
        # plotting of the time course graph
#        canvas = FigureCanvasTkAgg(f8,self)
#        canvas.show()
#        canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True) 
        
#        toolbar = NavigationToolbar2TkAgg(canvas,self)
#        toolbar.update()
#        toolbar.pack(side=tk.TOP)
#        canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)        
    
    
    def save_parameter_values(self):
        print("save_parameter_values was called")       
        
        for i in range(len(model.ParameterName)):            

            self.parameterValue['r'+str(i)].set(self.entryPara['r'+str(i)].get())
            if self.parameterValue['r'+str(i)].get() !='':
                print('model.ParameterName['+str(i)+']:',model.ParameterName[i])
                model.ParameterValue[i]=float(self.parameterValue['r'+str(i)].get())
                #setattr(model,'model.ParameterValue['+str(i)+']', float(self.parameterValue['r'+str(i)].get()))
                print('model.ParameterValue['+str(i)+']:',model.ParameterValue[i])
                self.LabelCurrent['l'+str(i)].config(text=float(self.parameterValue['r'+str(i)].get()))

        # update the parameter value into model object model.AllParameters
        updatedPar=[]
        for i in range(len(model.ParameterValue)):
            updatedPar.append(model.ParameterName[i]+"="+str(model.ParameterValue[i])+";\n")        

        model.AllParameters=updatedPar
        print('model.AllParameters:',model.AllParameters)

        print('model.ParameterName:',model.ParameterName)        
        print('model.ParameterValue:',model.ParameterValue)
        
        model.fromInitialCondition = np.ones((1,model.num_gene))*model.min_value
        model.toInitialCondition = np.ones((1,model.num_gene))*model.max_value
        
        model.y=np.zeros((1,model.num_gene), dtype = 'float')
        model.t=np.zeros((1,1))
        model.output=model.y
        model.outputT= np.hstack((model.t,model.y))
        
        # for storing simulated results 
        model.TimecourseData=np.zeros((int((model.t_end-model.t_start)/model.h+1),model.num_gene))
        model.PositionProb = np.zeros((model.gridNumber,model.gridNumber))
        model.InitialConditions=np.zeros((model.TrajectoryNumber,model.num_gene))        
 
        #'''This loop get all the random initial conditions in the state space'''  
        for j in range(model.num_gene):
            #print(j)
            model.InitialConditions[:,j][:,None]=np.random.random((model.TrajectoryNumber,1))*(model.toInitialCondition[0,j]-model.fromInitialCondition[0,j])+model.fromInitialCondition[0,j]
            #print(model.InitialConditions)   
        

        
        model.TempAttractors=np.zeros((model.TrajectoryNumber,noGene))        
        
    def onFrameConfigure(self, event):
        '''Reset the scroll region to encompass the inner frame'''
        self.canvas.configure(scrollregion=self.canvas.bbox('all'))
 
    def update_frame(self):
        print('update_frame was called in Parameter Page')   
        self.update_n=self.update_n + 1
        print("self.update_n=", self.update_n)        

        # to destroy the previous frame
        # for checking how many frame and the frame number(FN)
        # print(self.myframeNumber) 
        if self.update_n > 2:
            self.myframeNumber['FN'+str(self.update_n-1)].destroy()  

        # create a new frame
        self.myframeNumber['FN'+str(self.update_n)]=tk.Frame(self.frame, bg='lavender', width=400, height=400, bd=1)
        self.myframeNumber['FN'+str(self.update_n)].grid()

        # Labeling of current and new value 
        tk.Label(self.myframeNumber['FN'+str(self.update_n)],text="Current Value:", font=NORMAL_FONT).grid(row=3,column=2,pady=2,padx=2)
        tk.Label(self.myframeNumber['FN'+str(self.update_n)],text="New Value:", font=NORMAL_FONT).grid(row=3,column=3,pady=2,padx=2)

        #print('len(model.ParameterName):',len(model.ParameterName))
        #print('len(model.ParameterValue):',len(model.ParameterValue))
 
        for i in range(len(model.ParameterName)):
            self.parameterValue['r'+str(i)]=tk.StringVar()
            #self.vars.append(self.initialValue)

            self.labelParaName['ParN'+str(i)]=tk.Label(self.myframeNumber['FN'+str(self.update_n)],text=model.ParameterName[i], width=20, font=NORMAL_FONT)
            self.labelParaName['ParN'+str(i)].grid(row=i+5,column=1,pady=2,padx=2)
            self.LabelCurrent['l'+str(i)]=tk.Label(self.myframeNumber['FN'+str(self.update_n)],text=model.ParameterValue[i], width=20,font=NORMAL_FONT)
            self.LabelCurrent['l'+str(i)].grid(row=i+5,column=2,pady=2,padx=2)
            self.entryPara['r'+str(i)]=tk.Entry(self.myframeNumber['FN'+str(self.update_n)],width=20,textvariable=self.parameterValue['r'+str(i)])
            self.entryPara['r'+str(i)].grid(row=i+5,column=3,pady=2,padx=2)
            
            #self.labelGeneName['GN'+str(i)]=tk.Label(self.frame,text=model.geneName[i], font=NORMAL_FONT)
            #self.labelGeneName['GN'+str(i)].grid(row=i+4,column=1,pady=2,padx=2)


                

class TimeCourseDataViewer(tk.Frame):

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)

        #self.master = parent
        #self.master.title("Data Viewer")
        #self.master.geometry("800x800")
        #self.frame= tk.Frame(self.master)
        

        self.frame = tk.Frame(self)         
    
#        button1 = ttk.Button(self.frame, text="Back to Main Window",
#                                command=lambda: controller.show_frame(StartPage))
#        button1.pack(pady=2,padx=10, ipadx=5)
            
        buttonTimeCourse = ttk.Button(self.frame, text="Back to Time Course",
                                command=lambda: controller.show_frame(TimeCoursePage))
        buttonTimeCourse.pack(pady=2,padx=10, ipadx=5)        
     
        self.table_frame= tk.Frame(self.frame, bg='lavender', width=800, height=600)
        self.table_frame.pack(side='left',fill='both',expand=True)
            
        table_label = tk.Label(self.table_frame, text='Data Viewer', bg='lavender')
        table_label.pack(pady=2,padx=10, ipadx=5,expand=True)
            
        #self.SaveButton = ttk.Button(self.table_frame, text='Save Data to csv', width =25)#, command= save_data_to_csv)
        #self.SaveButton.pack()
        #self.SaveButton.bind("<Button>", save_data_to_csv)      
     
        self.SaveAsButton = ttk.Button(self.table_frame, text='Save as', width= 15, command=self.save_as)
        self.SaveAsButton.pack()
        
        #self.COLUMNS =['time']      
        
        #if model.type == 'ode':
        #    for i in range(len(model.geneName)):
        #        self.COLUMNS.append(model.geneName[i])
                #self.table.heading(model.geneName[i], text=model.geneName[i])
                
        #if model.type == 'SBML':
        #    for i in range(len(model.geneName)):
        #        self.COLUMNS.append(model.geneName[i])        
            
        #print('VariableName:',model.geneName)
        #print('COLUMNS:',self.COLUMNS)        
        
        self.table = ttk.Treeview(self.table_frame, height="50")#,columns=("Time","u","v","p","","") )#, columns=self.COLUMNS, show='headings') #height=500) #self) #table_frame, show='headings', )
            # add a vertical scrollbar
        vscroll = tk.Scrollbar(self.table_frame, orient="vertical",command= self.table.yview)
        vscroll.pack(side='right', fill='y')
            #table.configure(yscrollcommand=vscroll.set)
            # add a horizontal scrollbar
        hscroll = tk.Scrollbar(self.table_frame, orient="horizontal",command = self.table.xview)
        hscroll.pack(side='bottom',fill='x')
        self.table.configure(yscrollcommand=vscroll.set,xscrollcommand=hscroll.set)
            
        #k=0
        # setting column header for the table
        #for column in self.COLUMNS:
        #    print(column)
            #print(self.table.heading)
            #self.table.heading(column, text=column)               
        #    self.table.heading('#'+str(k),text=column)
        
        # self.table.heading('#0',text='time')
        

                        
        # setting first column width
        #table.column("#0",minwidth=0,width=10, stretch=tk.NO)
            
        # add data into table from DataOutputT 
        #for i in range(10):
        #    table.insert('', 'end', values= )
        # number of rows in DataOutputT =DataOutputT.shape[0]
        #if model.type == 'ode':
        #    for i in range(DataOutputT.shape[0]):
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
        #        self.table.insert('', 'end', text=DataOutputT[i,0], values=DataOutputT[i,:])
                #table.insert('', 'end', text='', values=DataOutputT[i,:])   
        #        print(DataOutputT[i,:]) 

        #if model.type == 'SBML':
        #    for i in range(sbml_DataOutputT.shape[0]):
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
        #        self.table.insert('', 'end', text=sbml_DataOutputT[i,0], values=sbml_DataOutputT[i,:])
                #table.insert('', 'end', text='', values=DataOutputT[i,:])  
                
        self.table.pack(side='left',fill='y',expand=True)                 
        self.frame.pack()


        
#        legend_frame= tk.Frame(self, bg='yellow')
#        legend_frame.pack()
#        legend_label = tk.Label(legend_frame, text='legend', bg='yellow')
#        legend_label.pack()
        
        self.status_bar_label = tk.Label(self, text="After loaded with an ode or a SBML model, start with plotting one trajectory.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)
        
    def write_to_file(self,file_name):
            try:
                np.savetxt(file_name, model.DataOutputT, delimiter=",", fmt='%10.5f')
                #content = model.DataOutputT.astype('|S10')
                #with open(file_name, 'w') as the_file:
                #    the_file.write(content)
            except IOError:
                tkinter.messagebox.showwarning("Save", "Could not save the file.")


    def save_as(self,event=None):
            input_file_name = tk.filedialog.asksaveasfilename(defaultextension=".csv",
                                                                   filetypes=[("CSV file", "*.csv")])
            if input_file_name:
                global file_name
                file_name = input_file_name

                self.write_to_file(file_name)
                #root.title('{} - {}'.format(os.path.basename(file_name), PROGRAM_NAME))
            return "break"

        
    def update_frame(self):
        print('time course dataviewer update_frame was called.')
        
        # delete the whole table
        #def delButton(self):
            #x = main.tree.get_children()
        #x = self.table.get_children()
        #for item in x:
                #main.tree.delete(item)
        #    print(item)
            #self.table.delete(item)
                
        #for widget in self.frame.winfo_children():
        #    widget.destroy()    
 
        #self.frame = tk.Frame(self)         
    
        #button1 = ttk.Button(self.frame, text="Back to Home",
        #                        command=lambda: self.controller.show_frame(StartPage))
        #button1.pack(pady=2,padx=10, ipadx=5)
            
        #buttonTimeCourse = ttk.Button(self.frame, text="Back to Time Course",
        #                        command=lambda: self.controller.show_frame(TimeCoursePage))
        #buttonTimeCourse.pack(pady=2,padx=10, ipadx=5)        
     
        #table_frame= tk.Frame(self.frame, bg='lavender', width=800, height=600)
        #table_frame.pack(side='left',fill='both',expand=True)
            
        #table_label = tk.Label(table_frame, text='Time Course Data', bg='yellow')
        #table_label.pack(pady=2,padx=10, ipadx=5,expand=True)
            
        #self.SaveButton = ttk.Button(table_frame, text='Save Data to csv', width =25)#, command= save_data_to_csv)
        #self.SaveButton.pack()
        #self.SaveButton.bind("<Button>", save_data_to_csv)      
     
        self.COLUMNS =['time']      
        
        if model.type == 'ode':
            for i in range(len(model.geneName)):
                self.COLUMNS.append(model.geneName[i])
                
                #self.table.heading(model.geneName[i], text=model.geneName[i])

        
                
        if model.type == 'SBML':
            for i in range(len(model.geneName)):
                self.COLUMNS.append(model.geneName[i])   
                
        # Add the columns in Treeview
        # tree["columns"]=("one","two")
        self.table["columns"]=tuple(self.COLUMNS)
            
        print('VariableName:',model.geneName)
        print('COLUMNS:',self.COLUMNS)        
        
        #self.table = ttk.Treeview(self.table_frame, columns=self.COLUMNS, show='headings') #height=500) #self) #table_frame, show='headings', )
            # add a vertical scrollbar
        #vscroll = tk.Scrollbar(self.table_frame, orient="vertical",command= self.table.yview)
        #vscroll.pack(side='right', fill='y')
            #table.configure(yscrollcommand=vscroll.set)
            # add a horizontal scrollbar
        #hscroll = tk.Scrollbar(self.table_frame, orient="horizontal",command = self.table.xview)
        #hscroll.pack(side='bottom',fill='x')
        #self.table.configure(yscrollcommand=vscroll.set,xscrollcommand=hscroll.set)
            
        jj=1
        # setting column header for the table
        for column in self.COLUMNS:
            print(jj)
            print('#'+str(jj))
            print(column)
            #self.table.heading(column, text=column) 
            
            self.table.heading('#'+str(jj),text=column, anchor=tk.W)
            jj=jj + 1
        
        # self.table.heading('#0',text='time')
        
        # setting the first empty column to width 0 
        #self.table.heading('#0',text='row')
        #self.table.column("row",width=10)
        #self.table.column("#0",width=0)
        self.table['show']= 'headings'

        # to delete or clear an entire Treeview with Tkinter
        for i in self.table.get_children():
            self.table.delete(i)

                        
        # setting first column width
        #table.column("#0",minwidth=0,width=10, stretch=tk.NO)
            
        # add data into table from DataOutputT 
        #for i in range(10):
        #    table.insert('', 'end', values= )
        # number of rows in DataOutputT =DataOutputT.shape[0]
        if (model.type == 'ode') and (model.DataOutputT != '') :
            for i in range(model.DataOutputT.shape[0]):
                print('i:',i)
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
                #self.table.insert('', 'end', text=DataOutputT[i,0], values=DataOutputT[i,1:])
                #self.table.insert('', 'end', text=DataOutputT[i,0], values=' '.join(map(str,DataOutputT[i,:])) )
                self.table.insert('', 'end', values=' '.join(map(str,model.DataOutputT[i,:])) )
                #table.insert('', 'end', text='', values=DataOutputT[i,:])   
                #print(DataOutputT[i,:]) 

        if (model.type == 'SBML') and (model.DataOutputT != ''):
            for i in range(sbml_DataOutputT.shape[0]):
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
                #self.table.insert('', 'end', text=sbml_DataOutputT[i,0], values=sbml_DataOutputT[i,:])
                self.table.insert('', 'end', values=' '.join(map(str,sbml_DataOutputT[i,:])) )
                #table.insert('', 'end', text='', values=DataOutputT[i,:])  
                
        #self.table.pack(side='left',fill='y',expand=True)                 
        #self.frame.pack()
        self.update()

class initTimeCourseDataViewer(tk.Frame):
    print('initTimeCourseDataViewer class')

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)      

        self.frame = tk.Frame(self)         
    
#        button1 = ttk.Button(self.frame, text="Back to Main Window",
#                                command=lambda: controller.show_frame(StartPage))
#        button1.pack(pady=2,padx=10, ipadx=5)
            
        buttonTimeCourse = ttk.Button(self.frame, text="Back to 'Time Course 2 Init'",
                                command=lambda: controller.show_frame(InitTimeCoursePage2))
        buttonTimeCourse.pack(pady=2,padx=10, ipadx=5)        
     
        self.table_frame= tk.Frame(self.frame, bg='lavender', width=800, height=600)
        self.table_frame.pack(side='left',fill='both',expand=True)
            
        table_label = tk.Label(self.table_frame, text='Data Viewer 2', bg='lavender')
        table_label.pack(pady=2,padx=10, ipadx=5,expand=True)
            
        #self.SaveButton = ttk.Button(self.table_frame, text='Save Data to csv', width =25)#, command= save_data_to_csv)
        #self.SaveButton.pack()
        #self.SaveButton.bind("<Button>", save_data_to_csv)     
        
        self.SaveAsButton = ttk.Button(self.table_frame, text='Save As', width= 15, command=self.save_as)
        self.SaveAsButton.pack()        
        
        self.table = ttk.Treeview(self.table_frame, height="50")
        
        # add a vertical scrollbar
        vscroll = tk.Scrollbar(self.table_frame, orient="vertical",command= self.table.yview)
        vscroll.pack(side='right', fill='y')
        
        #table.configure(yscrollcommand=vscroll.set)
        # add a horizontal scrollbar
        hscroll = tk.Scrollbar(self.table_frame, orient="horizontal",command = self.table.xview)
        hscroll.pack(side='bottom',fill='x')
        self.table.configure(yscrollcommand=vscroll.set,xscrollcommand=hscroll.set)
                            
        self.table.pack(side='left',fill='y',expand=True)                 
        self.frame.pack()

        self.status_bar_label = tk.Label(self, text="After loaded with an ode or a SBML model, start with plotting one trajectory.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)

    def write_to_file(self,file_name):
            try:
                np.savetxt(file_name, model.initDataOutputT, delimiter=",", fmt='%10.5f')
                #content = model.DataOutputT.astype('|S10')
                #with open(file_name, 'w') as the_file:
                #    the_file.write(content)
            except IOError:
                tkinter.messagebox.showwarning("Save", "Could not save the file.")


    def save_as(self,event=None):
            input_file_name = tk.filedialog.asksaveasfilename(defaultextension=".csv",
                                                                   filetypes=[("CSV file", "*.csv")])
            if input_file_name:
                global file_name
                file_name = input_file_name

                self.write_to_file(file_name)
                #root.title('{} - {}'.format(os.path.basename(file_name), PROGRAM_NAME))
            return "break"


        
    def update_frame(self):
        print('time course dataviewer update_frame was called.')
             
        self.COLUMNS =['time']      
        
        if model.type == 'ode':
            for i in range(len(model.geneName)):
                self.COLUMNS.append(model.geneName[i])
        
                
        if model.type == 'SBML':
            for i in range(len(model.geneName)):
                self.COLUMNS.append(model.geneName[i])   
                
        # Add the columns in Treeview
        # tree["columns"]=("one","two")
        self.table["columns"]=tuple(self.COLUMNS)
            
        print('VariableName:',model.geneName)
        print('COLUMNS:',self.COLUMNS)        
                    
        jj=1
        # setting column header for the table
        for column in self.COLUMNS:
            print(jj)
            print('#'+str(jj))
            print(column)
            #self.table.heading(column, text=column) 
            
            self.table.heading('#'+str(jj),text=column, anchor=tk.W)
            jj=jj + 1
        

        self.table['show']= 'headings'

        # to delete or clear an entire Treeview with Tkinter
        for i in self.table.get_children():
            self.table.delete(i)

                        
        # setting first column width
        #table.column("#0",minwidth=0,width=10, stretch=tk.NO)
            
        # add data into table from DataOutputT 
        #for i in range(10):
        #    table.insert('', 'end', values= )
        # number of rows in DataOutputT =DataOutputT.shape[0]
        if (model.type == 'ode') and (model.initDataOutputT != '') :
            for i in range(model.initDataOutputT.shape[0]):
                print('i:',i)
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
                #self.table.insert('', 'end', text=DataOutputT[i,0], values=DataOutputT[i,1:])
                #self.table.insert('', 'end', text=DataOutputT[i,0], values=' '.join(map(str,DataOutputT[i,:])) )
                self.table.insert('', 'end', values=' '.join(map(str,model.initDataOutputT[i,:])) )
                #table.insert('', 'end', text='', values=DataOutputT[i,:])   
                #print(DataOutputT[i,:]) 

        if (model.type == 'SBML') and (model.initDataOutputT != ''):
            for i in range(model.initDataOutputT.shape[0]):
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
                #self.table.insert('', 'end', text=sbml_DataOutputT[i,0], values=sbml_DataOutputT[i,:])
                self.table.insert('', 'end', values=' '.join(map(str,model.initDataOutputT[i,:])) )
                #table.insert('', 'end', text='', values=DataOutputT[i,:])  
                
        #self.table.pack(side='left',fill='y',expand=True)                 
        #self.frame.pack()
        self.update()

class ParameterTimeCourseDataViewer(tk.Frame):
    print('ParameterTimeCourseDataViewer class')

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)      

        self.frame = tk.Frame(self)         
    
        button1 = ttk.Button(self.frame, text="Back to Home",
                                command=lambda: controller.show_frame(StartPage))
        button1.pack(pady=2,padx=10, ipadx=5)
            
        buttonTimeCourse = ttk.Button(self.frame, text="Back to Time Course",
                                command=lambda: controller.show_frame(ParameterPage))
        buttonTimeCourse.pack(pady=2,padx=10, ipadx=5)        
     
        self.table_frame= tk.Frame(self.frame, bg='lavender', width=800, height=600)
        self.table_frame.pack(side='left',fill='both',expand=True)
            
        table_label = tk.Label(self.table_frame, text='Time Course Data', bg='yellow')
        table_label.pack(pady=2,padx=10, ipadx=5,expand=True)
            
#        self.SaveButton = ttk.Button(self.table_frame, text='Save Data to csv', width =25)#, command= save_data_to_csv)
#        self.SaveButton.pack()
#        self.SaveButton.bind("<Button>", save_data_to_csv)           

        self.SaveAsButton = ttk.Button(self.table_frame, text='Save as', width= 25, command=self.save_as)
        self.SaveAsButton.pack()     

        self.table = ttk.Treeview(self.table_frame, height="50")
        
        # add a vertical scrollbar
        vscroll = tk.Scrollbar(self.table_frame, orient="vertical",command= self.table.yview)
        vscroll.pack(side='right', fill='y')
        
        #table.configure(yscrollcommand=vscroll.set)
        # add a horizontal scrollbar
        hscroll = tk.Scrollbar(self.table_frame, orient="horizontal",command = self.table.xview)
        hscroll.pack(side='bottom',fill='x')
        self.table.configure(yscrollcommand=vscroll.set,xscrollcommand=hscroll.set)
                            
        self.table.pack(side='left',fill='y',expand=True)                 
        self.frame.pack()

        self.status_bar_label = tk.Label(self, text="After loaded with an ode or a SBML model, start with plotting one trajectory.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        self.status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)

    def write_to_file(self,file_name):
            try:
                np.savetxt(file_name, model.initDataOutputT, delimiter=",", fmt='%10.5f')
                #content = model.DataOutputT.astype('|S10')
                #with open(file_name, 'w') as the_file:
                #    the_file.write(content)
            except IOError:
                tkinter.messagebox.showwarning("Save", "Could not save the file.")


    def save_as(self,event=None):
            input_file_name = tk.filedialog.asksaveasfilename(defaultextension=".csv",
                                                                   filetypes=[("CSV file", "*.csv")])
            if input_file_name:
                global file_name
                file_name = input_file_name

                self.write_to_file(file_name)
                #root.title('{} - {}'.format(os.path.basename(file_name), PROGRAM_NAME))
            return "break"

        
    def update_frame(self):
        print('time course dataviewer update_frame was called.')
             
        self.COLUMNS =['time']      
        
        if model.type == 'ode':
            for i in range(len(model.geneName)):
                self.COLUMNS.append(model.geneName[i])
        
                
        if model.type == 'SBML':
            for i in range(len(model.geneName)):
                self.COLUMNS.append(model.geneName[i])   
                
        # Add the columns in Treeview
        # tree["columns"]=("one","two")
        self.table["columns"]=tuple(self.COLUMNS)
            
        print('VariableName:',model.geneName)
        print('COLUMNS:',self.COLUMNS)        
                    
        jj=1
        # setting column header for the table
        for column in self.COLUMNS:
            print(jj)
            print('#'+str(jj))
            print(column)
            #self.table.heading(column, text=column) 
            
            self.table.heading('#'+str(jj),text=column, anchor=tk.W)
            jj=jj + 1
        

        self.table['show']= 'headings'

        # to delete or clear an entire Treeview with Tkinter
        for i in self.table.get_children():
            self.table.delete(i)

                        
        # setting first column width
        #table.column("#0",minwidth=0,width=10, stretch=tk.NO)
            
        # add data into table from DataOutputT 
        #for i in range(10):
        #    table.insert('', 'end', values= )
        # number of rows in DataOutputT =DataOutputT.shape[0]
        if (model.type == 'ode') and (model.initDataOutputT != '') :
            for i in range(model.initDataOutputT.shape[0]):
                print('i:',i)
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
                #self.table.insert('', 'end', text=DataOutputT[i,0], values=DataOutputT[i,1:])
                #self.table.insert('', 'end', text=DataOutputT[i,0], values=' '.join(map(str,DataOutputT[i,:])) )
                self.table.insert('', 'end', values=' '.join(map(str,model.initDataOutputT[i,:])) )
                #table.insert('', 'end', text='', values=DataOutputT[i,:])   
                #print(DataOutputT[i,:]) 

        if (model.type == 'SBML') and (model.initDataOutputT != ''):
            for i in range(model.initDataOutputT.shape[0]):
                #table.insert('', 'end', text='', values=DataOutputT[i,:])
                #self.table.insert('', 'end', text=sbml_DataOutputT[i,0], values=sbml_DataOutputT[i,:])
                self.table.insert('', 'end', values=' '.join(map(str,sbml_DataOutputT[i,:])) )
                #table.insert('', 'end', text='', values=DataOutputT[i,:])  
                
        #self.table.pack(side='left',fill='y',expand=True)                 
        #self.frame.pack()
        self.update()


class AttractorsInfoPage(tk.Frame):

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Attractors Info Page", font=LARGE_FONT)
        label.pack(pady=2,padx=10)

#        button1 = ttk.Button(self, text="Back to Home",
#                            command=lambda: controller.show_frame(StartPage))
#        button1.pack(pady=2,padx=10, ipadx=5)
        
        #buttonTopView2 = ttk.Button(self, text="Top View", command=lambda: controller.show_frame(Graph_Page2))
        #buttonTopView2.pack(padx=5, pady=5)
        
        # frame for table to display attractor coordinates
        self.frame=tk.Frame(self)
        
        self.table_frame=tk.Frame(self.frame, bg='lavender', width=800, height=600)
        self.table_frame.pack(side='left', fill='both', expand=True)
        
        AttractorInfo_label = tk.Label(self.table_frame, text='Attractor Information', bg='lavender')
        AttractorInfo_label.pack(pady=2, padx=10, ipadx=5, expand=True)
        
        self.table = ttk.Treeview(self.table_frame, height="50")
        vscroll=tk.Scrollbar(self.table_frame, orient="vertical", command=self.table.yview)
        vscroll.pack(side='right', fill='y')
        hscroll= tk.Scrollbar(self.table_frame, orient="horizontal", command=self.table.xview)
        hscroll.pack(side='bottom', fill='x')
        
        self.table.configure(yscrollcommand=vscroll.set, xscrollcommand=hscroll.set)
        self.table.pack(side='left', fill='y', expand=True)
        
        buttonTopView = ttk.Button(self, text="Top View", command=lambda: controller.show_frame(Graph_Page2))
        buttonTopView.pack(padx=5, pady=5)        
        
        self.frame.pack()
        
        
        
        # canvas for displaying Attractors information
        #canvas3 = FigureCanvasTkAgg(f6, self)
        #canvas3.show()
        #canvas3.get_tk_widget().pack(side=tk.TOP) #, fill=tk.BOTH, expand=True)
        

        
    def update_frame(self):
        
        print('AttractorInfoPage update_frame was called.')
        
        self.COLUMNS=['Attractor Number']
        
        if model.type == 'ode' or model.type == 'SBML':
            for i in range(len(model.geneName)):
                self.COLUMNS.append(model.geneName[i])
                
        self.table["columns"]=tuple(self.COLUMNS)
        
        print('VariableName:', model.geneName)
        print('COLUMNS:', self.COLUMNS)
        
        # setting the column header for the table
        j=1
        for column in self.COLUMNS:
            self.table.heading('#'+str(j), text=column, anchor=tk.W)
            j= j + 1
            
        self.table['show']='headings'
        
        for i in self.table.get_children():
            self.table.delete(i)
            
        if model.type== 'ode' or model.type == 'SBML':
            #print('model attractor:',model.Attractors)
            for i in range(len(model.Attractors)):
                mylist=[]
                mylist.append(i+1)
                row_Attractor=model.Attractors[i,:]
                #print('row_Attractor:',row_Attractor)
                for j in range(model.num_gene):
                    #print(j)
                    mylist.append(row_Attractor[j])
                    #print(row_Attractor[j])
                self.table.insert('', 'end', values=' '.join(map(str, mylist)) )
                #self.table.insert('', 'end', values=i+1)
                #self.table.insert('', 'end', values=' '.join(map(str, model.Attractors[i,:])) )
        
        #f6.clear()
        #a6 = f6.text(0.35,0.9, "Number of Attractors="+str(len(model.Attractors)), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        #for i in range(len(model.Attractors)):
        #    a6 = f6.text(0.35,0.5, str(model.Attractors[i]), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        #a6 = f6.text(0.35,0.5, str(model.Attractors), bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        #a6 = f6.text(0.1,0.1, "The zero matrix is the default dummy attractor.", bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
        #f6.canvas.draw_idle()        
        self.update()

class PCAInfoPage(tk.Frame):

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="PCA Info Page", font=LARGE_FONT)
        label.pack(pady=2,padx=10)
        
        # frame for table to display attractor coordinates
        self.frame=tk.Frame(self)
        
        self.table_frame=tk.Frame(self.frame, bg='lavender', width=800, height=600)
        self.table_frame.pack(side='left', fill='both', expand=True)
        
        AttractorInfo_label = tk.Label(self.table_frame, text='PCA Information', bg='lavender')
        AttractorInfo_label.pack(pady=2, padx=10, ipadx=5, expand=True)
        
        self.table = ttk.Treeview(self.table_frame, height="50")
        vscroll=tk.Scrollbar(self.table_frame, orient="vertical", command=self.table.yview)
        vscroll.pack(side='right', fill='y')
        hscroll= tk.Scrollbar(self.table_frame, orient="horizontal", command=self.table.xview)
        hscroll.pack(side='bottom', fill='x')
        
        self.table.configure(yscrollcommand=vscroll.set, xscrollcommand=hscroll.set)
        self.table.pack(side='left', fill='y', expand=True)
        
        buttonTopView = ttk.Button(self, text="PCA View", command=lambda: controller.show_frame(Graph_Page3))
        buttonTopView.pack(padx=5, pady=5)        
        
        self.frame.pack()
                
    def update_frame(self):
        
        print('PCAInfoPage update_frame was called.')
        
        self.COLUMNS=['PCA Variance Ratio: ']        
        self.COLUMNS.append('PC 1')
        self.COLUMNS.append('PC 2')
                
        self.table["columns"]=tuple(self.COLUMNS)
        
        #print('VariableName:', model.geneName)
        print('COLUMNS:', self.COLUMNS)
        
        # setting the column header for the table
        j=1
        for column in self.COLUMNS:
            self.table.heading('#'+str(j), text=column, anchor=tk.W)
            j= j + 1
            
        self.table['show']='headings'
        
        for i in self.table.get_children():
            self.table.delete(i)
            

        mylist=[]
        #mylist.append(i+1)

        mylist.append(model.PCA_Ratio)
        print('model.PCA_Ratio: ', model.PCA_Ratio)
        self.table.insert('', 'end', values=' '.join(map(str, mylist)) )

               
        self.update()


class PhasePlane_Page(tk.Frame):
    '''Phase Plane drawn from using random initial conditions'''

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="""Phase Plane 
         using Random Initial Conditions""", font=LARGE_FONT)
        label.pack(pady=2,padx=10)

#        button1 = ttk.Button(self, text="Back to Main Window",
#                            command=lambda: controller.show_frame(StartPage))
#        button1.pack(pady=2,padx=10, ipadx=5)
        
        #button2 = ttk.Button(self, text="Plot landscape in BTCe Page", command= lambda: controller.plot_landscape())
        #button2.pack()

  
        # canvas for drawing phase plane
        canvas3 = FigureCanvasTkAgg(f3, self)
        canvas3.draw()
        canvas3.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        #toolbar3 = NavigationToolbar2Tk(canvas3, self)
        toolbar3 = NavigationToolbar2TkAgg(canvas3, self)
        toolbar3.update()
        toolbar3.pack(side=tk.TOP, pady=2,padx=5, ipadx=5)
        canvas3._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)
        
        
        # User control buttons

        buttonPlot3 = ttk.Button(self, text="Plot Phase Plane")
        buttonPlot3.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)
        buttonPlot3.bind("<Button>", plot_phase_plane_graph)

        button4 = ttk.Button(self, text="Clear Phase Plane", command= lambda: clear_phase_plane_graph())
        button4.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)   
        
        Info_label= tk.Label(self, text="Please click the 'Plot Phase Plane' button for more trajectories.")
        Info_label.pack()
        #canvas_StatusBar = tk.Canvas(self, width=600, height=64, bg='lavender')

        #canvas_StatusBar.pack()
        
        #canvas = FigureCanvasTkAgg(f5,self)
        #canvas.show()
        #canvas._tkcanvas.pack(side=tk.TOP, fill= tk.X)
        #status_bar_label = tk.Label(canvas, text="Start with loading an ode model.", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        #status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)

    def update_frame(self):
        self.update()


class PhasePlane_Page2(tk.Frame):
    '''Phase Plane drawn by using user input initial conditions or parameter values'''

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text=("""Phase Plane
        using User input Initial Conditions or Parameter Values"""), font=LARGE_FONT)
        label.pack(pady=2,padx=10)

#        button1 = ttk.Button(self, text="Back to Main Window",
#                            command=lambda: controller.show_frame(StartPage))
#        button1.pack(pady=2,padx=10, ipadx=5)
        
        #button2 = ttk.Button(self, text="Plot landscape in BTCe Page", command= lambda: controller.plot_landscape())
        #button2.pack()

  
        # canvas for drawing phase plane
        canvas9 = FigureCanvasTkAgg(f9, self)
        canvas9.draw()
        canvas9.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH)#, expand=True)

        #toolbar9 = NavigationToolbar2Tk(canvas9, self)
        toolbar9 = NavigationToolbar2TkAgg(canvas9, self)
        toolbar9.update()
        toolbar9.pack(side=tk.TOP, pady=2,padx=5, ipadx=5)
        canvas9._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH)#, expand=True)
        
        
        # User control buttons
        buttonPlot3 = ttk.Button(self, text="Plot Phase Plane")
        buttonPlot3.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)
        buttonPlot3.bind("<Button>", plot_phase_plane2_graph)

        buttonToSettingInitConds = ttk.Button(self, text="Setting Initial Conds", command = lambda: controller.show_frame(InitConditionsPage2))
        buttonToSettingInitConds.pack(side=tk.LEFT, pady=5, padx=5, ipadx=5)
        
        buttonPlot4 = ttk.Button(self, text="Add current Initial conditions trajectory")
        buttonPlot4.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)
        buttonPlot4.bind("<Button>", plot_add_phase_plane2_graph)        

        button4 = ttk.Button(self, text="Clear Phase Plane", command= lambda: clear_phase_plane2_graph())
        button4.pack(side=tk.LEFT, pady=5,padx=5, ipadx=5)          
        Info_label= tk.Label(self, text="Please click the 'Add current Initial conditions trajectory' button for one trajectory.")
        Info_label.pack()
      


        #canvas_StatusBar = tk.Canvas(self, width=600, height=64, bg='lavender')

        #canvas_StatusBar.pack()
        
 #       canvas = FigureCanvasTkAgg(f9,self)
 #       canvas.show()
 #       canvas._tkcanvas.pack(side=tk.TOP, fill= tk.X)


    def update_frame(self):
        self.update()


class Graph_Page(tk.Frame):
    '''Plotting 3D Landscape Page '''

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="3D Waddington's Landscape", font=LARGE_FONT)
        label.pack(pady=2,padx=10)

#        button1 = ttk.Button(self, text="Back to Main Window",
#                            command=lambda: controller.show_frame(StartPage))
#        button1.pack(pady=2,padx=10, ipadx=5)
        

        # canvas for drawing 3D landscape
        canvas = FigureCanvasTkAgg(f, self)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        #toolbar = NavigationToolbar2Tk(canvas, self)
        toolbar = NavigationToolbar2TkAgg(canvas, self)
        toolbar.update()
        toolbar.pack(side=tk.TOP, pady=2,padx=5, ipadx=5)
        canvas._tkcanvas.pack(pady=2,padx=10, ipadx=5, side=tk.TOP, fill=tk.BOTH, expand=True)
        
        
        # User control buttons
        b = ttk.Button(self, text='Plot Landscape (default)', command=lambda:self.start_progress("default"))
        b.pack(side="left",padx=20, pady=10)
        b.focus_set()
        
        #buttonSmoothSurface = ttk.Button(self, text="Default with Smooth Surface", command= lambda: defaultSmoothSurface())
        #buttonSmoothSurface.pack(side="left", padx=5, pady=5) 
        
        #slider current value
        current_value=tk.DoubleVar()
        
        def get_current_value():
            return '{: .2f}'.format(current_value.get())
        
        def slider_changed(event):
            print("slider_changed was called")
            #value_label.configure(text=get_current_value())
            
            model.Smooth_U  = MCLandscape_U.copy()
            model.SmoothSurfSize=get_current_value()
            size=int(float(model.SmoothSurfSize))
            print('size=',size)

            stride=1
            m, n = model.Smooth_U.shape
    
            avg=0
            for i in range(0, m - size + 1, stride):
                for j in range(0, n - size + 1, stride):
                    avg = sum(sum(model.Smooth_U[i:i + size, j:j + size])) / (size * size)
                    for ii in range(i, i + size):
                        for jj in range(j, j + size):
                            model.Smooth_U[ii, jj] = avg  
        
            f.clear()
            a = f.add_subplot(111, projection='3d')
            surf=a.plot_surface(model.X, model.Y, model.Smooth_U, cmap='jet', linewidth=0.2, antialiased=True, edgecolor='Gray')
            #f.colorbar(surf, shrink=0.5)    
            f.colorbar(surf,shrink=0.7,aspect=5)
            a.set_xlabel(str(model.geneName[model.index_2]))
            a.set_ylabel(str(model.geneName[model.index_1]))
            #a.set_ylabel('y')
            a.set_zlabel("U")    
            f.canvas.draw_idle()    
            print("slider_changed finished")            
            
        # label for the slider
        slider_label=ttk.Label(self,text='Smoothing Value:')
        slider_label.pack(side="left", padx=5, pady=5)       
        
        slider=tk.Scale(self, from_=1, to=5, orient='horizontal', repeatinterval=1, command=slider_changed, variable=current_value)
        slider.pack(side="left", padx=5, pady=5)
        
        #current_value_label=ttk.Label(self, text='Smoothness Value:')
        #current_value_label.pack(side="left", padx=5, pady=5)
        
        # value label
        #value_label = ttk.Label(self, text=get_current_value())
        #value_label.pack(side="left", padx=5, pady=5)
 
        buttonTopView = ttk.Button(self, text="Top View", command=lambda: controller.show_frame(Graph_Page2))
        buttonTopView.pack(side="left", padx=5, pady=5)
        #buttonTopView.bind("<Button>", Plot_TopView) 
        
        #bpca = ttk.Button(self, text='Plot Landscape (PCA)', command=lambda:self.start_progress("pca"))
        bpca = ttk.Button(self, text='Plot Landscape (PCA)', command=lambda: controller.show_frame(Graph_Page3))
        bpca.pack(side="left",padx=20, pady=10)
        bpca.focus_set()
        
        #buttonColorbar = ttk.Button(self, text="Color Bar", command= lambda: colorbar())
        #buttonColorbar.pack(side="left", padx=5, pady=5)    
 
        #buttonColorbar = ttk.Button(self, text="No Color Bar", command= lambda: no_colorbar())
        #buttonColorbar.pack(side="left", padx=5, pady=5)           

        #buttonClearerSurface = ttk.Button(self, text="Clearer Surface No Color Bar", command= lambda: clearerSurface_no_colorbar())
        #buttonClearerSurface.pack(side="left", padx=5, pady=5)  

        button2 = ttk.Button(self, text="Clear Graph", command= lambda: clear_graph())
        button2.pack(side="left", padx=5, pady=5)
        
        #self.button3PlotContour = ttk.Button(self, text="Contour", command= lambda: self.plot_contour())
        #self.button3PlotContour.pack(side="left", padx=5, pady=5)
        #button3PlotContour.bind("<Button>", plot_contour())

        # define the progress bar
        #self.progressB =Progressbar(self, orient=HORIZONTAL, length=150, mode= 'determinate')
        #self.progress =Progressbar(self, orient=HORIZONTAL, length=150, mode= 'indeterminate')
        # mode can be 'determinate' or indeterminate (mode= 'indeterminate' will show the progressbar indicator to the left and to the right)     
        
        # status bar in the bottom
        #status_bar_label = tk.Label(self, text="", bd=1, relief=tk.SUNKEN, anchor=tk.W)
        #status_bar_label.pack(side=tk.BOTTOM, fill=tk.X)        

        self.lst = [
            'Bushes01.png',  'Bushes02.png', 'Bushes03.png', 'Bushes04.png', 'Bushes05.png',
            'Forest01.png',  'Forest02.png', 'Forest03.png', 'Forest04.png', 'Road01.png',
            'Road02.png',    'Road03.png',   'Lake01.png',   'Lake02.png',   'Field01.png']


    def plot_contour(self):
        ''' Plot contour '''
        print("plot_contour was called.")

        #def toggle():

        #    if self.button3PlotContour.config('relief')[-1] == 'sunken':
        #        self.button3PlotContour.config(relief="raised")
        #        toggle=1
        #        return toggle
        #    else:
        #        self.button3PlotContour.config(relief="sunken")
        #        toggle=0
        #        return toggle
        # add contour to the 3D surface plot
        #a.contour(X, Y, Z, zdir='z', cmap='jet')  
        #f.canvas.draw_idle()
        if model.name=='':
            tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        
        elif model.calculated_U == 'no':
            tk.messagebox.showinfo("No potential values found.","Please calculate the potential values first.")
    
        else:  
            a = f.add_subplot(111, projection='3d')
    
            a.plot_surface(model.X, model.Y, model.Z, cmap = 'jet')
            # add contour to the 3D surface plot
            #print('model.toggle:',model.toggle)
            if (model.toggle % 2) ==0:
                #a.contour(X, Y, Z, zdir='z', offset=0, cmap=cm.coolwarm ) #cmap='jet')
                a.contour(model.X, model.Y, model.Z, zdir='z', offset=0, cmap='jet')
            model.toggle = model.toggle + 1 
            #print('model.toggle=',model.toggle)
            #print(model.index_1)
            a.set_xlabel(str(model.geneName[model.index_1]))
            a.set_ylabel(str(model.geneName[model.index_2]))
            #a.set_ylabel('y')
            a.set_zlabel("U")
            a.set_zlim(0, np.amax(model.Z)+2)
            f.canvas.draw_idle
            

    def calculate_potential_U(self):
        def calculate_progress():
            if model.name=='':
                tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
            else:
                #f.text(0.5,0.5, 'calculating potential landscape ...', bbox={'facecolor':'lavender','alpha':0.5, 'pad':10}, fontsize=10)
                #self.progressB.grid()
                #self.progressB.pack(padx=2, pady=2)
                #self.progressB.pack(side=tk.TOP)
                #self.progress.pack(side="top")
                #self.progress.start()
                model.Calculate_PositionProb() 
    #        global X
    #        global Y
    #        global Z
                model.X, model.Y, model.Z=model.Plotting_Landscape()
            
    #        model.X = X
    #        model.Y = Y
    #        model.Z = Z
                print('calculation time: ', model.calculation_time)
                print(time.time()-calculation_start)
                # seems that setting the time.sleep(0.1) is faster to get the landscape
                time.sleep(0.1)# model.calculation_time)
                #self.progressB.stop()
                #self.progressB.forget()
                #self.buttonPlot['state']='normal'
            
            
                Attractors= np.vstack({tuple(row) for row in model.TempAttractors})
                model.Attractors = Attractors
                #print('Number of attractors=', len(Attractors))
                #print('Attractors:')
                #print(Attractors)
     
                # Plot 3D graph
             
                # to plot 3D view into f GraphPage
                f.clear()
           
                a = f.add_subplot(111, projection='3d')
                a.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
                #print(model.index_1)
                a.set_xlabel(str(model.geneName[model.index_2]))
                a.set_ylabel(str(model.geneName[model.index_1]))
                #a.set_ylabel('y')
                a.set_zlabel("U")
                f.canvas.draw_idle()
           
                # to plot top view into f4 GraphPage2
           
                a4 = f4.add_subplot(111, projection='3d')
                a4.plot_surface(model.X, model.Y, model.Z, cmap = 'jet') 
                # add contour to the 3D surface plot
                #a.contour(X, Y, Z, zdir='z', offset=0, cmap='jet')
                #print(model.index_1)
                a4.set_xlabel(str(model.geneName[model.index_2]))
                a4.set_ylabel(str(model.geneName[model.index_1]))
                #a.set_ylabel('y')
                a4.set_zlabel("U")    
                a4.view_init(elev=90, azim=-90)
                f4.canvas.draw_idle()   
            
        self.buttonPlot['state']='disabled'
        threading.Thread(target=calculate_progress).start()
        
    def update_frame(self):
        
        self.update()    

    def start_progress(self,mode):
        ''' Open modal window '''
        print('start_progress was called.')
        if model.name=='':
            tk.messagebox.showinfo("No model equation found.","Please load a model equation first.")
        else:            
            model.loopNum=1
            model.PositionProb = np.zeros((model.gridNumber, model.gridNumber)) # initialization every call this func
            s = ProgressWindow(self, 'MyTest', self.lst,mode)  # create progress window
            self.master.wait_window(s)  # display the window and wait for it to close

class Graph_Page2(tk.Frame):
    '''Plotting Top view of Landscape Page '''

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="Top View of Waddington's Landscape", font=LARGE_FONT)
        label.pack(pady=2,padx=10)
        
        # canvas for drawing 3D landscape
        canvas = FigureCanvasTkAgg(f4, self)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        toolbar = NavigationToolbar2TkAgg(canvas, self)
        toolbar.update()
        toolbar.pack(side=tk.TOP, pady=2,padx=5, ipadx=5)
        canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)       
        
        # User control buttons

        buttonAttractorsInfoPage = ttk.Button(self, text="Attractors Info", command=lambda: controller.show_frame(AttractorsInfoPage))
        buttonAttractorsInfoPage.pack(side="left", padx=5, pady=5, ipadx=5)
        
        button3DView = ttk.Button(self, text="3D View", command=lambda: controller.show_frame(Graph_Page))
        button3DView.pack(side="left", padx=5, pady=5, ipadx=5)

        
    def update_frame(self):
        self.update()

class Graph_Page3(tk.Frame):
    '''Plotting PCA of Landscape Page '''

    def __init__(self, parent, controller):
        self.controller = controller
        tk.Frame.__init__(self, parent)
        label = tk.Label(self, text="PCA View of Waddington's Landscape", font=LARGE_FONT)
        label.pack(pady=2,padx=10)
        
        # canvas for drawing 3D landscape of PCA view
        canvas = FigureCanvasTkAgg(f12, self)
        canvas.draw()
        canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

        #label = tk.Label(self, text="PCA Variance Ratio: ", font=("Arial Bold", 10))
        #label.pack(pady=2,padx=10)
        #labelPCA_Ratio = tk.Label(self, text=model.PCA_Ratio, font=("Arial Bold", 10))
        #labelPCA_Ratio.pack(side="left", pady=2, padx=10)        

        toolbar = NavigationToolbar2TkAgg(canvas, self)
        toolbar.update()
        toolbar.pack(side=tk.TOP, pady=2,padx=5, ipadx=5)
        canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)       
        
        # User control buttons

        buttonAttractorsInfoPage = ttk.Button(self, text="PCA Info", command=lambda: controller.show_frame(PCAInfoPage))
        buttonAttractorsInfoPage.pack(side="left", padx=5, pady=5, ipadx=5)
        
        button3DView = ttk.Button(self, text="3D View", command=lambda: controller.show_frame(Graph_Page))
        button3DView.pack(side="left", padx=5, pady=5, ipadx=5)

        
    def update_frame(self):
        self.update()
  
def on_closing():
    if messagebox.askokcancel("Quit", "Do you want to quit?"):
        app.destroy()      


class StatusBar(tk.Frame):
    def __init__(self, parent):
        tk.Frame.__init__(self, parent)
        self.label = tk.Label(self, bd=1, relief=tk.SUNKEN, anchor = tk.W, bg='yellow')
        self.label.pack(fill=tk.X)
        
    def set(self, formata, *args):
        self.label.config(text=formata % args)
        self.label.update_idletasks()  
        
    def clear(self):
        self.label.config(text="")
        self.label.update_idletasks()     

def main(args=None):
    """The main routine."""
    if args is None:
        args = sys.argv[1:]

    print("This is the main routine.")
       
    app.mainloop()
    

# main program
if __name__== "__main__":  
    
    # using object oriented method to create an object model defined by the class Model
    model = Model()
    print('model:',model)
    
    textstring='default text'

    app = MCLapp()
    
    global StableSteadyState
    StableSteadyState=[] #np.array((result1[-1,:].shape))
    
    global Attractors
    
    global count_SimNum

           
    status=StatusBar(app)
    status.pack(side=tk.BOTTOM, fill=tk.X)
    status.set("Start by loading an ode model")
        
    app.geometry("1255x850+10+10")
    app.protocol("WM_DELETE_WINDOW", on_closing)
    
    app.update_idletasks()
    main()
    
