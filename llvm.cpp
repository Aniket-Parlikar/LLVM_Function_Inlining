#define DEBUG_TYPE "finalproject"
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Analysis/Verifier.h>
#include <llvm/Assembly/PrintModulePass.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CallingConv.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Function.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Instruction.h>
#include <llvm/IR/Instructions.h>
#include <llvm/ADT/SetVector.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/Twine.h>
#include <llvm/Analysis/InlineCost.h>
#include <llvm/Transforms/Utils/ValueMapper.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/SymbolTableListTraits.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/SymbolTableListTraits.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FormattedStream.h>
#include <llvm/Support/MathExtras.h>
#include <llvm/IR/User.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm//Support/InstIterator.h>
#include <llvm/IR/IRBuilder.h>
#include <iterator>
#include <functional>
#include <memory>
#include <vector>
#include <algorithm>
#include <utility>
#include <cassert>

using namespace llvm;

 // Global Variable Declarations.......... kedar




namespace {
	//The name of the pass is InliningPass which is of type pass........ kedar
  struct InliningPass : public ModulePass {
	 
	 //Defining a char ID
    static char ID;

	// We're invoking our ModulePass
    InliningPass() : ModulePass(ID) {}

	// Defining a bolean function which runs on our module..............................Kedar
    virtual bool runOnModule(Module &M) {
	 GlobalVariable* gvar_int32_x = new GlobalVariable(/*Module=*/M,
	 /*Type=*/IntegerType::get(M.getContext(), 32),
	 /*isConstant=*/false,
	 /*Linkage=*/GlobalValue::ExternalLinkage,
	 /*Initializer=*/0, // has initializer, specified below
	 /*Name=*/"x");
	 gvar_int32_x->setAlignment(4);

	 // Defining our constants to be passed as initializers to our global variable
	 ConstantInt* const_int32_2 = ConstantInt::get(M.getContext(), APInt(32, StringRef("32"), 10));
	 ConstantInt* const_int32_3 = ConstantInt::get(M.getContext(), APInt(32, StringRef("1"), 10));
	 ConstantInt* const_int32_4 = ConstantInt::get(M.getContext(), APInt(32, StringRef("0"), 10));

	 // Setting the initializer to globalvariable
	 gvar_int32_x->setInitializer(const_int32_2);
	
	//Module::FunctionListType FL;
	//FL = M.getFunctionList();
	//errs() << *FL;
	
	//Here we're loading the 'pop-direct-branch' function into a variable
	Function *op = M.getFunction("pop_direct_branch");
	
	// Initializing ValuetoValueMapTy vmap
	ValueToValueMapTy vmap;
	
	
	// Here we're iterating over all instructions and functions in our module........... kedar
	for (Module::iterator f=M.begin(), fend=M.end(); f!=fend; f++){
		for(Function::iterator b=f->begin(), bend=f->end(); b!=bend; b++){
			for(BasicBlock::iterator I=b->begin(), I1=b->end(); I!=I1; I++){
				
			if(CallInst* CI=dyn_cast<CallInst>(I)){
				
			// We're checking if a particular instruction is a CallInst
			errs() << "\n This is a call instruction \n" <<*CI<<"\n";
			
			//We're getting the called function from our called instruction
			Function* F = CI->getCalledFunction();
			
			// Using an if loop to check if the function is present
			if(F)
				
				// Checking if the function name starts with 'p' and not a declaration functions..... kedar
			{	StringRef name = F->getName();
				if(name[0]=='p' && !(F->isDeclaration()) && name!="pop_direct_branch"){
					errs() << "This is a function " << name << "\n";
					
					// We're performing Function cloning
					Function *clonef = CloneFunction(F, vmap, false);
					
					errs() << "The clone function is" << *clonef;
					
					// Getting parent module of the old function
					Module *m1 = F->getParent();
					
					// We're obtaining list of functions in the new module
					llvm::Module::FunctionListType& f1 = m1->getFunctionList();
					
					// In the end we're inserting clone to the list of new functions
					f1.push_back(clonef);
					
					// Iterating over each instruction in cloned function
					for(Function::iterator b=clonef->begin(), bend=clonef->end(); b!=bend; b++){
					for(BasicBlock::iterator In=b->begin(), In1=b->end(); In!=In1; In++){
					
					
					//errs()<<"\n Inside loop inst \n." << *In;
 					//if(isa<ReturnInst>(*In)){
						
					// We're checking if each instruction can is of type ReurnInst
					if(ReturnInst *RI = dyn_cast<ReturnInst>(In)){
					//if (ReturnInst *ri = dyn_cast<ReturnInst>(I))
					//errs()<<"This is a return instruction" <<*RI;;
				
						// We're checking if the instruction is not returning any void
						if(RI->getNumOperands() != 0)
						{
						errs()<<"\n This is non void RI \n" << *RI;
						
						// We're obtaining the return value in this line
						Value *ret = RI->getReturnValue();
						
						errs()<<"\n The return value is \n" <<*ret;
						
						// We're creating another type of instruction called as StoreInst
						// While intializing it we're paasing the return of return value and global variable value as arguments
						StoreInst *SI = new StoreInst(ret,gvar_int32_x,RI);
						
						// Here we are creating a new CallInst and passing 'pop_direct_branch' and ReturnInst 
						CallInst *pop = CallInst::Create(op,"",RI);
						
						// Here we're defining LoadInst and passing globalvariable and CallInst as parameters
						Value* V = new LoadInst(gvar_int32_x,"",CI);
						
						// Here we're replacing all instances of CallInst CI with V
						CI->replaceAllUsesWith(V);
						
						// Here we're replacing the call old function with the call to new function
						CI->setCalledFunction(clonef);
						}
					} 
					
					}
					}

					
	 				
				}
				
			}
	}
	}
		}
	}
	return false;
	}

      //errs() << "I saw a function called " << F.getName() << "!\n";
      
    };
  }

// Automatically enable the pass.
// http://adriansampson.net/blog/clangpass.html
char InliningPass::ID = 0;

// Declaring our RegisterPass
static RegisterPass<InliningPass> X("InliningPass", "Sample",false,false);