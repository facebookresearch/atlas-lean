/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION ON A ONE-REGISTER MACHINE (shared vertices have arcs only to leaves): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO4] CODE GENERATION ON A
ONE-REGISTER MACHINE (comment: NP-complete even if every vertex of in-degree larger than one has
arcs only to leaves, credited to Aho, Johnson and Ullman 1977);
A. V. Aho, S. C. Johnson and J. D. Ullman, "Code generation for expressions with common
subexpressions", Journal of the ACM 24(1) (1977), 146-160, doi:10.1145/321992.322001.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CodeGenerationOnAOneRegisterMachineDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneRegisterCodeGenerationSharedLeafArcs

open CodeGenerationOnAOneRegisterMachine (Graph)

/-- An instance, as in `CodeGenerationOnAOneRegisterMachineWanted`: vertex count, arc list, bound
`K`. -/
abbrev OneRegisterCodeGenerationSharedLeafArcsInstance :=
  CodeGenerationOnAOneRegisterMachine.CodeGenerationOnAOneRegisterMachineInstance

/-- Well-formedness of an instance: the instance of CODE GENERATION ON A ONE-REGISTER MACHINE is
well-formed, and every vertex with more than one incoming arc has arcs only to leaves. -/
def WellFormed (i : OneRegisterCodeGenerationSharedLeafArcsInstance) : Prop :=
  CodeGenerationOnAOneRegisterMachine.WellFormed i ∧
    ∀ v, 1 < {w | (Graph i).Adj w v}.ncard →
      ∀ u, (Graph i).Adj v u →
        ∀ w, ¬ (Graph i).Adj u w

/-- A program of at most `K` instructions computing all roots, exactly as in
`CodeGenerationOnAOneRegisterMachineWanted`. -/
def OneRegisterCodeGenerationSharedLeafArcsFeasible
    (i : OneRegisterCodeGenerationSharedLeafArcsInstance) : Prop :=
  CodeGenerationOnAOneRegisterMachine.CodeGenerationOnAOneRegisterMachineFeasible i

open Classical in
/-- CODE GENERATION ON A ONE-REGISTER MACHINE (shared vertices have arcs only to leaves) as a
decision problem over bitstrings. -/
noncomputable def oneRegisterCodeGenerationSharedLeafArcsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneRegisterCodeGenerationSharedLeafArcsInstance) x with
  | some i => decide (WellFormed i ∧ OneRegisterCodeGenerationSharedLeafArcsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OneRegisterCodeGenerationSharedLeafArcs
