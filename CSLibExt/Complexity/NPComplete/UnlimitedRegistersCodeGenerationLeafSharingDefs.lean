/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CODE GENERATION WITH UNLIMITED REGISTERS (only leaves shared): definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO5] CODE GENERATION WITH UNLIMITED
REGISTERS (comment: NP-complete even if only leaves have in-degree exceeding 1);
A. V. Aho, S. C. Johnson and J. D. Ullman, "Code generation for expressions with common
subexpressions", Journal of the ACM 24(1) (1977), 146-160, doi:10.1145/321992.322001.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.CodeGenerationWithUnlimitedRegistersDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnlimitedRegistersCodeGenerationLeafSharing

open CodeGenerationWithUnlimitedRegisters (Graph IsLeaf)

/-- An instance, as in `CodeGenerationWithUnlimitedRegistersWanted`: vertex count, arcs labelled
`L`/`R`, bound `K`. -/
abbrev UnlimitedRegistersCodeGenerationLeafSharingInstance :=
  CodeGenerationWithUnlimitedRegisters.CodeGenerationWithUnlimitedRegistersInstance

/-- Well-formedness of an instance: the instance of CODE GENERATION WITH UNLIMITED REGISTERS is
well-formed, and every vertex with more than one incoming arc is a leaf. -/
def WellFormed (i : UnlimitedRegistersCodeGenerationLeafSharingInstance) : Prop :=
  CodeGenerationWithUnlimitedRegisters.WellFormed i ∧
    ∀ v, 1 < {w | (Graph i).Adj w v}.ncard → IsLeaf i v

/-- A program of at most `K` instructions computing all roots, exactly as in
`CodeGenerationWithUnlimitedRegistersWanted`. -/
def UnlimitedRegistersCodeGenerationLeafSharingFeasible
    (i : UnlimitedRegistersCodeGenerationLeafSharingInstance) : Prop :=
  CodeGenerationWithUnlimitedRegisters.CodeGenerationWithUnlimitedRegistersFeasible i

open Classical in
/-- CODE GENERATION WITH UNLIMITED REGISTERS (only leaves shared) as a decision problem over
bitstrings. -/
noncomputable def unlimitedRegistersCodeGenerationLeafSharingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnlimitedRegistersCodeGenerationLeafSharingInstance) x with
  | some i => decide (WellFormed i ∧ UnlimitedRegistersCodeGenerationLeafSharingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.UnlimitedRegistersCodeGenerationLeafSharing
