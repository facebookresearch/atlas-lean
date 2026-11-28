/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER OF TREES: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT5] ACHROMATIC NUMBER;
N. Cairnie and K. Edwards, "Some results on the achromatic number", Journal of Graph Theory
26 (1997), 129-136, doi:10.1002/(SICI)1097-0118(199711)26:3<129::AID-JGT3>3.0.CO;2-T.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.AchromaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumberTrees

open MetaMathlibExt.Complexity.NPComplete.AchromaticNumber (AchromaticNumberInstance)

/-- Well-formedness of an instance: a well-formed ACHROMATIC NUMBER instance whose graph is
a tree, with `0 < K`. -/
def WellFormed (i : AchromaticNumberInstance) : Prop :=
  AchromaticNumber.WellFormed i ∧
    (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1).IsTree ∧ 0 < i.2.2

open Classical in
/-- ACHROMATIC NUMBER OF TREES as a decision problem over bitstrings. -/
noncomputable def achromaticNumberTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := AchromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ AchromaticNumber.AchromaticNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumberTrees
