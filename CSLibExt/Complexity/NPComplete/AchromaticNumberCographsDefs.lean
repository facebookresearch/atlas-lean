/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER OF COGRAPHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT5] ACHROMATIC NUMBER;
H. L. Bodlaender, "Achromatic number is NP-complete for cographs and interval graphs",
Information Processing Letters 31 (1989), 135-138, doi:10.1016/0020-0190(89)90221-4.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.AchromaticNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCographs

open MetaMathlibExt.Complexity.NPComplete.AchromaticNumber (AchromaticNumberInstance)

/-- Well-formedness of an instance: a well-formed ACHROMATIC NUMBER instance whose graph is
a cograph (no induced path on four vertices), with `0 < K`. -/
def WellFormed (i : AchromaticNumberInstance) : Prop :=
  AchromaticNumber.WellFormed i ∧
    ¬ (SimpleGraph.pathGraph 4).IsIndContained (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

open Classical in
/-- ACHROMATIC NUMBER OF COGRAPHS as a decision problem over bitstrings. -/
noncomputable def achromaticNumberCographsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := AchromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ AchromaticNumber.AchromaticNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumberCographs
