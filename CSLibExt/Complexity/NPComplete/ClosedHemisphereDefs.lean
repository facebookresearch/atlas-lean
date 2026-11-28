/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSED HEMISPHERE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP6] OPEN HEMISPHERE, p. 246
(comment: "The same results hold for the related CLOSED HEMISPHERE problem in which we ask that
y satisfy x·y ≥ 0 for at least K m-tuples x ∈ X [Johnson and Preparata, 1978].");
D. S. Johnson and F. P. Preparata, "The densest hemisphere problem", Theoretical
Computer Science 6 (1978), 93-107, doi:10.1016/0304-3975(78)90006-3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OpenHemisphereDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosedHemisphere

open MetaMathlibExt.Complexity.NPComplete.OpenHemisphere (OpenHemisphereInstance intOf WellFormed)

/-- A nonzero rational `m`-tuple `y` with `x · y ≥ 0` for at least `K` elements `x` of `X`. -/
def ClosedHemisphereFeasible (i : OpenHemisphereInstance) : Prop :=
  ∃ y : Fin i.1 → ℚ, y ≠ 0 ∧ i.2.2 ≤
    (i.2.1.filter fun x => 0 ≤ ∑ j : Fin i.1, (intOf (x.getD j (0, 0)) : ℚ) * y j).length

open Classical in
/-- CLOSED HEMISPHERE as a decision problem over bitstrings. -/
noncomputable def closedHemisphereDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenHemisphereInstance) x with
  | some i => decide (WellFormed i ∧ ClosedHemisphereFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ClosedHemisphere
