/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PACKING SQUARES INTO A SQUARE: definitions

Source:
J. Y.-T. Leung, T. W. Tam, C. S. Wong, G. H. Young and F. Y. L. Chin, "Packing squares into a
square", Journal of Parallel and Distributed Computing 10 (1990), 271-275,
doi:10.1016/0743-7315(90)90019-L.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.StripPackingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PackingSquaresIntoSquare

open StripPacking (StripPackingFeasible)

/-- An instance: the side lengths `s₁, ..., sₙ` of the squares and the side `s` of the
container. -/
abbrev PackingSquaresIntoSquareInstance := List ℕ × ℕ

/-- The STRIP PACKING instance of the squares in an `s × s` square: rectangles `(sⱼ, sⱼ)`, strip
width `s`, height bound `s`. -/
def toStripPacking (i : PackingSquaresIntoSquareInstance) : StripPacking.StripPackingInstance :=
  (i.1.map fun a => (a, a), i.2, i.2)

/-- Well-formedness of an instance: every side length is positive, and so is `s`. -/
def WellFormed (i : PackingSquaresIntoSquareInstance) : Prop :=
  (∀ a ∈ i.1, 0 < a) ∧ 0 < i.2

/-- The squares can be packed into the `s × s` square (`StripPackingFeasible` of
`toStripPacking`). -/
def PackingSquaresIntoSquareFeasible (i : PackingSquaresIntoSquareInstance) : Prop :=
  StripPackingFeasible (toStripPacking i)

open Classical in
/-- PACKING SQUARES INTO A SQUARE as a decision problem over bitstrings. -/
noncomputable def packingSquaresIntoSquareDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PackingSquaresIntoSquareInstance) x with
  | some i => decide (WellFormed i ∧ PackingSquaresIntoSquareFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PackingSquaresIntoSquare
