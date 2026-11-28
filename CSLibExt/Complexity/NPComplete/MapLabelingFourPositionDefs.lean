/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAP LABELING WITH FOUR POSITIONS: definitions

Source:
M. Formann and F. Wagner, "A packing problem with applications to lettering of maps", in
*Proceedings of the 7th Annual Symposium on Computational Geometry (SoCG 1991)*, ACM (1991),
281-288, doi:10.1145/109648.109680.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MapLabelingFourPosition

/-- An instance: the points, each coordinate an integer as `(positive part, negative part)`, and
`σ = p / q` as the pair `(p, q)`. -/
abbrev MapLabelingFourPositionInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ × ℕ

/-- The integer `a - b` encoded by `(a, b)`. -/
def toInt (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - z.2

/-- The points as integer pairs. -/
def points (i : MapLabelingFourPositionInstance) : List (ℤ × ℤ) :=
  i.1.map fun pt => (toInt pt.1, toInt pt.2)

/-- Well-formedness of an instance: no point is listed twice and `p, q > 0`. -/
def WellFormed (i : MapLabelingFourPositionInstance) : Prop :=
  (points i).Nodup ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- `|d| ≥ p`. -/
def AtLeast (p : ℕ) (d : ℤ) : Prop := (p : ℤ) ≤ d ∨ d ≤ -(p : ℤ)

/-- Some choice of corners `(a, b) ∈ {0, 1}²` satisfies the displayed integer inequalities for
every two distinct points. For `p, q > 0`, as well-formedness requires, this says the labels,
squares of side `p / q`, pairwise do not overlap. -/
def MapLabelingFourPositionFeasible (i : MapLabelingFourPositionInstance) : Prop :=
  ∃ a b : Fin (points i).length → Fin 2, ∀ j k : Fin (points i).length, j ≠ k →
    AtLeast i.2.1 ((i.2.2 : ℤ) * ((points i)[j].1 - (points i)[k].1) -
        (i.2.1 : ℤ) * (((a j : ℕ) : ℤ) - ((a k : ℕ) : ℤ))) ∨
      AtLeast i.2.1 ((i.2.2 : ℤ) * ((points i)[j].2 - (points i)[k].2) -
        (i.2.1 : ℤ) * (((b j : ℕ) : ℤ) - ((b k : ℕ) : ℤ)))

open Classical in
/-- MAP LABELING WITH FOUR POSITIONS as a decision problem over bitstrings. -/
noncomputable def mapLabelingFourPositionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MapLabelingFourPositionInstance) x with
  | some i => decide (WellFormed i ∧ MapLabelingFourPositionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MapLabelingFourPosition
