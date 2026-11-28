/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EUCLIDEAN LINE COVER (covering lines by points): definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 3 (1982),
381-395, doi:10.1016/0196-6774(82)90032-3 (comment on problem [2], the dual EUCLIDEAN LINE
COVER);
N. Megiddo and A. Tamir, "On the complexity of locating linear facilities in the plane",
Operations Research Letters 1 (1982), 194-197, doi:10.1016/0167-6377(82)90039-6.
-/
module

public import Mathlib.Basic.Real.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GeometricTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover

open GeometricTravelingSalesman (toInt)

/-- A line `a x + b y = c`, given by its integer coefficients `(a, b, c)` in positive/negative-part
form. -/
abbrev Line := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- An instance: the lines and the number of points `K`. -/
abbrev EuclideanLineCoverInstance := List Line × ℕ

/-- The point set `{(x, y) ∈ ℝ² | a x + b y = c}` of a line. -/
def lineSet (ℓ : Line) : Set (ℝ × ℝ) :=
  {p | (toInt ℓ.1 : ℝ) * p.1 + (toInt ℓ.2.1 : ℝ) * p.2 = (toInt ℓ.2.2 : ℝ)}

/-- Well-formedness of an instance: every line has `(a, b) ≠ (0, 0)`, the lines are distinct
as point sets, and `K` is positive. -/
def WellFormed (i : EuclideanLineCoverInstance) : Prop :=
  (∀ ℓ ∈ i.1, toInt ℓ.1 ≠ 0 ∨ toInt ℓ.2.1 ≠ 0) ∧ (i.1.map lineSet).Nodup ∧ 0 < i.2

/-- There are `K` points of `ℝ × ℝ` such that every line contains one of them. -/
def EuclideanLineCoverFeasible (i : EuclideanLineCoverInstance) : Prop :=
  ∃ q : Fin i.2 → ℝ × ℝ, ∀ ℓ ∈ i.1, ∃ j, q j ∈ lineSet ℓ

open Classical in
/-- EUCLIDEAN LINE COVER as a decision problem over bitstrings. -/
noncomputable def euclideanLineCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EuclideanLineCoverInstance) x with
  | some i => decide (WellFormed i ∧ EuclideanLineCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EuclideanLineCover
