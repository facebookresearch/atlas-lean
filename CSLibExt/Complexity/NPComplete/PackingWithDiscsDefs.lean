/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PACKING WITH DISCS: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [14] PACKING WITH SQUARES, comment;
R. J. Fowler, M. S. Paterson and S. L. Tanimoto, "Optimal packing and covering in the plane are
NP-complete", Information Processing Letters 12 (1981), 133-137,
doi:10.1016/0020-0190(81)90111-3.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import CSLibExt.Complexity.NPComplete.PackingSquaresRectilinearPolygonDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PackingWithDiscs



open PackingSquaresRectilinearPolygon

/-- The point `p` lies in the polygon: in some cell `[a, a + 1] × [b, b + 1]` of it. -/
def InPolygon (i : PackingSquaresRectilinearPolygonInstance) (p : ℝ × ℝ) : Prop :=
  ∃ q ∈ i.2.1, (q.1 : ℝ) ≤ p.1 ∧ p.1 ≤ q.1 + 1 ∧ (q.2 : ℝ) ≤ p.2 ∧ p.2 ≤ q.2 + 1

/-- `K` discs of diameter `d` with centers `c j` lie in the polygon and do not overlap. -/
def PackingWithDiscsFeasible (i : PackingSquaresRectilinearPolygonInstance) : Prop :=
  ∃ c : Fin i.2.2 → ℝ × ℝ,
    (∀ j, ∀ p : ℝ × ℝ, (p.1 - (c j).1) ^ 2 + (p.2 - (c j).2) ^ 2 ≤ ((i.1 : ℝ) / 2) ^ 2 →
      InPolygon i p) ∧
    ∀ j j', j ≠ j' → (i.1 : ℝ) ^ 2 ≤ ((c j).1 - (c j').1) ^ 2 + ((c j).2 - (c j').2) ^ 2

open Classical in
/-- PACKING WITH DISCS as a decision problem over bitstrings. -/
noncomputable def packingWithDiscsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PackingSquaresRectilinearPolygonInstance) x with
  | some i => decide (WellFormed i ∧ PackingWithDiscsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PackingWithDiscs
