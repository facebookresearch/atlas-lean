/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalNecklaceCrossedJoints

/-!
# The original first-crossing pairing index

Each full original missing simplex uses its least actually crossed
joint. The same canonical two-bead pairing inserts exactly that joint.
Its complete original support and both strict-side vertices are kept.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.OriginalNecklace.CrossedJoints

/-- The full original two-bead index at the first actual crossed necklace joint. -/
structure Index {n : ℕ} (J : Finset (Fin (n + 1))) where
  /-- The actual first original joint crossed by the entire support. -/
  pivot : Fin (n + 1)
  /-- The same full original pivot-insertion index. -/
  bead : OriginalTwoBead.Index.{u} pivot
  /-- The pivot is one of the supplied original necklace joints. -/
  joint : pivot ∈ J
  /-- No earlier original joint is crossed by the entire original support. -/
  first : ∀ k ∈ crossed J (stdSimplex.nonDegenerateEquiv' bead.original).val, pivot ≤ k

/-- Original support crossings are precisely the original full simplex crossings. -/
theorem mem_crossed_support_iff {n d : ℕ} (J : Finset (Fin (n + 1)))
    (x : (Δ[n] : SSet.{u}).nonDegenerate d) (k : Fin (n + 1)) :
    k ∈ crossed J (stdSimplex.nonDegenerateEquiv' x).val ↔
      k ∈ J ∧ (∃ a, x.val a < k) ∧ ∃ b, k < x.val b := by
  rw [mem_crossed]
  constructor
  · rintro ⟨hk, ⟨a, ha, hak⟩, b, hb, hkb⟩
    obtain ⟨i, rfl⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).mp ha
    obtain ⟨j, rfl⟩ := (stdSimplex.nonDegenerateEquiv'_iff _ _).mp hb
    exact ⟨hk, ⟨i, hak⟩, j, hkb⟩
  · rintro ⟨hk, ⟨i, hi⟩, j, hj⟩
    exact ⟨hk, ⟨x.val i, (stdSimplex.nonDegenerateEquiv'_iff _ _).mpr ⟨i, rfl⟩, hi⟩,
      x.val j, (stdSimplex.nonDegenerateEquiv'_iff _ _).mpr ⟨j, rfl⟩, hj⟩

namespace Index

variable {n : ℕ} {J : Finset (Fin (n + 1))} (s : Index.{u} J)

/-- The original pivot is genuinely crossed by the entire original support. -/
theorem pivot_crossed : s.pivot ∈ crossed J (stdSimplex.nonDegenerateEquiv' s.bead.original).val :=
  (mem_crossed_support_iff _ _ _).mpr ⟨s.joint, s.bead.below, s.bead.above⟩

/-- The same whole original paired simplex has exactly the same crossed joints. -/
theorem crossed_paired :
    crossed J (stdSimplex.nonDegenerateEquiv' s.bead.paired).val =
      crossed J (stdSimplex.nonDegenerateEquiv' s.bead.original).val := by
  rw [s.bead.support_paired]
  exact crossed_insert J _ s.pivot ((mem_crossed _ _ _).mp s.pivot_crossed).2

/-- The entire original face is outside the native necklace for its actual supplied joint. -/
theorem original_not_mem : s.bead.original.val ∉ (complex J).obj (op ⦋s.bead.dim⦌) := by
  intro h
  exact s.bead.original_not_mem ((OriginalTwoBead.mem_union_iff _ _).mpr
    ((mem_complex_iff _ _).mp h s.pivot s.joint))

/-- The entire original paired simplex is outside the native necklace at the same actual joint. -/
theorem paired_not_mem : s.bead.paired.val ∉ (complex J).obj (op ⦋s.bead.dim + 1⦌) := by
  intro h
  exact s.bead.paired_not_mem ((OriginalTwoBead.mem_union_iff _ _).mpr
    ((mem_complex_iff _ _).mp h s.pivot s.joint))

/-- The actual first crossed pivot is the minimum of the complete original crossing set. -/
theorem pivot_eq_min : s.pivot =
    (crossed J (stdSimplex.nonDegenerateEquiv' s.bead.original).val).min'
      ⟨s.pivot, s.pivot_crossed⟩ :=
  le_antisymm (s.first _ (Finset.min'_mem _ _))
    (Finset.min'_le _ _ s.pivot_crossed)

end Index

end SSet.OriginalNecklace.CrossedJoints
