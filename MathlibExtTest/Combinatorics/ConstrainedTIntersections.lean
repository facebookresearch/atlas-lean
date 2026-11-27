/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ConstrainedTIntersections
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for constrained T intersections

The four-point configuration uses a horizontal stem and a diagonally upward stem.
A coincident crossbar gives an infinite intersection.
-/

namespace MetaMathlibExt.ConstrainedTIntersectionsTest

private noncomputable def tCut (c : ℝ × ℝ) (θ : ℝ) : Set (ℝ × ℝ) :=
  Set.range (fun s : ℝ => c + s • (-Real.sin θ, Real.cos θ)) ∪
    (fun s : ℝ => c + s • (Real.cos θ, Real.sin θ)) '' Set.Ici 0

private theorem mem_horizontal {x y : ℝ} :
    (x, y) ∈ tCut (0, 0) 0 ↔ x = 0 ∨ 0 ≤ x ∧ y = 0 := by
  simp [tCut, Prod.ext_iff, eq_comm]

private theorem mem_diagonal {x y : ℝ} :
    (x, y) ∈ tCut (2, -1) (Real.pi - Real.pi / 4) ↔ y = x - 3 ∨ y = 1 - x ∧ x ≤ 2 := by
  let q := Real.sqrt 2 / 2
  have hq : 0 < q := by positivity
  simp only [tCut, Set.mem_union, Set.mem_range, Set.mem_image, Set.mem_Ici, Real.sin_pi_sub,
    Real.cos_pi_sub, Real.sin_pi_div_four, Real.cos_pi_div_four, Prod.ext_iff]
  change ((∃ a : ℝ, 2 + a * -q = x ∧ -1 + a * -q = y) ∨
    (∃ a : ℝ, 0 ≤ a ∧ 2 + a * -q = x ∧ -1 + a * q = y)) ↔ _
  constructor
  · rintro (⟨a, hx, hy⟩ | ⟨a, ha, hx, hy⟩)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨by linarith, by linarith [mul_nonneg ha hq.le]⟩
  · rintro (hy | ⟨hy, hx⟩)
    · refine Or.inl ⟨(2 - x) / q, ?_, ?_⟩ <;>
        rw [mul_neg, div_mul_cancel₀ _ hq.ne'] <;> linarith
    · refine Or.inr ⟨(2 - x) / q, div_nonneg (sub_nonneg.mpr hx) hq.le, ?_, ?_⟩
      · rw [mul_neg, div_mul_cancel₀ _ hq.ne']
        linarith
      · rw [div_mul_cancel₀ _ hq.ne']
        linarith

private theorem four_crossings :
    (tCut (0, 0) 0 ∩ tCut (2, -1) (Real.pi - Real.pi / 4)).ncard = 4 := by
  have hpoints : tCut (0, 0) 0 ∩ tCut (2, -1) (Real.pi - Real.pi / 4) =
      {(0, -3), (3, 0), (0, 1), (1, 0)} := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, mem_horizontal, mem_diagonal, Set.mem_insert_iff,
      Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hx | ⟨_, hy⟩, hbar | ⟨hstem, _⟩⟩
      · exact Or.inl ⟨hx, by linarith⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hx, by linarith⟩))
      · exact Or.inr (Or.inl ⟨by linarith, hy⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨by linarith, hy⟩))
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
  rw [hpoints]
  norm_num [Set.ncard_insert_of_notMem, Prod.ext_iff]

example : Real.cos (0 - (Real.pi - Real.pi / 4)) < 0 :=
  cos_sub_neg_of_tbar_inter_ncard_four (0, 0) (2, -1) 0 (Real.pi - Real.pi / 4) four_crossings

example : (tCut (0, 0) 0 ∩ tCut (0, 1) 0).ncard = 0 := by
  apply Set.Infinite.ncard
  have hline : (Set.range fun s : ℝ => ((0 : ℝ), s)).Infinite :=
    Set.infinite_range_of_injective fun _ _ h => congrArg Prod.snd h
  refine hline.mono ?_
  rintro _ ⟨s, rfl⟩
  exact ⟨Or.inl ⟨s, by simp⟩, Or.inl ⟨s - 1, by simp⟩⟩

end MetaMathlibExt.ConstrainedTIntersectionsTest
