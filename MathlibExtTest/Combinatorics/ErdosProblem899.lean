/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.ErdosProblem899
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Counting-window tests for Ruzsa's theorem -/

open Filter
open scoped Pointwise Topology

namespace MathlibExt.Combinatorics.ErdosProblem899Wanted

-- For squares, at most the first ⌊√N⌋ positive roots contribute to the counting window.
example :
    let A := Set.range (fun k : ℕ ↦ k ^ 2)
    atTop.limsup (fun n ↦ (((A - A) ∩ Set.Icc 1 n).ncard : EReal) /
      ((A ∩ Set.Icc 1 n).ncard : EReal)) = ⊤ := by
  intro A
  apply conjecture_holds
  · exact Set.infinite_iff_exists_gt.mpr fun n ↦
      ⟨(n + 1) ^ 2, ⟨n + 1, rfl⟩, by nlinarith⟩
  have hcount (n : ℕ) : (A ∩ Set.Icc 1 n).ncard ≤ n.sqrt := by
    have hsub : A ∩ Set.Icc 1 n ⊆ (fun k : ℕ ↦ k ^ 2) '' Set.Icc 1 n.sqrt := by
      rintro _ ⟨⟨k, rfl⟩, hlo, hhi⟩
      refine ⟨k, ⟨?_, Nat.le_sqrt'.mpr hhi⟩, rfl⟩
      by_contra! hk
      simp [show k = 0 by omega] at hlo
    exact (Set.ncard_le_ncard hsub ((Set.finite_Icc ..).image _)).trans
      (Set.ncard_image_le (Set.finite_Icc ..) |>.trans (by simp))
  apply squeeze_zero (fun n ↦ by positivity) (g := fun n : ℕ ↦ (Real.sqrt n)⁻¹)
  · intro n
    rw [← Real.sqrt_div_self]
    exact div_le_div_of_nonneg_right ((by exact_mod_cast hcount n : _ ≤ (n.sqrt : ℝ)).trans
      Real.nat_sqrt_le_real_sqrt) (by positivity)
  · exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

-- The difference can be visible even when both of its witnesses lie beyond the cutoff.
example :
    let A : Set ℕ := {10, 13}
    ((A - A) ∩ Set.Icc 1 3).ncard = 1 ∧
      (((A - A) ∩ Set.Icc 1 3).ncard : EReal) / ((A ∩ Set.Icc 1 3).ncard : EReal) = 0 := by
  intro A
  have hdiff : (A - A) ∩ Set.Icc 1 3 = {3} := by
    ext x
    simp only [A, Set.mem_inter_iff, Set.mem_sub, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_Icc]
    constructor
    · rintro ⟨⟨a, ha, b, hb, rfl⟩, hlo, hhi⟩
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega
    · rintro rfl
      exact ⟨⟨13, Or.inr rfl, 10, Or.inl rfl, rfl⟩, by decide, le_rfl⟩
  have hempty : A ∩ Set.Icc 1 3 = ∅ := by
    ext x
    simp only [A, Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    omega
  simp [hdiff, hempty]

end MathlibExt.Combinatorics.ErdosProblem899Wanted
