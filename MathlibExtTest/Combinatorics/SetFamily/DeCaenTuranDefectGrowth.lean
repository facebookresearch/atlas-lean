/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SetFamily.DeCaenTuranDefectGrowth

@[expose] public section

namespace MathlibExt.Combinatorics.DeCaenTuranDefectGrowthWanted

open Pikhurko

/-- De Caen's conjecture is false. -/
example : ¬ conjecture := conjecture_refuted

/-- `above B V` keeps the elements of `V` above `max B`, and is computable. -/
example : above ({1, 3} : Finset ℕ) (Finset.range 6) = {4, 5} := by decide

/-- Edge case: every element is above the empty set. -/
example (V : Finset ℕ) : above ∅ V = V := by
  ext v
  simp [mem_above]

/-- A concrete Turán system: every `2`-subset of `{0, 1, 2}` contains `{0}` or `{1}`. -/
example : IsTuranSystemOn ({0, 1, 2} : Finset ℕ) 1 {{0}, {1}} := by
  have key : ∀ X ∈ ({0, 1, 2} : Finset ℕ).powersetCard 2,
      ∃ A ∈ ({{0}, {1}} : Finset (Finset ℕ)), A ⊆ X ∧ A.card = 1 := by
    decide
  exact fun X hX hc => key X (Finset.mem_powersetCard.mpr ⟨hX, hc⟩)

/-- A non-example: the pair `{1, 2}` contains no member of `{{0}}`. -/
example : ¬ IsTuranSystemOn ({0, 1, 2} : Finset ℕ) 1 {{0}} := by
  intro h
  obtain ⟨A, hA, hAX, -⟩ := h {1, 2} (by decide) (by decide)
  rw [Finset.mem_singleton] at hA
  subst hA
  exact absurd hAX (by decide)

/-- The family of all `r`-subsets is a Turán system of uniformity `r`. -/
example : IsTuranSystemOn (Finset.range 6) 3 ((Finset.range 6).powersetCard 3) :=
  isTuranSystemOn_powersetCard _ _

/-- The construction for `m = 4`: a Turán `(40, 16, 15)`-system with at most
`3 / 4 * C(40, 15)` members, three quarters of the complete `15`-graph. -/
example : ∃ G : Finset (Finset (Fin 40)), IsTuranSystemOn Finset.univ 15 G ∧
    (G.card : ℝ) ≤ 3 / 4 * (Nat.choose 40 15) := by
  obtain ⟨G, hG, hGc⟩ := exists_isTuranSystemOn (α := Fin 40) 4 Finset.univ
  refine ⟨G, hG, ?_⟩
  norm_num at hGc ⊢
  exact hGc

/-- The construction works on any finite subset of a linear order, here a set of naturals. -/
example (V : Finset ℕ) : ∃ G : Finset (Finset ℕ), IsTuranSystemOn V 31 G ∧
    (G.card : ℝ) ≤ 3 / 8 * (V.card.choose 31) := by
  obtain ⟨G, hG, hGc⟩ := exists_isTuranSystemOn 5 V
  refine ⟨G, hG, ?_⟩
  norm_num at hGc ⊢
  exact hGc

/-- The Turán number never exceeds the number of `k`-subsets. -/
example (n : ℕ) : turanNumber 3 n ≤ n.choose 3 := turanNumber_le_choose 3 n

/-- Edge case: the ratio is `0` below the uniformity, where `C(n, k) = 0`. -/
example : turanDensityRatio 3 2 = 0 := by
  simp [turanDensityRatio]

/-- The density bound is nontrivial from `k = 15` on: `π(K_{16}^{15}) ≥ 1 / 4`. -/
example : (1 : ℝ) / 4 ≤ turanDensityComplete 15 := by
  have h := one_sub_le_turanDensityComplete 4
  norm_num at h ⊢
  linarith

/-- The ratio bound holds for every `n ≥ k`; here `k = 31` and `n = 100`. -/
example : (5 : ℝ) / 8 ≤ turanDensityRatio 31 100 := by
  have h := one_sub_le_turanDensityRatio 5 100 (by norm_num)
  norm_num at h ⊢
  linarith

/-- De Caen's quantity `k * (1 - π(K_{k+1}^k))` is at most `12` at `k = 63`. -/
example : (63 : ℝ) * (1 - turanDensityComplete 63) ≤ 12 := by
  have h := mul_one_sub_turanDensityComplete_le 6
  norm_num at h
  exact h

end MathlibExt.Combinatorics.DeCaenTuranDefectGrowthWanted
