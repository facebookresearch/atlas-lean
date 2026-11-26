/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.ZeckendorfMaxBlockScaling

/-! # Tests for the geometric scaling of shifted maximal Zeckendorf blocks -/

open MetaMathlibExt

-- For `L = (2, 3, 0)`, the unit at index `0` is the proper block `[0, 0]` with entry `1 < 2`,
-- so it lies in `E*`.
example : (fun i => if i = 0 then 1 else 0) ∈ lStarCollection [2, 3, 0] := by
  refine ⟨fun h => by simpa using congrFun h 0, {(0, 0)}, by simp,
    Set.pairwiseDisjoint_singleton _ _, by simp [maxLStarBlock], fun i hi => ?_⟩
  have hi0 : i ≠ 0 := fun h => hi (0, 0) rfl (by simp [h])
  simp [hi0]

-- The maximal block `β̄₀` is not a member of `E*`: a block covering index `0` would have to end
-- with an entry below the maximal block's own entry there.
example : maxLStarBlock [2, 3, 0] 0 ∉ lStarCollection [2, 3, 0] := by
  rintro ⟨-, I, hI⟩
  by_cases hcov : ∃ p ∈ I, (0 : ℕ) ∈ Set.Icc p.1 p.2
  · obtain ⟨p, hp, hp0⟩ := hcov
    have hp1 : p.1 = 0 := Nat.le_zero.mp hp0.1
    have hlt := (hI.2.2.1 p hp).2
    rw [hp1] at hlt
    exact lt_irrefl _ hlt
  · have h0 := hI.2.2.2 0 fun p hp hmem => hcov ⟨p, hp, hmem⟩
    simp [maxLStarBlock] at h0

-- The scaling for the list `(2, 3, 0)` of the source's example, shifted by two indices; the
-- hypotheses on that list are decided.
example (L' : List ℕ) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0) {Q' : ℕ → ℝ}
    (hQ' : StrictAnti Q') (hQ'01 : ∀ n, 0 < Q' n ∧ Q' n < 1)
    (hbij' : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q' k) (lStarCollection L')
      (Set.Ioo 0 1)) :
    ∑' k, (maxLStarBlock [2, 3, 0] 2 k : ℝ) * Q' k =
      Q' 0 ^ 2 * ∑' k, (maxLStarBlock [2, 3, 0] 0 k : ℝ) * Q' k :=
  tsum_maxLStarBlock_mul_eq [2, 3, 0] L' (by decide) (by decide) (hL' := hL') (he' := he')
    hQ' hQ'01 hbij' 2

-- With `L = (1, 1)`, all of whose maximal-block entries are `1`, the scaling says that the tail
-- of the fundamental sequence after its first term is `Q₀` times the whole sum.
example (L' : List ℕ) (hL' : 2 ≤ L'.length) (he' : L'.getD 0 0 ≠ 0) {Q' : ℕ → ℝ}
    (hQ' : StrictAnti Q') (hQ'01 : ∀ n, 0 < Q' n ∧ Q' n < 1)
    (hbij' : Set.BijOn (fun ε : ℕ → ℕ => ∑' k, (ε k : ℝ) * Q' k) (lStarCollection L')
      (Set.Ioo 0 1)) :
    ∑' k, (if k < 1 then 0 else Q' k) = Q' 0 * ∑' k, Q' k := by
  have h := tsum_maxLStarBlock_mul_eq [1, 1] L' (by decide) (by decide) hL' he' hQ' hQ'01
    hbij' 1
  have h1 : ∀ s k, (maxLStarBlock [1, 1] s k : ℝ) = if k < s then 0 else 1 := by
    intro s k
    unfold maxLStarBlock
    split_ifs
    · simp
    · rcases Nat.mod_two_eq_zero_or_one (k - s) with h2 | h2 <;> simp [h2]
  simp only [h1, pow_one, Nat.not_lt_zero, ite_false, one_mul] at h
  simpa [ite_mul] using h
