/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of the weighted-sum proof are adapted from:

`Mathlib/Probability/Distributions/Binomial.lean` (Mathlib):
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Yaël Dillies, Etienne Marion
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.SplitIfs
public import Domains.Biology.StatisticalGenetics.LiMantelSegregationLiMantelTendstoAe

/-!
# The zero-truncated binomial law and its mean

`truncBinom` defines the zero-truncated binomial probabilities. The theorem
`truncBinom_law_mean` proves their nonnegativity, normalization, and mean.

Sources: C. C. Li and N. Mantel, "A simple method of estimating the segregation ratio under
complete ascertainment", Am. J. Hum. Genet. 20 (1968) 61–81; R. A. Fisher, "The effect of
methods of ascertainment upon the estimation of frequencies", Ann. Eugen. 6 (1934) 13–25.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted

open Finset

private lemma binom_sum (s : ℕ) (p : ℝ) :
    ∑ k ∈ range (s + 1), (s.choose k : ℝ) * p ^ k * (1 - p) ^ (s - k) = 1 := by
  calc
    _ = ∑ k ∈ range (s + 1), p ^ k * (1 - p) ^ (s - k) * (s.choose k : ℝ) := by
      apply sum_congr rfl
      intro k _
      ring
    _ = (p + (1 - p)) ^ s := (add_pow p (1 - p) s).symm
    _ = 1 := by simp

private lemma binom_shifted_mean (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), ((k + 1 : ℕ) : ℝ) * ((n + 1).choose (k + 1) : ℝ) *
      p ^ (k + 1) * (1 - p) ^ (n + 1 - (k + 1)) = (n + 1 : ℕ) * p := by
  calc
    _ = ∑ k ∈ range (n + 1), ((n + 1 : ℕ) : ℝ) * p *
        ((n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)) := by
      apply sum_congr rfl
      intro k _
      have hc : ((k + 1 : ℕ) : ℝ) * ((n + 1).choose (k + 1) : ℝ) =
          ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) := by
        exact_mod_cast (by simpa [mul_comm] using (Nat.add_one_mul_choose_eq n k).symm)
      rw [hc, Nat.add_sub_add_right, pow_succ]
      ring
    _ = ((n + 1 : ℕ) : ℝ) * p *
        ∑ k ∈ range (n + 1), (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) :=
      (mul_sum _ _ _).symm
    _ = (n + 1 : ℕ) * p := by rw [binom_sum, mul_one]

/-- **The zero-truncated binomial law and its mean** (Fisher 1934): for `s ≥ 1` and
`0 < p < 1`, the truncated probabilities are nonnegative, sum to `1` over `k ∈ {0, …, s}`, and
have mean `s p / (1 - (1 - p)ˢ)`.

Sources: Fisher (1934); Li and Mantel (1968). -/
public theorem truncBinom_law_mean (s : ℕ) (hs : 1 ≤ s) (p : ℝ) (hp₀ : 0 < p)
    (hp₁ : p < 1) :
    (∀ k, 0 ≤ truncBinom s p k) ∧
      ∑ k ∈ range (s + 1), truncBinom s p k = 1 ∧
      ∑ k ∈ range (s + 1), (k : ℝ) * truncBinom s p k = s * p / (1 - (1 - p) ^ s)
    := by
  have hq₀ : 0 ≤ 1 - p := sub_nonneg.mpr hp₁.le
  have hq₁ : 1 - p < 1 := sub_lt_self 1 hp₀
  have hd : 0 < 1 - (1 - p) ^ s :=
    sub_pos.mpr (pow_lt_one₀ hq₀ hq₁ (by omega))
  refine ⟨?_, ?_, ?_⟩
  · intro k
    unfold truncBinom
    split_ifs
    · exact div_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp₀.le _))
        (pow_nonneg hq₀ _)) hd.le
    · exact le_rfl
  · rw [sum_range_succ']
    have ht : ∑ k ∈ range s, truncBinom s p (k + 1) =
        (∑ k ∈ range s, (s.choose (k + 1) : ℝ) * p ^ (k + 1) *
          (1 - p) ^ (s - (k + 1))) / (1 - (1 - p) ^ s) := by
      rw [sum_div]
      apply sum_congr rfl
      intro k hk
      have hk' : 1 ≤ k + 1 ∧ k + 1 ≤ s := ⟨by omega, by simpa using mem_range.mp hk⟩
      simp [truncBinom, hk']
    rw [ht]
    have hsum := binom_sum s p
    rw [sum_range_succ'] at hsum
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero] at hsum
    have hnum : (∑ k ∈ range s, (s.choose (k + 1) : ℝ) * p ^ (k + 1) *
        (1 - p) ^ (s - (k + 1))) = 1 - (1 - p) ^ s := by linarith
    simp [hnum, truncBinom, ne_of_gt hd]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
    rw [sum_range_succ']
    have ht : ∑ k ∈ range (n + 1), ((k + 1 : ℕ) : ℝ) * truncBinom (n + 1) p (k + 1) =
        (∑ k ∈ range (n + 1), ((k + 1 : ℕ) : ℝ) * ((n + 1).choose (k + 1) : ℝ) *
          p ^ (k + 1) * (1 - p) ^ (n + 1 - (k + 1))) / (1 - (1 - p) ^ (n + 1)) := by
      rw [sum_div]
      apply sum_congr rfl
      intro k hk
      have hk' : 1 ≤ k + 1 ∧ k + 1 ≤ n + 1 := ⟨by omega, by simpa using mem_range.mp hk⟩
      simp [truncBinom, hk', mul_div_assoc, mul_assoc]
    simpa using ht.trans (congrArg (fun x : ℝ => x / (1 - (1 - p) ^ (n + 1)))
      (binom_shifted_mean n p))

end WantedExt.Biology.StatisticalGenetics.LiMantelSegregationWanted
