/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FiniteProbability

import Mathlib.Tactic

@[expose] public section



/-!
# The sample mean minimizes the sum of squared deviations

For real data `x : ι → ℝ` on a finite index type, the sum of squared deviations from a point `c`
splits as `∑ i, (x i - c) ^ 2 = ∑ i, (x i - x̄) ^ 2 + n (x̄ - c) ^ 2` with `x̄ = sampleMean x` and
`n = card ι`. Hence `x̄` minimizes `c ↦ ∑ i, (x i - c) ^ 2`, and for a nonempty sample it is the
only minimizer. No absolute-deviation minimizer claim is made here; an absolute-loss tie appears
only as a numeric contrast fixture in the tests.

For an empty sample every `c` gives the empty sum `0`, so every `c` is a minimizer; the
decomposition and the minimizing inequality still hold there (with Lean's junk value
`sampleMean x = 0`), and uniqueness needs `Nonempty ι`.

For data split into two groups (`Sum.elim x y` on `ι ⊕ κ`), the pooled mean is the
size-weighted average of the group means. It equals the unweighted average of the two group means
exactly when the groups have the same size or the same mean. For an empty group Lean's junk mean
`0` enters the unweighted average; that is the stated reading, not a data-validity claim.

These are algebraic identities about a fixed finite dataset. They carry no sampling, inferential
or causal guarantee.

## Main results

* `sum_sq_sub_eq_sum_sq_sub_sampleMean_add`: the decomposition above.
* `sum_sq_sub_sampleMean_le`, `sum_sq_sub_sampleMean_lt`: the mean minimizes, strictly against
  every other point of a nonempty sample.
* `forall_sum_sq_sub_le_iff_eq_sampleMean`, `existsUnique_forall_sum_sq_sub_le`: for a nonempty
  sample the minimizers are exactly the mean, and there is exactly one.
* `card_mul_sampleMean_sumElim`, `sampleMean_sumElim_eq_average_iff`: pooled versus group means.
-/

namespace MathlibExt.Probability.FiniteProbability

lemma sampleMean_eq_zero_of_card_eq_zero {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (h : Fintype.card ι = 0) : sampleMean x = 0 := by
  rw [sampleMean_eq_sum_div, h]
  have huniv : (Finset.univ : Finset ι) = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_univ, h]
  simp [huniv]

/-- **Squared deviations about a point.** For every `c`,
`∑ i, (x i - c) ^ 2 = ∑ i, (x i - x̄) ^ 2 + n (x̄ - c) ^ 2`, with `x̄` the sample mean and
`n = card ι`. Both sides are `0` for an empty sample. -/
theorem sum_sq_sub_eq_sum_sq_sub_sampleMean_add {ι : Type*} [Fintype ι] (x : ι → ℝ) (c : ℝ) :
    ∑ i, (x i - c) ^ 2 =
      ∑ i, (x i - sampleMean x) ^ 2 + Fintype.card ι * (sampleMean x - c) ^ 2 := by
  have hexpand : ∀ i, (x i - c) ^ 2 = (x i - sampleMean x) ^ 2
      + 2 * (sampleMean x - c) * (x i - sampleMean x) + (sampleMean x - c) ^ 2 := by
    intro i; ring
  simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum, sum_sub_sampleMean, mul_zero,
    add_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The sample mean minimizes the sum of squared deviations. -/
theorem sum_sq_sub_sampleMean_le {ι : Type*} [Fintype ι] (x : ι → ℝ) (c : ℝ) :
    ∑ i, (x i - sampleMean x) ^ 2 ≤ ∑ i, (x i - c) ^ 2 := by
  rw [sum_sq_sub_eq_sum_sq_sub_sampleMean_add x c]
  have h : (0:ℝ) ≤ Fintype.card ι * (sampleMean x - c) ^ 2 := by positivity
  exact le_add_of_nonneg_right h

/-- For a nonempty sample, every point other than the sample mean has a strictly larger sum of
squared deviations. -/
theorem sum_sq_sub_sampleMean_lt {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) {c : ℝ}
    (hc : c ≠ sampleMean x) :
    ∑ i, (x i - sampleMean x) ^ 2 < ∑ i, (x i - c) ^ 2 := by
  rw [sum_sq_sub_eq_sum_sq_sub_sampleMean_add x c]
  have hcard : (0:ℝ) < Fintype.card ι := by
    have h : 0 < Fintype.card ι := Fintype.card_pos
    exact_mod_cast h
  have hsq : (0:ℝ) < (sampleMean x - c) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hc))
  have hpos : (0:ℝ) < Fintype.card ι * (sampleMean x - c) ^ 2 := mul_pos hcard hsq
  linarith

/-- **The mean is the unique least-squares location.** For a nonempty sample, `c` minimizes the
sum of squared deviations if and only if `c` is the sample mean. -/
theorem forall_sum_sq_sub_le_iff_eq_sampleMean {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (c : ℝ) :
    (∀ d, ∑ i, (x i - c) ^ 2 ≤ ∑ i, (x i - d) ^ 2) ↔ c = sampleMean x := by
  constructor
  · intro h
    by_contra hne
    have hlt := sum_sq_sub_sampleMean_lt x hne
    have hle := h (sampleMean x)
    linarith
  · intro h
    rw [h]
    exact fun d => sum_sq_sub_sampleMean_le x d

/-- For a nonempty sample, the sum of squared deviations has exactly one minimizer. -/
theorem existsUnique_forall_sum_sq_sub_le {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    ∃! c : ℝ, ∀ d, ∑ i, (x i - c) ^ 2 ≤ ∑ i, (x i - d) ^ 2 := by
  refine ⟨sampleMean x, fun d => sum_sq_sub_sampleMean_le x d, ?_⟩
  intro y hy
  exact (forall_sum_sq_sub_le_iff_eq_sampleMean x y).mp hy

/-- **Pooled mean of two groups.** `(m + n) * mean (x, y) = m * mean x + n * mean y` with
`m = card ι` and `n = card κ`; no group needs to be nonempty. -/
theorem card_mul_sampleMean_sumElim {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → ℝ)
    (y : κ → ℝ) :
    ((Fintype.card ι : ℝ) + Fintype.card κ) * sampleMean (Sum.elim x y) =
      Fintype.card ι * sampleMean x + Fintype.card κ * sampleMean y := by
  have h1 := card_mul_sampleMean x
  have h2 := card_mul_sampleMean y
  have h3 := card_mul_sampleMean (Sum.elim x y)
  rw [Fintype.card_sum, Fintype.sum_sum_type] at h3
  simp only [Sum.elim_inl, Sum.elim_inr] at h3
  push_cast at h3
  linear_combination h3 - h1 - h2

/-- **Unweighted group averages.** The pooled mean of two groups equals the unweighted average of
the two group means if and only if the groups have the same size or the same mean. An empty group
contributes Lean's junk mean `0` to the unweighted average. -/
theorem sampleMean_sumElim_eq_average_iff {ι κ : Type*} [Fintype ι] [Fintype κ] (x : ι → ℝ)
    (y : κ → ℝ) :
    sampleMean (Sum.elim x y) = (sampleMean x + sampleMean y) / 2 ↔
      Fintype.card ι = Fintype.card κ ∨ sampleMean x = sampleMean y := by
  constructor
  · intro h
    have hpool := card_mul_sampleMean_sumElim x y
    rw [h] at hpool
    have hmul : ((Fintype.card ι : ℝ) - Fintype.card κ) * (sampleMean x - sampleMean y) = 0 := by
      linear_combination -2 * hpool
    rcases mul_eq_zero.mp hmul with hmn | hab
    · left
      have hcast : (Fintype.card ι : ℝ) = Fintype.card κ := sub_eq_zero.mp hmn
      exact_mod_cast hcast
    · right
      exact sub_eq_zero.mp hab
  · rintro (hmn | hab)
    · have hcast : (Fintype.card ι : ℝ) = Fintype.card κ := by exact_mod_cast hmn
      have hpool := card_mul_sampleMean_sumElim x y
      by_cases hm : Fintype.card ι = 0
      · have hn : Fintype.card κ = 0 := by rw [← hmn, hm]
        have hp0 : sampleMean (Sum.elim x y) = 0 :=
          sampleMean_eq_zero_of_card_eq_zero _ (by rw [Fintype.card_sum, hm, hn])
        have ha0 : sampleMean x = 0 := sampleMean_eq_zero_of_card_eq_zero _ hm
        have hb0 : sampleMean y = 0 := sampleMean_eq_zero_of_card_eq_zero _ hn
        rw [hp0, ha0, hb0]
        norm_num
      · have hm' : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hm
        have hκ : (Fintype.card κ : ℝ) ≠ 0 := by rw [← hcast]; exact hm'
        rw [hcast] at hpool
        have hfactor : (Fintype.card κ : ℝ) * (2 * sampleMean (Sum.elim x y))
            = (Fintype.card κ : ℝ) * (sampleMean x + sampleMean y) := by
          linear_combination hpool
        have h2p := mul_left_cancel₀ hκ hfactor
        linarith
    · have hpool := card_mul_sampleMean_sumElim x y
      rw [hab] at hpool
      by_cases hsum : (Fintype.card ι : ℝ) + Fintype.card κ = 0
      · have hm' : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
        have hn' : (0:ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
        have ⟨hm0, hn0⟩ := (add_eq_zero_iff_of_nonneg hm' hn').mp hsum
        have hm : Fintype.card ι = 0 := by exact_mod_cast hm0
        have hn : Fintype.card κ = 0 := by exact_mod_cast hn0
        have hp0 : sampleMean (Sum.elim x y) = 0 :=
          sampleMean_eq_zero_of_card_eq_zero _ (by rw [Fintype.card_sum, hm, hn])
        have ha0 : sampleMean x = 0 := sampleMean_eq_zero_of_card_eq_zero _ hm
        have hb0 : sampleMean y = 0 := by rw [← hab]; exact ha0
        rw [hp0, ha0, hb0]
        norm_num
      · have hfactor : ((Fintype.card ι : ℝ) + Fintype.card κ) * sampleMean (Sum.elim x y)
            = ((Fintype.card ι : ℝ) + Fintype.card κ) * sampleMean y := by
          linear_combination hpool
        have hp := mul_left_cancel₀ hsum hfactor
        rw [hp, hab]
        ring

end MathlibExt.Probability.FiniteProbability
