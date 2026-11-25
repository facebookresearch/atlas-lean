/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.SubGaussian

/-!
# Hoeffding's inequality for averages of bounded independent variables

The form used throughout statistical learning theory: for independent real random variables
`Z₁, …, Zₙ` with values in `[a, b]`, the empirical average exceeds the average of the means by at
least `t ≥ 0` with probability at most `exp (-2 n t² / (b - a)²)`, falls below it by at least `t`
with the same bound, and deviates from it by at least `t` in absolute value with probability at
most twice that.

Mathlib proves Hoeffding's lemma (`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`) and the
Hoeffding inequality for sums of independent sub-Gaussian variables
(`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`); this file specializes
them to the normalization of averages with an almost sure range `[a, b]`.

## Main results

- `measureReal_avg_sub_ge_le`: one-sided bound (F. Bach, *Learning Theory from First
  Principles*, Proposition 1.2, extended to `[a, b]` as in the first bullet after Corollary 1.1).
- `measureReal_avg_sub_le_neg_le`: the lower tail, from the upper tail of the negated variables.
- `measureReal_abs_avg_sub_ge_le`: two-sided bound (Corollary 1.1 and the same bullet).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

namespace MathlibExt.Probability.HoeffdingBounded

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Hoeffding's inequality for averages** (one-sided). If `Z₁, …, Zₙ` are independent real
random variables with `Zᵢ ∈ [a, b]` almost surely, then for every `t ≥ 0`,
`P((1/n) ∑ Zᵢ - (1/n) ∑ E[Zᵢ] ≥ t) ≤ exp (-2 n t² / (b - a)²)`.

Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 1.2.1,
Proposition 1.2 (stated for `Zᵢ ∈ [0, 1]`) and the first bullet after Corollary 1.1 (the
range `[a, b]`); W. Hoeffding, J. Amer. Statist. Assoc. 58 (1963), Theorem 2.
When `a = b` the right-hand side is `exp 0 = 1` by Lean's convention `x / 0 = 0`. -/
theorem measureReal_avg_sub_ge_le {n : ℕ} {Z : Fin n → Ω → ℝ} (h_indep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ) {a b : ℝ}
    (hZ : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc a b) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]} ≤
      exp (-2 * n * t ^ 2 / (b - a) ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero, CharP.cast_eq_zero,
      zero_mul, zero_div, exp_zero]
    exact measureReal_le_one
  rcases eq_or_ne (b - a) 0 with hba | hba
  · rw [hba]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero, exp_zero]
    exact measureReal_le_one
  -- Centered variables and their sub-Gaussian parameter.
  set Y : Fin n → Ω → ℝ := fun i ω => Z i ω - μ[Z i] with hY
  set c : ℝ≥0 := (‖b - a‖₊ / 2) ^ 2 with hc
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)), HasSubgaussianMGF (Y i) c μ :=
    fun i _ => hasSubgaussianMGF_of_mem_Icc (hmeas i) (hZ i)
  have hindepY : iIndepFun Y μ :=
    h_indep.comp (fun (i : Fin n) (x : ℝ) => x - ∫ ω, Z i ω ∂μ)
      (fun i => measurable_id.sub_const _)
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have key := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindepY hsub
    (ε := n * t) (mul_nonneg hnpos.le ht)
  have hset : {ω | t ≤ (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]} =
      {ω | (n : ℝ) * t ≤ ∑ i, Y i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hY, Finset.sum_sub_distrib]
    rw [← mul_sub, one_div, ← div_eq_inv_mul, le_div_iff₀ hnpos, mul_comm]
  have hcsum : ((∑ _i : Fin n, c : ℝ≥0) : ℝ) = n * ((b - a) ^ 2 / 4) := by
    rw [NNReal.coe_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
    simp only [NNReal.coe_pow, NNReal.coe_div, coe_nnNorm, Real.norm_eq_abs, NNReal.coe_ofNat]
    rw [div_pow, sq_abs]
    norm_num
  rw [hset]
  refine key.trans (le_of_eq ?_)
  congr 1
  rw [hcsum]
  have hba2 : (b - a) ^ 2 ≠ 0 := pow_ne_zero 2 hba
  field_simp
  ring

/-- **Lower-tail Hoeffding inequality for averages.** If `Z₁, …, Zₙ` are independent real
random variables with `Zᵢ ∈ [a, b]` almost surely, then for every `t ≥ 0`,
`P((1/n) ∑ Zᵢ - (1/n) ∑ E[Zᵢ] ≤ -t) ≤ exp (-2 n t² / (b - a)²)`. When `a = b` the right-hand side
is `exp 0 = 1` by Lean's convention `x / 0 = 0`. When `n = 0` both sums are empty, so the average
is `0`, and the right-hand side is `exp 0 = 1`: the bound holds trivially.

Source: W. Hoeffding, J. Amer. Statist. Assoc. 58 (1963), Theorem 2, applied to `-Zᵢ`; F. Bach,
*Learning Theory from First Principles*, MIT Press (2024), Section 1.2.1, proof of Corollary 1.1. -/
theorem measureReal_avg_sub_le_neg_le {n : ℕ} {Z : Fin n → Ω → ℝ} (h_indep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ) {a b : ℝ}
    (hZ : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc a b) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i] ≤ -t} ≤
      exp (-2 * n * t ^ 2 / (b - a) ^ 2) := by
  have hindep' : iIndepFun (fun i ω => -Z i ω) μ :=
    h_indep.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hZ' : ∀ i, ∀ᵐ ω ∂μ, -Z i ω ∈ Set.Icc (-b) (-a) := fun i => by
    filter_upwards [hZ i] with ω h using ⟨neg_le_neg h.2, neg_le_neg h.1⟩
  have hlow := measureReal_avg_sub_ge_le hindep' (fun i => (hmeas i).neg) hZ' ht
  have hba : (-a - -b) ^ 2 = (b - a) ^ 2 := by ring
  rw [hba] at hlow
  refine le_of_eq_of_le (congrArg μ.real (Set.ext fun ω => ?_)) hlow
  simp only [Set.mem_ofPred_eq, integral_neg, Finset.sum_neg_distrib]
  constructor <;> intro h <;> linarith

/-- **Two-sided Hoeffding inequality for averages.** If `Z₁, …, Zₙ` are independent real
random variables with `Zᵢ ∈ [a, b]` almost surely, then for every `t ≥ 0`,
`P(|(1/n) ∑ Zᵢ - (1/n) ∑ E[Zᵢ]| ≥ t) ≤ 2 exp (-2 n t² / (b - a)²)`.

Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 1.2.1,
Corollary 1.1 (stated for `Zᵢ ∈ [0, 1]`) and the first bullet after it (the range `[a, b]`).
Proof: the one-sided bound for `Zᵢ` and for `-Zᵢ ∈ [-b, -a]`, and a union bound. -/
theorem measureReal_abs_avg_sub_ge_le {n : ℕ} {Z : Fin n → Ω → ℝ} (h_indep : iIndepFun Z μ)
    (hmeas : ∀ i, AEMeasurable (Z i) μ) {a b : ℝ}
    (hZ : ∀ i, ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc a b) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]|} ≤
      2 * exp (-2 * n * t ^ 2 / (b - a) ^ 2) := by
  have hup := measureReal_avg_sub_ge_le h_indep hmeas hZ ht
  have hlow := measureReal_avg_sub_le_neg_le h_indep hmeas hZ ht
  have hsub : {ω | t ≤ |(1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]|} ⊆
      {ω | t ≤ (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]} ∪
      {ω | (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i] ≤ -t} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    rcases le_abs'.mp hω with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc _ ≤ μ.real ({ω | t ≤ (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i]} ∪
      {ω | (1 / n : ℝ) * ∑ i, Z i ω - (1 / n : ℝ) * ∑ i, μ[Z i] ≤ -t}) :=
        measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add hup hlow
    _ = _ := by ring

end MathlibExt.Probability.HoeffdingBounded
