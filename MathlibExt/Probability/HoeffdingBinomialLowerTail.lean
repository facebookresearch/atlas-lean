/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

open scoped BigOperators

namespace ProbabilityTheory

@[expose] public section

/-- **Hoeffding lower-tail bound for Bernoulli sums.** Let $X_0, \dots, X_{n-1}$ be independent
real random variables on a probability space, each almost everywhere measurable, almost surely
equal to $0$ or $1$, and with expectation $p$, and let $\varepsilon > 0$. Then the probability
that $X_0 + \dots + X_{n-1} \le n(p - \varepsilon)$ is at most $e^{-2 \varepsilon^2 n}$.

Proves `Wanted` entry `hoeffding_binomial_lower_tail`.

Source: Griffiths JIS VOL16 Eq. `hoeff`, source lines 167-191,
`https://cs.uwaterloo.ca/journals/JIS/VOL16/Griffiths/griffiths22.tex`,
source object `9d2fd3574fc15b79a0e00894b68d9608850dec38628c212a69d57f903588a30c`
(JIS concept `jis_grounded_4cd778f9d6394cee44270586`).
-/
theorem hoeffding_binomial_lower_tail {Ω : Type*}
    [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (p ε : ℝ)
    (h_indep : ProbabilityTheory.iIndepFun X μ)
    (hmeas : ∀ i, AEMeasurable (X i) μ)
    (hBernoulli : ∀ i, ∀ᵐ ω ∂μ, X i ω = 0 ∨ X i ω = 1)
    (hexp : ∀ i, ∫ x, X i x ∂μ = p)
    (hε : 0 < ε) :
    μ.real {ω | (∑ i, X i ω) ≤ (n : ℝ) * (p - ε)} ≤
      Real.exp (-2 * ε ^ 2 * (n : ℝ)) := by
  -- Each `X i` is integrable since it is a.e. bounded.
  have hXint : ∀ i, MeasureTheory.Integrable (X i) μ := by
    intro i
    refine MeasureTheory.Integrable.of_bound ((hmeas i).aestronglyMeasurable) 1 ?_
    filter_upwards [hBernoulli i] with ω hω
    rcases hω with h | h <;> rw [h] <;> simp
  -- Centered variables have mean zero.
  have hYint : ∀ i, ∫ ω, (X i ω - p) ∂μ = 0 := by
    intro i
    have h2 : ∫ ω, (X i ω - p) ∂μ
        = (∫ ω, X i ω ∂μ) - ∫ _, p ∂μ :=
      MeasureTheory.integral_sub (hXint i) (MeasureTheory.integrable_const p)
    rw [h2, MeasureTheory.integral_const, MeasureTheory.probReal_univ, one_smul, hexp i, sub_self]
  -- Centered variables lie in `[−p, 1 − p]`.
  have hYIcc : ∀ i, ∀ᵐ ω ∂μ, X i ω - p ∈ Set.Icc (-p) (1 - p) := by
    intro i
    filter_upwards [hBernoulli i] with ω hω
    have hle : -p ≤ 1 - p := by linarith
    rcases hω with h | h
    · rw [h, zero_sub]
      exact Set.left_mem_Icc.mpr hle
    · rw [h]
      exact Set.right_mem_Icc.mpr hle
  -- Hoeffding's lemma: each centered variable is subgaussian.
  have hsub : ∀ i, HasSubgaussianMGF (fun ω => X i ω - p)
      ((‖(1 - p - -p)‖₊ / 2) ^ 2) μ :=
    fun i => hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      ((hmeas i).sub_const p) (hYIcc i) (hYint i)
  -- The subgaussian parameter equals `1 / 4`.
  have hc4 : (‖(1 - p - -p)‖₊ / 2) ^ 2 = (1 / 4 : NNReal) := by
    have h1 : (1 - p - -p : ℝ) = 1 := by ring
    rw [h1, nnnorm_one]
    norm_num
  have hsub4 : ∀ i, HasSubgaussianMGF (fun ω => -(X i ω - p)) (1 / 4 : NNReal) μ := by
    intro i
    rw [hc4.symm]
    exact (hsub i).neg
  -- Independence is preserved by centering and negation.
  have hindepY : iIndepFun (fun i ω => X i ω - p) μ :=
    h_indep.comp (fun _ x => x - p) (fun _ => measurable_sub_const p)
  have hindepZ : iIndepFun (fun i ω => -(X i ω - p)) μ :=
    hindepY.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  -- The sum of subgaussian parameters is `n / 4`.
  have hcsum : ((∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 / 4 : NNReal) : NNReal) : ℝ)
      = (n : ℝ) / 4 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  -- The negated sum in terms of the original sum.
  have hsum : ∀ ω, (∑ i, (-(X i ω - p))) = (n : ℝ) * p - (∑ i, X i ω) := by
    intro ω
    have h1 : (∑ i, (-(X i ω - p))) = (∑ _i ∈ (Finset.univ : Finset (Fin n)), p)
        - (∑ i, X i ω) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- Empty sum: both sides equal `1`.
    have hmem : ∀ ω, ω ∈ {ω | (∑ i, X i ω) ≤ ((0 : ℕ) : ℝ) * (p - ε)} := fun ω => by
      simp
    rw [Set.eq_univ_of_forall hmem, MeasureTheory.probReal_univ]
    simp
  · -- Chernoff bound applied to the negated centered sum.
    have hpos : (0 : ℝ) ≤ (n : ℝ) * ε :=
      mul_nonneg (Nat.cast_nonneg _) hε.le
    have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i ω => -(X i ω - p)) (c := fun _ => (1 / 4 : NNReal))
      (s := Finset.univ) (ε := (n : ℝ) * ε) hindepZ (fun i _ => hsub4 i) hpos
    rw [hcsum] at htail
    have hexp_eq : -((n : ℝ) * ε) ^ 2 / (2 * ((n : ℝ) / 4))
        = -2 * ε ^ 2 * (n : ℝ) := by
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
      field_simp
      ring
    rw [hexp_eq] at htail
    have hev : {ω | (∑ i, X i ω) ≤ (n : ℝ) * (p - ε)} =
        {ω | (n : ℝ) * ε ≤ ∑ i, (-(X i ω - p))} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hsum ω]
      have hnp : (n : ℝ) * (p - ε) = (n : ℝ) * p - (n : ℝ) * ε := by ring
      constructor <;> intro h <;> linarith
    rw [hev]
    exact htail

end

end ProbabilityTheory
