/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Kernel density estimator: expectation and variance at a fixed bandwidth

For a kernel `K : ℝ → ℝ`, a bandwidth `h` and a sample `x : Fin n → ℝ`, the kernel density
estimator is `kde K h x t = (n * h)⁻¹ * ∑ i, K ((t - x i) / h)`.

For a sample whose coordinates each have law `f(x) dx`, with `f` measurable, nonnegative and
bounded above by `B`, `n ≥ 1` and `h > 0`:

* `ProbabilityTheory.integral_kde_eq`: for an integrable measurable kernel,
  `E[kde K h X t] = ∫ K(u) f(t - h u) du`. Independence is not used.
* `ProbabilityTheory.variance_kde_le`: for independent coordinates and a measurable kernel with
  `∫ K² < ∞`, `Var(kde K h X t) ≤ B ∫ K² / (n h)`.

Both statements are at fixed `n`, `h` and `t`. Bandwidth asymptotics (bias tending to zero,
mean-squared-error consistency), which need continuity of `f` at `t`, are not covered here.

## Source

The definition `kde` is copied from `Lean-MoDS/StatsMLlib` (commit `edcd3104`),
`StatsMLlib/Statistics/DensityEstimation/KernelDensity.lean`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- The kernel density estimator with kernel `K` and bandwidth `h` at the sample `x`. -/
noncomputable def kde (K : ℝ → ℝ) (h : ℝ) {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : ℝ :=
  ((n : ℝ) * h)⁻¹ * ∑ i, K ((t - x i) / h)

private lemma integrable_withDensity_ofReal {f g : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hfg : Integrable fun x => f x * g x) :
    Integrable g (volume.withDensity fun x => ENNReal.ofReal (f x)) := by
  rw [integrable_withDensity_iff (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine hfg.congr (ae_of_all _ fun x => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (hf_nonneg x), mul_comm]

private lemma integral_withDensity_ofReal {f : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) (g : ℝ → ℝ) :
    ∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) = ∫ x, f x * g x := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf_nonneg _), smul_eq_mul]

private lemma comp_sub_div_eq (g : ℝ → ℝ) (h t : ℝ) :
    (fun x => g ((t - x) / h)) = fun x => g ((x - t) / -h) := by
  ext x
  rw [div_neg, ← neg_div, neg_sub]

private lemma integrable_comp_sub_div {g : ℝ → ℝ} (hg : Integrable g) {h : ℝ} (hh : 0 < h)
    (t : ℝ) : Integrable fun x => g ((t - x) / h) := by
  rw [comp_sub_div_eq]
  exact ((measurePreserving_sub_right volume t).integrable_comp_emb
    (MeasurableEquiv.subRight t).measurableEmbedding).mpr (hg.comp_div (neg_ne_zero.mpr hh.ne'))

private lemma integral_comp_sub_div (g : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ∫ x, g ((t - x) / h) = h * ∫ u, g u := by
  rw [comp_sub_div_eq, (measurePreserving_sub_right volume t).integral_comp
      (MeasurableEquiv.subRight t).measurableEmbedding (fun y => g (y / -h)),
    Measure.integral_comp_div, abs_neg, abs_of_pos hh, smul_eq_mul]

private lemma integrable_mul_of_le {f g : ℝ → ℝ} (hf_meas : Measurable f)
    (hf_nonneg : ∀ x, 0 ≤ f x) {B : ℝ} (hf_le : ∀ x, f x ≤ B) (hg : Integrable g) :
    Integrable fun x => f x * g x :=
  (hg.norm.const_mul B).mono' (hf_meas.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_of_nonneg (hf_nonneg x)]
      exact mul_le_mul_of_nonneg_right (hf_le x) (norm_nonneg _))

/-- **Expectation of the kernel density estimator.** If `X 0, …, X (n-1)` (`n ≥ 1`) each have
law `f(x) dx` for a measurable, nonnegative density `f` bounded above by `B`, and `K` is a
measurable integrable kernel, then for `h > 0` and every `t`,
`E[kde K h X t] = ∫ K(u) f(t - h u) du`. Independence is not needed, and neither are
continuity of `f`, `K ≥ 0` or `∫ K = 1`. -/
theorem integral_kde_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    {f : ℝ → ℝ} (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    {B : ℝ} (hf_le : ∀ x, f x ≤ B)
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P)
    {K : ℝ → ℝ} (hK_meas : Measurable K) (hK_int : Integrable K)
    {h : ℝ} (hh : 0 < h) (t : ℝ) :
    ∫ ω, kde K h (fun i => X i ω) t ∂P = ∫ u, K u * f (t - h * u) := by
  have hφ_meas : Measurable fun x => K ((t - x) / h) := by fun_prop
  have hfφ : Integrable fun x => f x * K ((t - x) / h) :=
    integrable_mul_of_le hf_meas hf_nonneg hf_le (integrable_comp_sub_div hK_int hh t)
  have h_int : ∀ i, Integrable (fun ω => K ((t - X i ω) / h)) P := fun i =>
    (hX i).integrable_comp (integrable_withDensity_ofReal hf_meas hf_nonneg hfφ)
  have h_term : ∀ i, ∫ ω, K ((t - X i ω) / h) ∂P = h * ∫ u, K u * f (t - h * u) := by
    intro i
    rw [← integral_comp_sub_div (fun u => K u * f (t - h * u)) hh t]
    refine ((hX i).integral_comp hφ_meas.aestronglyMeasurable).trans ?_
    rw [integral_withDensity_ofReal hf_meas hf_nonneg]
    congr 1
    ext x
    rw [mul_div_cancel₀ _ hh.ne', sub_sub_cancel, mul_comm]
  simp only [kde]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => h_int i]
  simp only [h_term, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

/-- **Variance bound for the kernel density estimator.** If `X 0, …, X (n-1)` (`n ≥ 1`) are
independent, each with law `f(x) dx` for a measurable nonnegative density `f ≤ B`, and `K` is a
measurable kernel with `∫ K² < ∞`, then for `h > 0` and every `t`,
`Var(kde K h X t) ≤ B ∫ K² / (n h)`. -/
theorem variance_kde_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X P)
    {f : ℝ → ℝ} (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    {B : ℝ} (hf_le : ∀ x, f x ≤ B)
    (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x => ENNReal.ofReal (f x)) P)
    {K : ℝ → ℝ} (hK_meas : Measurable K) (hK_sq : Integrable fun u => K u ^ 2)
    {h : ℝ} (hh : 0 < h) (t : ℝ) :
    Var[fun ω => kde K h (fun i => X i ω) t; P] ≤ B * (∫ u, K u ^ 2) / (n * h) := by
  set φ : ℝ → ℝ := fun x => K ((t - x) / h) with hφ
  have hφ_meas : Measurable φ := by fun_prop
  have hφ2_meas : Measurable fun x => φ x ^ 2 := by fun_prop
  have hfφ2 : Integrable fun x => f x * φ x ^ 2 :=
    integrable_mul_of_le hf_meas hf_nonneg hf_le (integrable_comp_sub_div hK_sq hh t)
  have hY_aesm : ∀ i, AEStronglyMeasurable (φ ∘ X i) P := fun i =>
    (hφ_meas.comp_aemeasurable (hX i).aemeasurable).aestronglyMeasurable
  have hY_memLp : ∀ i, MemLp (φ ∘ X i) 2 P := fun i =>
    (memLp_two_iff_integrable_sq (hY_aesm i)).mpr
      ((hX i).integrable_comp (f := fun x => φ x ^ 2)
        (integrable_withDensity_ofReal hf_meas hf_nonneg hfφ2))
  have hY_indep : iIndepFun (fun i => φ ∘ X i) P := hindep.comp (fun _ => φ) fun _ => hφ_meas
  have h_term : ∀ i, Var[φ ∘ X i; P] ≤ B * (h * ∫ u, K u ^ 2) := by
    intro i
    calc Var[φ ∘ X i; P] ≤ ∫ ω, ((φ ∘ X i) ^ 2) ω ∂P := variance_le_expectation_sq (hY_aesm i)
      _ = ∫ x, φ x ^ 2 ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) :=
        (hX i).integral_comp (f := fun x => φ x ^ 2) hφ2_meas.aestronglyMeasurable
      _ = ∫ x, f x * φ x ^ 2 := integral_withDensity_ofReal hf_meas hf_nonneg _
      _ ≤ ∫ x, B * φ x ^ 2 :=
        integral_mono hfφ2 ((integrable_comp_sub_div hK_sq hh t).const_mul B)
          fun x => mul_le_mul_of_nonneg_right (hf_le x) (sq_nonneg _)
      _ = B * (h * ∫ u, K u ^ 2) := by
        rw [integral_const_mul, hφ, integral_comp_sub_div (fun u => K u ^ 2) hh t]
  have hkde : (fun ω => kde K h (fun i => X i ω) t) =
      fun ω => ((n : ℝ) * h)⁻¹ * (∑ i, φ ∘ X i) ω := by
    ext ω
    simp only [kde, hφ, Finset.sum_apply, Function.comp_apply]
  rw [hkde, variance_const_mul,
    IndepFun.variance_sum (fun i _ => hY_memLp i) fun i _ j _ hij => hY_indep.indepFun hij]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  calc ((n : ℝ) * h)⁻¹ ^ 2 * ∑ i, Var[φ ∘ X i; P]
      ≤ ((n : ℝ) * h)⁻¹ ^ 2 * ∑ _i : Fin n, B * (h * ∫ u, K u ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h_term i) (sq_nonneg _)
    _ = B * (∫ u, K u ^ 2) / (n * h) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end ProbabilityTheory
