/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Moments.SubGaussian
public import MathlibExt.Probability.HoeffdingBounded

/-!
# Uniform deviation of the empirical risk over a finite class

For a finite class of predictors and a loss bounded in `[0, ℓ∞]`, Hoeffding's inequality for each
predictor and a union bound control the largest deviation between the empirical risk and the
expected risk (F. Bach, *Learning Theory from First Principles*, MIT Press (2024),
Section 4.4.3). A uniform deviation bound in turn controls empirical risk minimization through the
decomposition of Section 4.4, equation (4.10).

Predictors are abstract: `L f z` stands for the loss `ℓ(y, f(x))` of predictor `f` at the example
`z = (x, y)`.

## Main definitions

- `risk L ν f`: expected risk `∫ L f z dν(z)`.
- `empiricalRisk L z f`: empirical risk `(1/n) ∑ᵢ L f (zᵢ)` on a sample `z : Fin n → 𝒵`.

## Main results

- `measureReal_exists_abs_empiricalRisk_sub_risk_ge_le`: the tail bound
  `P(∃ f, |R̂(f) - R(f)| ≥ t) ≤ 2 |F| exp (-2 n t² / ℓ∞²)`.
- `one_sub_le_measureReal_forall_abs_empiricalRisk_sub_risk_lt`: the high-probability form.
- `risk_le_add_two_mul_of_forall_abs_sub_le`: if `f̂` minimizes the empirical risk and every
  deviation is at most `s`, then `R(f̂) ≤ R(f) + 2 s` for every `f`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace CSLibExt.MachineLearning.GeneralizationBounds

variable {Ω 𝒵 F : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒵]

/-- The expected risk `R(f) = E[ℓ(y, f(x))] = ∫ L f z dν(z)` of a predictor `f` under the data
distribution `ν`, where `L f z` is the loss of `f` at the example `z`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Definition 2.1. -/
noncomputable def risk (L : F → 𝒵 → ℝ) (ν : Measure 𝒵) (f : F) : ℝ :=
  ∫ z, L f z ∂ν

/-- The empirical risk `R̂(f) = (1/n) ∑ᵢ ℓ(yᵢ, f(xᵢ))` of a predictor `f` on a sample
`z : Fin n → 𝒵`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Definition 2.2. -/
noncomputable def empiricalRisk {n : ℕ} (L : F → 𝒵 → ℝ) (z : Fin n → 𝒵) (f : F) : ℝ :=
  (1 / n : ℝ) * ∑ i, L f (z i)

/-- **Excess risk of empirical risk minimization under a uniform deviation bound.** If `f̂`
minimizes the empirical risk `R̂` over the class and `|R̂(f) - R(f)| ≤ s` for every `f`, then
`R(f̂) ≤ R(f) + 2 s` for every `f`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 4.4,
equation (4.10) (the decomposition `R(f̂) - R(f) ≤ (R(f̂) - R̂(f̂)) + (R̂(f̂) - R̂(f)) +
(R̂(f) - R(f))`). -/
theorem risk_le_add_two_mul_of_forall_abs_sub_le {R Rhat : F → ℝ} {fhat : F}
    (hmin : ∀ f, Rhat fhat ≤ Rhat f) {s : ℝ} (hdev : ∀ f, |Rhat f - R f| ≤ s) (f : F) :
    R fhat ≤ R f + 2 * s := by
  have h1 := (abs_le.mp (hdev fhat)).1
  have h2 := (abs_le.mp (hdev f)).2
  linarith [hmin f]

/-- The empirical risk of a measurable loss along measurable sample maps is measurable. -/
theorem measurable_empiricalRisk {n : ℕ} {Z : Fin n → Ω → 𝒵} (hZ : ∀ i, Measurable (Z i))
    {L : F → 𝒵 → ℝ} (hL : ∀ f, Measurable (L f)) (f : F) :
    Measurable fun ω => empiricalRisk L (fun i => Z i ω) f := by
  unfold empiricalRisk
  exact (Finset.measurable_sum _ fun i _ => (hL f).comp (hZ i)).const_mul _

/-- **Uniform deviation for a finite class.** Let `Z₁, …, Zₙ` (`n ≥ 1`) be independent examples
with common law `ν`, let `F` be a finite class and let the loss satisfy `L f z ∈ [0, ℓ∞]` for
`ν`-almost every `z`. Then for every `t ≥ 0`,
`P(∃ f ∈ F, |R̂(f) - R(f)| ≥ t) ≤ 2 |F| exp (-2 n t² / ℓ∞²)`.

Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 4.4.3
(finite number of models: Hoeffding's inequality for each predictor and the union bound).
Proof: `MathlibExt.Probability.HoeffdingBounded.measureReal_abs_avg_sub_ge_le` for each `f` and
a union bound over the finite class. -/
theorem measureReal_exists_abs_empiricalRisk_sub_risk_ge_le {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype F] {ν : Measure 𝒵} {n : ℕ} (hn : 0 < n)
    {Z : Fin n → Ω → 𝒵} (h_indep : iIndepFun Z μ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, μ.map (Z i) = ν) {L : F → 𝒵 → ℝ} (hL : ∀ f, Measurable (L f)) {ℓ : ℝ}
    (hbound : ∀ f, ∀ᵐ z ∂ν, L f z ∈ Set.Icc 0 ℓ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | ∃ f, t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} ≤
      2 * Fintype.card F * exp (-2 * n * t ^ 2 / ℓ ^ 2) := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hone : ∀ f : F, μ.real {ω | t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} ≤
      2 * exp (-2 * n * t ^ 2 / ℓ ^ 2) := by
    intro f
    have hindep : iIndepFun (fun i ω => L f (Z i ω)) μ :=
      h_indep.comp (fun _ => L f) (fun _ => hL f)
    have hb : ∀ i, ∀ᵐ ω ∂μ, L f (Z i ω) ∈ Set.Icc 0 ℓ := fun i =>
      ae_of_ae_map (hZ i).aemeasurable (by rw [hlaw i]; exact hbound f)
    have h := MathlibExt.Probability.HoeffdingBounded.measureReal_abs_avg_sub_ge_le hindep
      (fun i => ((hL f).comp (hZ i)).aemeasurable) hb ht
    have hmean : ∀ i, ∫ ω, L f (Z i ω) ∂μ = risk L ν f := fun i => by
      rw [risk, ← hlaw i, integral_map (hZ i).aemeasurable (hL f).aestronglyMeasurable]
    have havg : (1 / n : ℝ) * ∑ i, ∫ ω, L f (Z i ω) ∂μ = risk L ν f := by
      simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    simpa only [havg, sub_zero, empiricalRisk] using h
  have hsub : {ω | ∃ f, t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} =
      ⋃ f, {ω | t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} := by
    ext ω; simp
  rw [hsub]
  calc _ ≤ ∑ f, μ.real {ω | t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} :=
        measureReal_iUnion_fintype_le _
    _ ≤ ∑ _f : F, 2 * exp (-2 * n * t ^ 2 / ℓ ^ 2) := Finset.sum_le_sum fun f _ => hone f
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- **Uniform deviation for a finite class, high-probability form.** Under the hypotheses of
`measureReal_exists_abs_empiricalRisk_sub_risk_ge_le`, with `F` nonempty and `ℓ∞ > 0`, for every
`δ ∈ (0, 1]`, with probability at least `1 - δ`, every `f ∈ F` satisfies
`|R̂(f) - R(f)| < ℓ∞ √(log (2 |F| / δ) / (2 n))`.

Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 4.4.3
(the source states the bound with probability greater than `1 - δ` and a non-strict
inequality; the strict event and `δ = 1` are derived here). -/
theorem one_sub_le_measureReal_forall_abs_empiricalRisk_sub_risk_lt {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype F] [Nonempty F] {ν : Measure 𝒵} {n : ℕ} (hn : 0 < n)
    {Z : Fin n → Ω → 𝒵} (h_indep : iIndepFun Z μ) (hZ : ∀ i, Measurable (Z i))
    (hlaw : ∀ i, μ.map (Z i) = ν) {L : F → 𝒵 → ℝ} (hL : ∀ f, Measurable (L f)) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (hbound : ∀ f, ∀ᵐ z ∂ν, L f z ∈ Set.Icc 0 ℓ) {δ : ℝ} (hδ : δ ∈ Set.Ioc 0 1) :
    1 - δ ≤ μ.real {ω | ∀ f, |empiricalRisk L (fun i => Z i ω) f - risk L ν f| <
      ℓ * √(log (2 * Fintype.card F / δ) / (2 * n))} := by
  set t := ℓ * √(log (2 * Fintype.card F / δ) / (2 * n)) with ht_def
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have harg : 1 ≤ 2 * Fintype.card F / δ := by
    rw [le_div_iff₀ hδ.1]; nlinarith [hδ.2]
  have hlog : 0 ≤ log (2 * Fintype.card F / δ) := log_nonneg harg
  have ht : 0 ≤ t := mul_nonneg hℓ.le (sqrt_nonneg _)
  have htail := measureReal_exists_abs_empiricalRisk_sub_risk_ge_le hn h_indep hZ hlaw hL
    hbound ht
  have hexp : 2 * (Fintype.card F : ℝ) * exp (-2 * n * t ^ 2 / ℓ ^ 2) = δ := by
    have ht2 : t ^ 2 = ℓ ^ 2 * (log (2 * Fintype.card F / δ) / (2 * n)) := by
      rw [ht_def, mul_pow, sq_sqrt (div_nonneg hlog (by positivity))]
    have hexpo : -2 * n * t ^ 2 / ℓ ^ 2 = -log (2 * Fintype.card F / δ) := by
      rw [ht2]; field_simp
    rw [hexpo, exp_neg, exp_log (by linarith)]
    field_simp
  have hmeas : MeasurableSet
      {ω | ∃ f, t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} := by
    have : {ω | ∃ f, t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} =
        ⋃ f, {ω | t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iUnion fun f => measurableSet_le measurable_const
      (continuous_abs.measurable.comp
        ((measurable_empiricalRisk hZ hL f).sub_const (risk L ν f)))
  have hcompl : {ω | ∀ f, |empiricalRisk L (fun i => Z i ω) f - risk L ν f| < t} =
      {ω | ∃ f, t ≤ |empiricalRisk L (fun i => Z i ω) f - risk L ν f|}ᶜ := by
    ext ω; simp
  rw [hcompl, measureReal_compl hmeas, probReal_univ]
  linarith

end CSLibExt.MachineLearning.GeneralizationBounds
