/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.StrongLaw

/-!
# CDIS Probabilités V: importance sampling

* id 99: the fundamental identity `E_f[h(X)] = ∫ h (f/g) g`, and the almost sure convergence of
  the importance sampling estimator `(1/n) ∑ (f/g)(X_i) h(X_i)` for `X_i` i.i.d. with density `g`.
* id 100: the optimal instrumental density `g* = |h| f / ∫ |h| f` minimises the variance of the
  estimator, for every sample size (`variance_estimator_optimal_le`). The chain is: the variance of
  one term is `∫ (h f)² / g - (E_f[h])²` (`variance_importanceSampling`), the estimator has
  variance `Var_g[(f / g) h] / n` (`variance_importanceSampling_estimator`), and `g*` minimises
  `∫ (h f)² / g` by Cauchy-Schwarz (`isMinOn_optimal_density`).

The course says there is "no restriction on the choice of `g`". The identity needs `g > 0`
wherever `h f ≠ 0`; `not_forall_integral_eq_integral_ratio` shows it fails otherwise. This is
the support condition used throughout, and `g*` satisfies it even where `h` vanishes and `f` does
not.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace CDIS

section Identity

/-- CDIS P.V, id 99: the fundamental identity of importance sampling, for any `g` that is
nonzero wherever `h f` is. -/
theorem integral_mul_eq_integral_ratio {f g h : ℝ → ℝ}
    (hsupp : ∀ x, g x = 0 → h x * f x = 0) :
    ∫ x, h x * f x = ∫ x, h x * f x / g x * g x := by
  congr 1
  ext x
  by_cases hg : g x = 0
  · simp [hg, hsupp x hg]
  · field_simp

/-- Without the support condition the identity of id 99 fails: `f = 1_[0,1]`, `g = 1_[2,3]`,
`h = 1`. -/
theorem not_forall_integral_eq_integral_ratio :
    ¬ ∀ f g : ℝ → ℝ, (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) → ∫ x, f x = 1 → ∫ x, g x = 1 →
      ∫ x, 1 * f x = ∫ x, 1 * f x / g x * g x := by
  intro H
  set f := (Icc (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ))
  set g := (Icc (2 : ℝ) 3).indicator (fun _ ↦ (1 : ℝ))
  have hf1 : ∫ x, f x = 1 := by simp [f, integral_indicator measurableSet_Icc]
  have hg1 : ∫ x, g x = 1 := by
    simp [g, integral_indicator measurableSet_Icc]; norm_num
  have hzero : ∀ x, 1 * f x / g x * g x = 0 := by
    intro x
    by_cases hx : x ∈ Icc (2 : ℝ) 3
    · have : x ∉ Icc (0 : ℝ) 1 := fun h ↦ by linarith [h.2, hx.1]
      simp [f, this]
    · simp [g, hx]
  have := H f g (fun x ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) x)
    (fun x ↦ indicator_nonneg (fun _ _ ↦ zero_le_one) x) hf1 hg1
  have h2 : ∫ x, 1 * f x / g x * g x = 0 := by simp_rw [hzero]; exact integral_zero ℝ ℝ
  rw [h2] at this
  simp [hf1] at this

end Identity

section Optimal

variable {a g : ℝ → ℝ}

/-- Cauchy-Schwarz core of id 100: for a density `g` that is positive where `a` is,
`(∫ a)² ≤ ∫ a² / g`. -/
theorem sq_integral_le_integral_sq_div (ha : 0 ≤ a) (hg : 0 ≤ g) (ham : Measurable a)
    (hgm : Measurable g) (hgi : Integrable g) (hg1 : ∫ x, g x = 1)
    (hsupp : ∀ x, g x = 0 → a x = 0) (hint : Integrable fun x ↦ a x ^ 2 / g x) :
    (∫ x, a x) ^ 2 ≤ ∫ x, a x ^ 2 / g x := by
  set F : ℝ → ℝ := fun x ↦ a x / √(g x)
  set G : ℝ → ℝ := fun x ↦ √(g x)
  have hFG : ∀ x, F x * G x = a x := by
    intro x
    by_cases hgx : g x = 0
    · simp [F, G, hgx, hsupp x hgx]
    · have : √(g x) ≠ 0 := Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (hg x) (Ne.symm hgx))
      simp only [F, G]
      field_simp
  have hF2 : ∀ x, F x ^ 2 = a x ^ 2 / g x := by
    intro x
    simp only [F, div_pow, Real.sq_sqrt (hg x)]
  have hG2 : ∀ x, G x ^ 2 = g x := fun x ↦ Real.sq_sqrt (hg x)
  have hFm : Measurable F := ham.div hgm.sqrt
  have hGm : Measurable G := hgm.sqrt
  have hFL : MemLp F (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp, memLp_two_iff_integrable_sq hFm.aestronglyMeasurable]
    simpa [hF2] using hint
  have hGL : MemLp G (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by simp, memLp_two_iff_integrable_sq hGm.aestronglyMeasurable]
    simpa [hG2] using hgi
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (Eventually.of_forall fun x ↦ div_nonneg (ha x) (Real.sqrt_nonneg _))
    (Eventually.of_forall fun x ↦ Real.sqrt_nonneg _) hFL hGL
  have e1 : ∫ x, F x * G x = ∫ x, a x := integral_congr_ae (Eventually.of_forall hFG)
  have e2 : ∫ x, F x ^ (2 : ℝ) = ∫ x, a x ^ 2 / g x := by
    congr 1; ext x; rw [Real.rpow_two, hF2]
  have e3 : ∫ x, G x ^ (2 : ℝ) = 1 := by
    rw [← hg1]; congr 1; ext x; rw [Real.rpow_two, hG2]
  rw [e1, e2, e3, Real.one_rpow, mul_one] at hCS
  have hV : 0 ≤ ∫ x, a x ^ 2 / g x :=
    integral_nonneg fun x ↦ div_nonneg (sq_nonneg _) (hg x)
  have hA : 0 ≤ ∫ x, a x := integral_nonneg ha
  calc (∫ x, a x) ^ 2 ≤ ((∫ x, a x ^ 2 / g x) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
    _ = ∫ x, a x ^ 2 / g x := by
      rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hV]

/-- Under the optimal density `g* = a / ∫ a`, the integrand `a² / g*` is `(∫ a) a`. -/
lemma sq_div_optimal_eq (x : ℝ) : a x ^ 2 / (a x / ∫ y, a y) = (∫ y, a y) * a x := by
  by_cases hax : a x = 0
  · simp [hax]
  · by_cases hc : ∫ y, a y = 0
    · simp [hc]
    · field_simp

/-- The optimal density `g* = a / ∫ a` attains the bound: `∫ a² / g* = (∫ a)²`. -/
theorem integral_sq_div_optimal :
    ∫ x, a x ^ 2 / (a x / ∫ y, a y) = (∫ x, a x) ^ 2 := by
  simp_rw [sq_div_optimal_eq, integral_const_mul, sq]

/-- CDIS P.V, id 100 (optimal density), with `a = |h| f`: among the densities `g` positive where
`a` is and with `a² / g` integrable, `g* = a / ∫ a` minimises `∫ a² / g = E_g[(h f / g)²]`. -/
theorem isMinOn_optimal_density (ha : 0 ≤ a) (ham : Measurable a) (hai : Integrable a)
    (hpos : 0 < ∫ x, a x) :
    let D := {g : ℝ → ℝ | 0 ≤ g ∧ Measurable g ∧ Integrable g ∧ ∫ x, g x = 1 ∧
      (∀ x, g x = 0 → a x = 0) ∧ Integrable fun x ↦ a x ^ 2 / g x}
    (fun x ↦ a x / ∫ y, a y) ∈ D ∧ IsMinOn (fun g ↦ ∫ x, a x ^ 2 / g x) D
      (fun x ↦ a x / ∫ y, a y) := by
  intro D
  refine ⟨⟨fun x ↦ div_nonneg (ha x) hpos.le, ham.div_const _, hai.div_const _, ?_, ?_, ?_⟩, ?_⟩
  · rw [integral_div, div_self hpos.ne']
  · intro x hx
    rcases (div_eq_zero_iff.1 hx) with h | h
    · exact h
    · exact absurd h hpos.ne'
  · simp_rw [sq_div_optimal_eq]
    exact hai.const_mul _
  · rintro g ⟨hg, hgm, hgi, hg1, hsupp, hint⟩
    simp only [mem_ofPred_eq, integral_sq_div_optimal]
    exact sq_integral_le_integral_sq_div ha hg ham hgm hgi hg1 hsupp hint

end Optimal

section Estimator

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {f g h : ℝ → ℝ}

/-- Integrals against the law with density `g`. -/
lemma integral_withDensity_ofReal (hgm : Measurable g) (hg : 0 ≤ g) (φ : ℝ → ℝ) :
    ∫ x, φ x ∂(volume.withDensity fun x ↦ ENNReal.ofReal (g x)) = ∫ x, g x * φ x := by
  rw [show (fun x ↦ ENNReal.ofReal (g x)) = fun x ↦ ((g x).toNNReal : ℝ≥0∞) from rfl,
    integral_withDensity_eq_integral_smul hgm.real_toNNReal]
  congr 1
  ext x
  simp [NNReal.smul_def, Real.coe_toNNReal _ (hg x)]

lemma integrable_withDensity_ofReal_iff (hgm : Measurable g) (hg : 0 ≤ g) (φ : ℝ → ℝ) :
    Integrable φ (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) ↔
      Integrable fun x ↦ g x * φ x := by
  rw [show (fun x ↦ ENNReal.ofReal (g x)) = fun x ↦ ((g x).toNNReal : ℝ≥0∞) from rfl,
    integrable_withDensity_iff_integrable_smul hgm.real_toNNReal]
  refine integrable_congr (Eventually.of_forall fun x ↦ ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (hg x)]

lemma mul_ratio_eq (hsupp : ∀ x, g x = 0 → h x * f x = 0) (x : ℝ) :
    g x * (f x / g x * h x) = h x * f x := by
  by_cases hgx : g x = 0
  · simp [hgx, hsupp x hgx]
  · field_simp

omit [IsProbabilityMeasure P] in
/-- CDIS P.V, id 99: the importance sampling estimator `(1/n) ∑ (f/g)(X_i) h(X_i)`, with
`X_i` i.i.d. of density `g`, converges almost surely to `E_f[h] = ∫ h f`. -/
theorem tendsto_importanceSampling (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hg : 0 ≤ g) (hsupp : ∀ x, g x = 0 → h x * f x = 0) (hint : Integrable fun x ↦ h x * f x)
    {X : ℕ → Ω → ℝ} (hlaw : ∀ i, HasLaw (X i) (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) P)
    (hindep : iIndepFun X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, f (X i ω) / g (X i ω) * h (X i ω)) / n)
      atTop (𝓝 (∫ x, h x * f x)) := by
  set φ : ℝ → ℝ := fun x ↦ f x / g x * h x
  have hφ : Measurable φ := (hfm.div hgm).mul hhm
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i ↦
    ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, (hlaw i).map_eq.trans (hlaw 0).map_eq.symm⟩
  have hY : iIndepFun (fun i ↦ φ ∘ X i) P := hindep.comp (fun _ ↦ φ) (fun _ ↦ hφ)
  have hmap : Integrable φ (P.map (X 0)) := by
    rw [(hlaw 0).map_eq, integrable_withDensity_ofReal_iff hgm hg]
    simpa [φ, mul_ratio_eq hsupp] using hint
  have hint0 : Integrable (φ ∘ X 0) P :=
    (integrable_map_measure hφ.aestronglyMeasurable (hlaw 0).aemeasurable).1 hmap
  have hmean : ∫ ω, (φ ∘ X 0) ω ∂P = ∫ x, h x * f x := by
    rw [show ∫ ω, (φ ∘ X 0) ω ∂P = ∫ x, φ x ∂(P.map (X 0)) from
      (integral_map (hlaw 0).aemeasurable hφ.aestronglyMeasurable).symm, (hlaw 0).map_eq,
      integral_withDensity_ofReal hgm hg]
    simp [φ, mul_ratio_eq hsupp]
  have := strong_law_ae_real (fun i ↦ φ ∘ X i) hint0
    (fun i j hij ↦ hY.indepFun hij) (fun i ↦ (hident i).comp hφ)
  rw [← hmean]
  exact this

omit [IsProbabilityMeasure P] in
/-- CDIS P.V, id 99: the self-normalised estimator `∑ w_i h(X_i) / ∑ w_i`, with weights
`w_i = f(X_i) / g(X_i)`, also converges almost surely to `E_f[h]` when `f` is a density. -/
theorem tendsto_importanceSampling_normalized (hfm : Measurable f) (hgm : Measurable g)
    (hhm : Measurable h) (hg : 0 ≤ g) (hsupp : ∀ x, g x = 0 → f x = 0)
    (hint : Integrable fun x ↦ h x * f x) (hfi : Integrable f) (hf1 : ∫ x, f x = 1)
    {X : ℕ → Ω → ℝ} (hlaw : ∀ i, HasLaw (X i) (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) P)
    (hindep : iIndepFun X P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (∑ i ∈ Finset.range n, f (X i ω) / g (X i ω) * h (X i ω)) /
      ∑ i ∈ Finset.range n, f (X i ω) / g (X i ω)) atTop (𝓝 (∫ x, h x * f x)) := by
  have hA := tendsto_importanceSampling hfm hgm hhm hg (fun x hx ↦ by simp [hsupp x hx]) hint
    hlaw hindep
  have hB := tendsto_importanceSampling (h := fun _ ↦ 1) hfm hgm measurable_const hg
    (fun x hx ↦ by simp [hsupp x hx]) (by simpa using hfi) hlaw hindep
  filter_upwards [hA, hB] with ω hAω hBω
  simp only [one_mul, mul_one, hf1] at hBω
  have := hAω.div hBω one_ne_zero
  rw [div_one] at this
  refine this.congr fun n ↦ ?_
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · simp [Nat.cast_eq_zero.1 hn]
  · exact div_div_div_cancel_right₀ hn _ _

/-- CDIS P.V, id 100: the variance of one importance sampling term under the density `g` is
`∫ (h f)² / g - (E_f[h])²`; only the first term depends on `g`, which is the quantity minimised
in `isMinOn_optimal_density` (with `a = |h f|`). -/
theorem variance_importanceSampling (hgm : Measurable g) (hg : 0 ≤ g)
    (hsupp : ∀ x, g x = 0 → h x * f x = 0)
    [IsProbabilityMeasure (volume.withDensity fun x ↦ ENNReal.ofReal (g x))]
    (hL2 : MemLp (fun x ↦ f x / g x * h x) 2 (volume.withDensity fun x ↦ ENNReal.ofReal (g x))) :
    Var[fun x ↦ f x / g x * h x; volume.withDensity fun x ↦ ENNReal.ofReal (g x)] =
      (∫ x, (h x * f x) ^ 2 / g x) - (∫ x, h x * f x) ^ 2 := by
  rw [variance_eq_sub hL2]
  simp only [Pi.pow_apply, integral_withDensity_ofReal hgm hg, mul_ratio_eq hsupp]
  congr 2
  ext x
  by_cases hgx : g x = 0
  · simp [hgx]
  · field_simp

/-- The law with a probability density `g` is a probability measure. -/
lemma isProbabilityMeasure_withDensity_ofReal (hg : 0 ≤ g) (hgi : Integrable g)
    (hg1 : ∫ x, g x = 1) :
    IsProbabilityMeasure (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg), hg1, ENNReal.ofReal_one]

/-- One importance sampling term has finite variance under `g` exactly when
`∫ (h f)² / g < ∞`, the course's condition. -/
lemma memLp_two_ratio_iff (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hg : 0 ≤ g) :
    MemLp (fun x ↦ f x / g x * h x) 2 (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) ↔
      Integrable fun x ↦ (h x * f x) ^ 2 / g x := by
  have hm : AEStronglyMeasurable (fun x ↦ f x / g x * h x)
      (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) :=
    ((hfm.div hgm).mul hhm).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm, integrable_withDensity_ofReal_iff hgm hg]
  refine integrable_congr (Eventually.of_forall fun x ↦ ?_)
  by_cases hgx : g x = 0
  · simp [hgx]
  · simp only
    field_simp

omit [IsProbabilityMeasure P] in
/-- CDIS P.V, id 100: for an i.i.d. sample of density `g`, the estimator of id 99 has variance
`Var_g[(f / g) h] / n`. -/
theorem variance_importanceSampling_estimator (hfm : Measurable f) (hgm : Measurable g)
    (hhm : Measurable h) [IsProbabilityMeasure P]
    (hL2 : MemLp (fun x ↦ f x / g x * h x) 2 (volume.withDensity fun x ↦ ENNReal.ofReal (g x)))
    {X : ℕ → Ω → ℝ} (hlaw : ∀ i, HasLaw (X i) (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) P)
    (hindep : iIndepFun X P) (n : ℕ) :
    Var[fun ω ↦ (∑ i ∈ Finset.range n, f (X i ω) / g (X i ω) * h (X i ω)) / n; P] =
      Var[fun x ↦ f x / g x * h x; volume.withDensity fun x ↦ ENNReal.ofReal (g x)] / n := by
  set φ : ℝ → ℝ := fun x ↦ f x / g x * h x
  have hφ : Measurable φ := (hfm.div hgm).mul hhm
  have hterm : ∀ i, Var[φ ∘ X i; P] = Var[φ; volume.withDensity fun x ↦ ENNReal.ofReal (g x)] :=
    fun i ↦ by rw [← (hlaw i).map_eq, variance_map hφ.aemeasurable (hlaw i).aemeasurable]
  have hL2' : ∀ i, MemLp (φ ∘ X i) 2 P := fun i ↦ by
    rw [← (hlaw i).map_eq] at hL2
    exact hL2.comp_of_map (hlaw i).aemeasurable
  have hsum : Var[fun ω ↦ ∑ i ∈ Finset.range n, φ (X i ω); P] =
      n * Var[φ; volume.withDensity fun x ↦ ENNReal.ofReal (g x)] := by
    have := IndepFun.variance_sum (s := Finset.range n) (fun i _ ↦ hL2' i)
      (fun i _ j _ hij ↦ (hindep.comp (fun _ ↦ φ) (fun _ ↦ hφ)).indepFun hij)
    rw [show (fun ω ↦ ∑ i ∈ Finset.range n, φ (X i ω)) = ∑ i ∈ Finset.range n, φ ∘ X i by
      ext ω; simp, this]
    simp [hterm]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero, div_zero]
    exact variance_zero P
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [show (fun ω ↦ (∑ i ∈ Finset.range n, φ (X i ω)) / n) =
      fun ω ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, φ (X i ω) by ext ω; rw [div_eq_inv_mul],
    variance_const_mul, hsum]
  field_simp

end Estimator

section OptimalVariance

variable {f h : ℝ → ℝ}

/-- The instrumental densities of id 100: probability densities `g` that are positive wherever
`h f ≠ 0` and for which one importance sampling term has finite variance. -/
def admissibleDensities (f h : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {g | 0 ≤ g ∧ Measurable g ∧ Integrable g ∧ ∫ x, g x = 1 ∧ (∀ x, g x = 0 → h x * f x = 0) ∧
    Integrable fun x ↦ (h x * f x) ^ 2 / g x}

/-- The optimal density `g* = |h f| / ∫ |h f|` of id 100. -/
noncomputable def optimalDensity (f h : ℝ → ℝ) : ℝ → ℝ :=
  fun x ↦ |h x * f x| / ∫ y, |h y * f y|

/-- The variance of one term under an admissible `g` is `∫ (h f)² / g - (E_f[h])²`. -/
lemma variance_eq_of_mem_admissibleDensities (hfm : Measurable f) (hhm : Measurable h)
    {g : ℝ → ℝ} (hgD : g ∈ admissibleDensities f h) :
    Var[fun x ↦ f x / g x * h x; volume.withDensity fun x ↦ ENNReal.ofReal (g x)] =
      (∫ x, (h x * f x) ^ 2 / g x) - (∫ x, h x * f x) ^ 2 := by
  obtain ⟨hg, hgm, hgi, hg1, hsupp, hint⟩ := hgD
  have := isProbabilityMeasure_withDensity_ofReal hg hgi hg1
  exact variance_importanceSampling hgm hg hsupp ((memLp_two_ratio_iff hfm hgm hhm hg).2 hint)

/-- CDIS P.V, id 100: `g*` is admissible and minimises the variance of one importance sampling
term `(f / g) h` under `g` among the admissible densities. -/
theorem isMinOn_variance_optimalDensity (hfm : Measurable f) (hhm : Measurable h)
    (hint : Integrable fun x ↦ h x * f x) (hpos : 0 < ∫ x, |h x * f x|) :
    optimalDensity f h ∈ admissibleDensities f h ∧
      IsMinOn (fun g ↦ Var[fun x ↦ f x / g x * h x;
        volume.withDensity fun x ↦ ENNReal.ofReal (g x)]) (admissibleDensities f h)
        (optimalDensity f h) := by
  have ha : Measurable fun x ↦ |h x * f x| := by fun_prop
  obtain ⟨hmem, hmin⟩ := isMinOn_optimal_density (fun x ↦ abs_nonneg (h x * f x)) ha hint.abs hpos
  have hD : {g : ℝ → ℝ | 0 ≤ g ∧ Measurable g ∧ Integrable g ∧ ∫ x, g x = 1 ∧
      (∀ x, g x = 0 → |h x * f x| = 0) ∧ Integrable fun x ↦ |h x * f x| ^ 2 / g x} =
      admissibleDensities f h := by
    ext g
    simp only [admissibleDensities, abs_eq_zero, sq_abs]
  rw [hD] at hmem hmin
  have hmem' : optimalDensity f h ∈ admissibleDensities f h := hmem
  refine ⟨hmem', isMinOn_iff.2 fun g hg ↦ ?_⟩
  have hle : ∫ x, (h x * f x) ^ 2 / optimalDensity f h x ≤ ∫ x, (h x * f x) ^ 2 / g x := by
    have := isMinOn_iff.1 hmin g hg
    simp only [sq_abs] at this
    exact this
  rw [variance_eq_of_mem_admissibleDensities hfm hhm hg,
    variance_eq_of_mem_admissibleDensities hfm hhm hmem']
  linarith

/-- CDIS P.V, id 100, as stated in the course: for every sample size `n`, the importance
sampling estimator built on an i.i.d. sample of density `g*` has a variance no larger than the
one built on an i.i.d. sample of any admissible density `g`. -/
theorem variance_estimator_optimal_le {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hfm : Measurable f) (hhm : Measurable h) (hint : Integrable fun x ↦ h x * f x)
    (hpos : 0 < ∫ x, |h x * f x|) {g : ℝ → ℝ} (hgD : g ∈ admissibleDensities f h)
    {X : ℕ → Ω → ℝ} (hX : ∀ i, HasLaw (X i) (volume.withDensity fun x ↦ ENNReal.ofReal (g x)) P)
    (hXi : iIndepFun X P) {Y : ℕ → Ω' → ℝ}
    (hY : ∀ i, HasLaw (Y i)
      (volume.withDensity fun x ↦ ENNReal.ofReal (optimalDensity f h x)) P')
    (hYi : iIndepFun Y P') (n : ℕ) :
    Var[fun ω ↦ (∑ i ∈ Finset.range n,
        f (Y i ω) / optimalDensity f h (Y i ω) * h (Y i ω)) / n; P'] ≤
      Var[fun ω ↦ (∑ i ∈ Finset.range n, f (X i ω) / g (X i ω) * h (X i ω)) / n; P] := by
  obtain ⟨hmem, hmin⟩ := isMinOn_variance_optimalDensity hfm hhm hint hpos
  have hL2 : ∀ {k : ℝ → ℝ}, k ∈ admissibleDensities f h →
      MemLp (fun x ↦ f x / k x * h x) 2 (volume.withDensity fun x ↦ ENNReal.ofReal (k x)) :=
    fun hk ↦ (memLp_two_ratio_iff hfm hk.2.1 hhm hk.1).2 hk.2.2.2.2.2
  rw [variance_importanceSampling_estimator hfm hmem.2.1 hhm (hL2 hmem) hY hYi,
    variance_importanceSampling_estimator hfm hgD.2.1 hhm (hL2 hgD) hX hXi]
  exact div_le_div_of_nonneg_right (hmin hgD) (Nat.cast_nonneg n)

end OptimalVariance

end CDIS
