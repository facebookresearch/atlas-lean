/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.MirrorDescent
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Robust stochastic approximation: the expected error of stochastic mirror descent

Mirror descent stochastic approximation (A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro,
*Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19(4)
(2009), 1574–1609, Section 2.3) minimizes a convex function `f` over a compact convex set `X`
from unbiased stochastic subgradients `G(x, ξ)`, `ξ₀, ξ₁, …` i.i.d.: it runs the prox steps of
mirror descent (`MirrorDescent`) with `G(x_t, ξ_t)` and returns the weighted average of the
iterates. Taking expectations of the pathwise bound (2.39), where the noise term has mean zero
because `ξ_t` is independent of `x_t`, gives the efficiency estimate (2.44)
`E[f(x̃_N)] - f(x⋆) ≤ (D² + M² ∑ γ_t² / (2α)) / ∑ γ_t`.

Here the prox mapping is a measurable map `P` whose values satisfy the optimality condition of the
prox step, and the stochastic subgradients are bounded, `‖G(x, ξ)‖_* ≤ M`, a special case of the
source's second-moment assumption (2.40).

Main result: `integral_robust_sa_average_sub_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Analysis.Convex.MirrorDescent

namespace MathlibExt.Analysis.Convex.RobustStochasticApproximation

variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]

omit [MeasurableSpace Ω] [FiniteDimensional ℝ E] [BorelSpace E] in
/- The iterates are measurable with respect to the past of the noise. -/
private theorem measurable_iterate_past {G : E → Ξ → E →L[ℝ] ℝ}
    (hGmeas : Measurable (Function.uncurry G)) {P : E → (E →L[ℝ] ℝ) → E}
    (hPmeas : Measurable (Function.uncurry P)) {ξ : ℕ → Ω → Ξ} {γ : ℕ → ℝ} {x0 : E}
    {x : ℕ → Ω → E} (hx0 : ∀ s, x 0 s = x0)
    (hx : ∀ t s, x (t + 1) s = P (x t s) (γ t • G (x t s) (ξ t s))) (t : ℕ) :
    Measurable[⨆ i ∈ Set.Iio t, MeasurableSpace.comap (ξ i) inferInstance] (x t) := by
  induction t with
  | zero =>
    have : x 0 = fun _ => x0 := funext hx0
    rw [this]; exact measurable_const
  | succ t ih =>
    set 𝓕 := ⨆ i ∈ Set.Iio (t + 1), MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ)
    have hle : (⨆ i ∈ Set.Iio t, MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ))
        ≤ 𝓕 := biSup_mono fun i hi => lt_trans hi (Nat.lt_succ_self t)
    have hxt : Measurable[𝓕] (x t) := ih.mono hle le_rfl
    have hξt : Measurable[𝓕] (ξ t) :=
      (comap_measurable (ξ t)).mono (le_iSup₂ (f := fun i (_ : i ∈ Set.Iio (t + 1)) =>
        MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ)) t (Nat.lt_succ_self t))
        le_rfl
    have : x (t + 1) = fun s => P (x t s) (γ t • G (x t s) (ξ t s)) := funext (hx t)
    rw [this]
    exact hPmeas.comp (hxt.prodMk ((hGmeas.comp (hxt.prodMk hξt)).const_smul (γ t)))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem indepFun_iterate {G : E → Ξ → E →L[ℝ] ℝ}
    (hGmeas : Measurable (Function.uncurry G)) {P : E → (E →L[ℝ] ℝ) → E}
    (hPmeas : Measurable (Function.uncurry P)) {ξ : ℕ → Ω → Ξ} (hξmeas : ∀ t, Measurable (ξ t))
    (hξindep : iIndepFun ξ μ) {γ : ℕ → ℝ} {x0 : E} {x : ℕ → Ω → E} (hx0 : ∀ s, x 0 s = x0)
    (hx : ∀ t s, x (t + 1) s = P (x t s) (γ t • G (x t s) (ξ t s))) (t : ℕ) :
    IndepFun (x t) (ξ t) μ := by
  have hind := indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (ξ i) inferInstance)
    (fun i => (hξmeas i).comap_le) ((iIndepFun_iff_iIndep _ _ _).mp hξindep)
    (S := Set.Iio t) (T := {t}) (by simp)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
  · exact (measurable_iterate_past hGmeas hPmeas hx0 hx t).comap_le
  · exact le_iSup₂ (f := fun i (_ : i ∈ ({t} : Set ℕ)) =>
      MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ)) t rfl

/- Joint measurability of the evaluation of linear forms. -/
private theorem measurable_eval :
    Measurable fun p : (E →L[ℝ] ℝ) × E => p.1 p.2 :=
  (continuous_fst.clm_apply continuous_snd).measurable

/- Conditioning on the past: the noise has mean zero against the current iterate. -/
private theorem integral_apply_stochastic_eq [IsProbabilityMeasure μ] {X : Set E}
    {Y : Ω → E} {Z : Ω → Ξ} (hY : Measurable Y) (hZ : Measurable Z) (hind : IndepFun Y Z μ)
    (hYX : ∀ s, Y s ∈ X) {ν : Measure Ξ} [IsProbabilityMeasure ν] (hlaw : μ.map Z = ν)
    {G : E → Ξ → E →L[ℝ] ℝ} (hGmeas : Measurable (Function.uncurry G)) {M : ℝ}
    (hGbound : ∀ x ∈ X, ∀ ζ, ‖G x ζ‖ ≤ M) {c : E} {C : ℝ} (hXb : ∀ x ∈ X, ‖x - c‖ ≤ C) :
    ∫ s, G (Y s) (Z s) (Y s - c) ∂μ = ∫ s, ∫ ζ, G (Y s) ζ (Y s - c) ∂ν ∂μ := by
  set h : E × Ξ → ℝ := fun p => G p.1 p.2 (p.1 - c) with hh_def
  have hh : Measurable h :=
    measurable_eval.comp (hGmeas.prodMk (measurable_fst.sub_const c))
  have hF : Measurable fun s => (Y s, Z s) := hY.prodMk hZ
  have hmap : μ.map (fun s => (Y s, Z s)) = (μ.map Y).prod ν := by
    rw [← hlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable).mp hind
  have hbd : ∀ x ∈ X, ∀ ζ, ‖G x ζ (x - c)‖ ≤ M * C := by
    intro x hx ζ
    have hC : 0 ≤ C := (norm_nonneg _).trans (hXb x hx)
    exact ((G x ζ).le_opNorm _).trans (mul_le_mul (hGbound x hx ζ) (hXb x hx) (norm_nonneg _)
      ((norm_nonneg _).trans (hGbound x hx ζ)))
  have hint_μ : Integrable (h ∘ fun s => (Y s, Z s)) μ :=
    Integrable.of_bound (hh.comp hF).aestronglyMeasurable (M * C)
      (ae_of_all _ fun s => hbd _ (hYX s) _)
  have hint_prod : Integrable h ((μ.map Y).prod ν) := by
    rw [← hmap]; exact (integrable_map_measure hh.aestronglyMeasurable hF.aemeasurable).mpr hint_μ
  calc ∫ s, G (Y s) (Z s) (Y s - c) ∂μ = ∫ s, h (Y s, Z s) ∂μ := rfl
    _ = ∫ p, h p ∂(μ.map fun s => (Y s, Z s)) :=
        (integral_map hF.aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ p, h p ∂((μ.map Y).prod ν) := by rw [hmap]
    _ = ∫ y, ∫ ζ, h (y, ζ) ∂ν ∂(μ.map Y) := integral_prod h hint_prod
    _ = ∫ s, ∫ ζ, h (Y s, ζ) ∂ν ∂μ :=
        integral_map hY.aemeasurable hh.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable


omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/- A function continuous on `X` composed with a measurable map into `X` is measurable. -/
private theorem measurable_comp_of_continuousOn {X : Set E} {f : E → ℝ} (hfc : ContinuousOn f X)
    {Y : Ω → E} (hY : Measurable Y) (hYX : ∀ s, Y s ∈ X) : Measurable fun s => f (Y s) := by
  have h1 : Measurable fun s => (⟨Y s, hYX s⟩ : X) := hY.subtype_mk
  have h2 : Continuous (X.domRestrict f) := hfc.domRestrict
  exact h2.measurable.comp h1

/-- **Expected error of robust stochastic approximation (mirror descent SA).** Let `E` be a
finite-dimensional real normed space, `X ⊆ E` compact, `Xo ⊆ X`, `α > 0`, and let the
distance-generating function `ω` be `α`-strongly convex in the Bregman form
`V_x(u) ≥ (α/2) ‖u - x‖²` (`x ∈ Xo`, `u ∈ X`). Let `P : E → E* → E` be a measurable prox mapping:
for `x ∈ Xo`, `P x ξ ∈ Xo` satisfies the optimality condition of
`argmin_{u ∈ X} {ξ u + V_x(u)}`. Let `f` be convex and continuous on `X`, let `ξ₀, ξ₁, …` be
independent with common law `ν`, and let `G : E → Ξ → E*` be jointly measurable with
`‖G(x, ζ)‖_* ≤ M` on `X` and mean `∫ G(x, ζ) dν(ζ)` a subgradient of `f` at every `x ∈ X`
relative to `X`. Run `x_{t+1} = P(x_t, γ_t G(x_t, ξ_t))` from `x₀ ∈ Xo` with steps `γ_t > 0`.
Then for every `xstar ∈ X` with `V_{x₀}(xstar) ≤ D²` and every `N ≥ 1`, the weighted average
`x̃_N = (∑_{t<N} γ_t)⁻¹ ∑_{t<N} γ_t x_t` satisfies
`E[f(x̃_N)] - f(xstar) ≤ (D² + M² ∑_{t<N} γ_t² / (2α)) / ∑_{t<N} γ_t`.
This is the efficiency estimate (2.44) of A. Nemirovski, A. Juditsky, G. Lan and A. Shapiro,
*Robust stochastic approximation approach to stochastic programming*, SIAM J. Optim. 19 (2009),
Section 2.3 (there `x₀ = argmin_X ω` and `D = D_{ω,X}` of (2.43), which gives
`V_{x₀}(x) ≤ D²` on `X` by (2.42)), under the stronger assumption of a bounded stochastic
subgradient in place of the second-moment bound (2.40), with i.i.d. noise. -/
theorem integral_robust_sa_average_sub_le [IsProbabilityMeasure μ]
    (ω : E → ℝ) (ω' : E → E →L[ℝ] ℝ) {α : ℝ} (hα : 0 < α) {X Xo : Set E} (hXo : Xo ⊆ X)
    (hXc : IsCompact X) (hsc : ∀ x ∈ Xo, ∀ u ∈ X, α / 2 * ‖u - x‖ ^ 2 ≤ bregman ω ω' x u)
    {P : E → (E →L[ℝ] ℝ) → E} (hPmeas : Measurable (Function.uncurry P))
    (hP : ∀ x ∈ Xo, ∀ ξ, P x ξ ∈ Xo ∧ ∀ u ∈ X, 0 ≤ (ξ - ω' x + ω' (P x ξ)) (u - P x ξ))
    {f : E → ℝ} (hf : ConvexOn ℝ X f) (hfc : ContinuousOn f X)
    {ν : Measure Ξ} [IsProbabilityMeasure ν] {G : E → Ξ → E →L[ℝ] ℝ}
    (hGmeas : Measurable (Function.uncurry G)) {M : ℝ} (hGbound : ∀ x ∈ X, ∀ ζ, ‖G x ζ‖ ≤ M)
    (hGmean : ∀ x ∈ X, ∀ y ∈ X, f x + (∫ ζ, G x ζ ∂ν) (y - x) ≤ f y)
    {ξ : ℕ → Ω → Ξ} (hξmeas : ∀ t, Measurable (ξ t)) (hξindep : iIndepFun ξ μ)
    (hξlaw : ∀ t, μ.map (ξ t) = ν) {x0 : E} (hx0Xo : x0 ∈ Xo) {γ : ℕ → ℝ} (hγ : ∀ t, 0 < γ t)
    {x : ℕ → Ω → E} (hx0 : ∀ s, x 0 s = x0)
    (hx : ∀ t s, x (t + 1) s = P (x t s) (γ t • G (x t s) (ξ t s)))
    {xstar : E} (hxstar : xstar ∈ X) {D : ℝ} (hD : bregman ω ω' x0 xstar ≤ D ^ 2)
    {N : ℕ} (hN : 0 < N) :
    ∫ s, f ((∑ t ∈ range N, γ t)⁻¹ • ∑ t ∈ range N, γ t • x t s) ∂μ - f xstar ≤
      (D ^ 2 + M ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α)) / ∑ t ∈ range N, γ t := by
  -- The iterates stay in `Xo`.
  have hxXo : ∀ t s, x t s ∈ Xo := by
    intro t s
    induction t with
    | zero => rw [hx0]; exact hx0Xo
    | succ t ih => rw [hx]; exact (hP _ ih _).1
  have hxX : ∀ t s, x t s ∈ X := fun t s => hXo (hxXo t s)
  have hxmeas : ∀ t, Measurable (x t) := fun t =>
    (measurable_iterate_past hGmeas hPmeas hx0 hx t).mono
      (iSup₂_le fun i _ => (hξmeas i).comap_le) le_rfl
  set S := ∑ t ∈ range N, γ t with hSdef
  have hS : 0 < S := sum_pos (fun t _ => hγ t) (nonempty_range_iff.mpr hN.ne')
  -- Bounds on `X`.
  obtain ⟨Cf, hCf⟩ := hXc.exists_bound_of_continuousOn hfc
  obtain ⟨R, hR⟩ := hXc.isBounded.exists_norm_le
  have hXb : ∀ y ∈ X, ‖y - xstar‖ ≤ R + ‖xstar‖ := fun y hy =>
    (norm_sub_le _ _).trans (by linarith [hR y hy])
  -- The cross terms `G_t (x_t - x⋆)`.
  set Gt : ℕ → Ω → ℝ := fun t s => G (x t s) (ξ t s) (x t s - xstar) with hGt
  have hGtmeas : ∀ t, Measurable (Gt t) := fun t =>
    measurable_eval.comp ((hGmeas.comp ((hxmeas t).prodMk (hξmeas t))).prodMk
      ((hxmeas t).sub_const xstar))
  have hGtint : ∀ t, Integrable (Gt t) μ := fun t =>
    Integrable.of_bound (hGtmeas t).aestronglyMeasurable (M * (R + ‖xstar‖))
      (ae_of_all _ fun s => ((G (x t s) (ξ t s)).le_opNorm _).trans
        (mul_le_mul (hGbound _ (hxX t s) _) (hXb _ (hxX t s)) (norm_nonneg _)
          ((norm_nonneg _).trans (hGbound _ (hxX t s) (ξ t s)))))
  have hfint : ∀ t, Integrable (fun s => f (x t s)) μ := fun t =>
    Integrable.of_bound
      (measurable_comp_of_continuousOn hfc (hxmeas t) (hxX t)).aestronglyMeasurable Cf
      (ae_of_all _ fun s => hCf _ (hxX t s))
  -- Expected cross term dominates the expected gap.
  set h : E × Ξ → ℝ := fun p => G p.1 p.2 (p.1 - xstar) with hh_def
  have hh : Measurable h := measurable_eval.comp (hGmeas.prodMk (measurable_fst.sub_const xstar))
  have hk : StronglyMeasurable fun y => ∫ ζ, h (y, ζ) ∂ν :=
    hh.stronglyMeasurable.integral_prod_right'
  have hGint : ∀ y ∈ X, Integrable (G y) ν := fun y hy =>
    Integrable.of_bound (hGmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      M (ae_of_all _ (hGbound y hy))
  have hcross : ∀ t, ∫ s, f (x t s) ∂μ - f xstar ≤ ∫ s, Gt t s ∂μ := by
    intro t
    have heq := integral_apply_stochastic_eq (hxmeas t) (hξmeas t)
      (indepFun_iterate hGmeas hPmeas hξmeas hξindep hx0 hx t) (hxX t) (hξlaw t) hGmeas hGbound
      hXb
    have hle : ∀ s, f (x t s) - f xstar ≤ ∫ ζ, G (x t s) ζ (x t s - xstar) ∂ν := by
      intro s
      have := hGmean _ (hxX t s) _ hxstar
      have h2 : (∫ ζ, G (x t s) ζ ∂ν) (xstar - x t s) =
          -(∫ ζ, G (x t s) ζ ∂ν) (x t s - xstar) := by
        rw [← map_neg, neg_sub]
      rw [← ContinuousLinearMap.integral_apply (hGint _ (hxX t s))]
      linarith
    have hint2 : Integrable (fun s => ∫ ζ, G (x t s) ζ (x t s - xstar) ∂ν) μ := by
      refine Integrable.of_bound (hk.comp_measurable (hxmeas t)).aestronglyMeasurable
        (M * (R + ‖xstar‖)) (ae_of_all _ fun s => ?_)
      have hb : ∀ ζ, ‖G (x t s) ζ (x t s - xstar)‖ ≤ M * (R + ‖xstar‖) := fun ζ =>
        ((G (x t s) ζ).le_opNorm _).trans (mul_le_mul (hGbound _ (hxX t s) _)
          (hXb _ (hxX t s)) (norm_nonneg _) ((norm_nonneg _).trans (hGbound _ (hxX t s) ζ)))
      have := norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all _ hb)
      simpa [probReal_univ] using this
    have hsub : ∫ s, f (x t s) ∂μ - f xstar = ∫ s, (f (x t s) - f xstar) ∂μ := by
      rw [integral_sub (hfint t) (integrable_const _), integral_const, probReal_univ, one_smul]
    rw [hsub, heq]
    exact integral_mono ((hfint t).sub (integrable_const _)) hint2 hle
  -- Pathwise bound.
  have hpath : ∀ s, ∑ t ∈ range N, γ t * Gt t s ≤
      D ^ 2 + M ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α) := by
    intro s
    have h0 := mirror_descent_sum_le ω ω' hα hXo hsc (x := fun t => x t s)
      (g := fun t => G (x t s) (ξ t s)) (γ := γ) (fun t => hxXo t s)
      (fun t u hu => by
        rw [hx t s]
        exact (hP _ (hxXo t s) _).2 u hu) hxstar N
    rw [hx0 s] at h0
    have hsq : ∑ t ∈ range N, γ t ^ 2 * ‖G (x t s) (ξ t s)‖ ^ 2 ≤
        M ^ 2 * ∑ t ∈ range N, γ t ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun t _ => ?_
      have := pow_le_pow_left₀ (norm_nonneg _) (hGbound _ (hxX t s) (ξ t s)) 2
      nlinarith [sq_nonneg (γ t)]
    have : (∑ t ∈ range N, γ t ^ 2 * ‖G (x t s) (ξ t s)‖ ^ 2) / (2 * α) ≤
        M ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α) := by gcongr
    simp only [hGt]
    linarith
  -- Jensen's inequality, pointwise, and integrability of the average.
  have hw0 : ∀ t ∈ range N, 0 ≤ γ t / S := fun t _ => div_nonneg (hγ t).le hS.le
  have hw1 : ∑ t ∈ range N, γ t / S = 1 := by
    rw [show (∑ t ∈ range N, γ t / S) = (∑ t ∈ range N, γ t) / S by
      simp [div_eq_mul_inv, Finset.sum_mul], ← hSdef, div_self hS.ne']
  have hpt : ∀ s, S⁻¹ • ∑ t ∈ range N, γ t • x t s = ∑ t ∈ range N, (γ t / S) • x t s := by
    intro s
    rw [smul_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [smul_smul, div_eq_inv_mul]
  have havgX : ∀ s, S⁻¹ • ∑ t ∈ range N, γ t • x t s ∈ X := fun s => by
    rw [hpt]; exact hf.1.sum_mem hw0 hw1 fun t _ => hxX t s
  have havgmeas : Measurable fun s => S⁻¹ • ∑ t ∈ range N, γ t • x t s :=
    (Finset.measurable_sum _ fun t _ => (hxmeas t).const_smul (γ t)).const_smul _
  have havgint : Integrable (fun s => f (S⁻¹ • ∑ t ∈ range N, γ t • x t s)) μ :=
    Integrable.of_bound (measurable_comp_of_continuousOn hfc havgmeas havgX).aestronglyMeasurable
      Cf (ae_of_all _ fun s => hCf _ (havgX s))
  have hjensen : ∀ s, f (S⁻¹ • ∑ t ∈ range N, γ t • x t s) ≤
      ∑ t ∈ range N, (γ t / S) * f (x t s) := by
    intro s
    rw [hpt]
    have := hf.map_sum_le (t := range N) (w := fun t => γ t / S) (p := fun t => x t s) hw0 hw1
      (fun t _ => hxX t s)
    simpa [smul_eq_mul] using this
  -- Integrate.
  have hstep1 : ∫ s, f (S⁻¹ • ∑ t ∈ range N, γ t • x t s) ∂μ ≤
      ∑ t ∈ range N, (γ t / S) * ∫ s, f (x t s) ∂μ := by
    calc ∫ s, f (S⁻¹ • ∑ t ∈ range N, γ t • x t s) ∂μ
        ≤ ∫ s, ∑ t ∈ range N, (γ t / S) * f (x t s) ∂μ :=
          integral_mono havgint (integrable_finsetSum _ fun t _ => (hfint t).const_mul _)
            hjensen
      _ = ∑ t ∈ range N, (γ t / S) * ∫ s, f (x t s) ∂μ := by
          rw [integral_finsetSum _ fun t _ => (hfint t).const_mul _]
          exact sum_congr rfl fun t _ => integral_const_mul _ _
  have hstep2 : ∑ t ∈ range N, γ t * (∫ s, f (x t s) ∂μ - f xstar) ≤
      ∑ t ∈ range N, γ t * ∫ s, Gt t s ∂μ :=
    sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hcross t) (hγ t).le
  have hstep3 : ∑ t ∈ range N, γ t * ∫ s, Gt t s ∂μ ≤
      D ^ 2 + M ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α) := by
    have : ∑ t ∈ range N, γ t * ∫ s, Gt t s ∂μ = ∫ s, ∑ t ∈ range N, γ t * Gt t s ∂μ := by
      rw [integral_finsetSum _ fun t _ => (hGtint t).const_mul _]
      exact sum_congr rfl fun t _ => (integral_const_mul _ _).symm
    rw [this]
    calc ∫ s, ∑ t ∈ range N, γ t * Gt t s ∂μ
        ≤ ∫ _s, (D ^ 2 + M ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α)) ∂μ :=
          integral_mono (integrable_finsetSum _ fun t _ => (hGtint t).const_mul _)
            (integrable_const _) hpath
      _ = _ := by rw [integral_const, probReal_univ, one_smul]
  have hlin : ∑ t ∈ range N, (γ t / S) * ∫ s, f (x t s) ∂μ - f xstar =
      (∑ t ∈ range N, γ t * (∫ s, f (x t s) ∂μ - f xstar)) / S := by
    rw [eq_div_iff hS.ne', sub_mul, sum_mul]
    have : ∑ t ∈ range N, γ t * (∫ s, f (x t s) ∂μ - f xstar) =
        ∑ t ∈ range N, γ t * ∫ s, f (x t s) ∂μ - S * f xstar := by
      rw [hSdef, sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl fun t _ => by ring
    rw [this]
    congr 1
    · exact sum_congr rfl fun t _ => by field_simp
    · ring
  have hfin : (∑ t ∈ range N, γ t * (∫ s, f (x t s) ∂μ - f xstar)) / S ≤
      (D ^ 2 + M ^ 2 * (∑ t ∈ range N, γ t ^ 2) / (2 * α)) / S :=
    div_le_div_of_nonneg_right (hstep2.trans hstep3) hS.le
  linarith

end MathlibExt.Analysis.Convex.RobustStochasticApproximation
