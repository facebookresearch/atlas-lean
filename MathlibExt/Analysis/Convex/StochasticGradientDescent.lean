/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Stochastic gradient descent for nonsmooth convex objectives

Stochastic gradient descent with step sizes `γₜ ∝ 1 / √t` on a convex objective whose stochastic
subgradients are unbiased and bounded by `B` reaches an expected objective gap of order
`D B log t / √t` at the weighted average of the iterates (F. Bach, *Learning Theory from First
Principles*, MIT Press (2024), Section 5.4, Proposition 5.7). Applied to the expected risk with
one fresh example per step, it is single-pass learning with the same `1 / √n` rate as the
estimation error of empirical risk minimization.

The stochastic gradients are modelled, as the source suggests after its assumptions (H-1) and
(H-2), by independent gradient functions `gₜ(θ) = G(θ, ξₜ)` with `ξ₀, ξ₁, …` i.i.d. The
deterministic counterpart is `MetaMathlibExt.subgradient_method_rate`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators RealInnerProductSpace

namespace MathlibExt.Analysis.Convex.StochasticGradientDescent

variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace Ω] in
/- The iterates are measurable with respect to the past of the noise. -/
private theorem measurable_iterate_past {G : E → Ξ → E} (hGmeas : Measurable (Function.uncurry G))
    {ξ : ℕ → Ω → Ξ} {γ : ℕ → ℝ} {θ₀ : E} {θ : ℕ → Ω → E} (hθ0 : ∀ ω, θ 0 ω = θ₀)
    (hθ : ∀ t ω, θ (t + 1) ω = θ t ω - γ t • G (θ t ω) (ξ t ω)) (t : ℕ) :
    Measurable[⨆ i ∈ Set.Iio t, MeasurableSpace.comap (ξ i) inferInstance] (θ t) := by
  induction t with
  | zero =>
    have : θ 0 = fun _ => θ₀ := funext hθ0
    rw [this]; exact measurable_const
  | succ t ih =>
    set 𝓕 := ⨆ i ∈ Set.Iio (t + 1), MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ)
    have hle : (⨆ i ∈ Set.Iio t, MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ))
        ≤ 𝓕 := biSup_mono fun i hi => lt_trans hi (Nat.lt_succ_self t)
    have hθt : Measurable[𝓕] (θ t) := ih.mono hle le_rfl
    have hξt : Measurable[𝓕] (ξ t) :=
      (comap_measurable (ξ t)).mono (le_iSup₂ (f := fun i (_ : i ∈ Set.Iio (t + 1)) =>
        MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ)) t (Nat.lt_succ_self t))
        le_rfl
    have : θ (t + 1) = fun ω => θ t ω - γ t • G (θ t ω) (ξ t ω) := funext (hθ t)
    rw [this]
    exact hθt.sub ((hGmeas.comp (hθt.prodMk hξt)).const_smul _)


omit [IsProbabilityMeasure μ] in
private theorem indepFun_iterate {G : E → Ξ → E} (hGmeas : Measurable (Function.uncurry G))
    {ξ : ℕ → Ω → Ξ} (hξmeas : ∀ t, Measurable (ξ t)) (hξindep : iIndepFun ξ μ)
    {γ : ℕ → ℝ} {θ₀ : E} {θ : ℕ → Ω → E} (hθ0 : ∀ ω, θ 0 ω = θ₀)
    (hθ : ∀ t ω, θ (t + 1) ω = θ t ω - γ t • G (θ t ω) (ξ t ω)) (t : ℕ) :
    IndepFun (θ t) (ξ t) μ := by
  have hind := indep_iSup_of_disjoint (m := fun i => MeasurableSpace.comap (ξ i) inferInstance)
    (fun i => (hξmeas i).comap_le) ((iIndepFun_iff_iIndep _ _ _).mp hξindep)
    (S := Set.Iio t) (T := {t}) (by simp)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
  · exact (measurable_iterate_past hGmeas hθ0 hθ t).comap_le
  · exact le_iSup₂ (f := fun i (_ : i ∈ ({t} : Set ℕ)) =>
      MeasurableSpace.comap (ξ i) (inferInstance : MeasurableSpace Ξ)) t rfl


private theorem integral_inner_stochastic_eq {X : Ω → E} {Y : Ω → Ξ} (hX : Measurable X)
    (hY : Measurable Y) (hind : IndepFun X Y μ) {ν : Measure Ξ} [IsProbabilityMeasure ν]
    (hlaw : μ.map Y = ν) {G : E → Ξ → E} (hGmeas : Measurable (Function.uncurry G)) {B : ℝ}
    (hGbound : ∀ θ ξ, ‖G θ ξ‖ ≤ B) {c : E} {C : ℝ} (hXb : ∀ ω, ‖X ω - c‖ ≤ C) :
    ∫ ω, ⟪X ω - c, G (X ω) (Y ω)⟫ ∂μ = ∫ ω, ⟪X ω - c, ∫ ξ, G (X ω) ξ ∂ν⟫ ∂μ := by
  set h : E × Ξ → ℝ := fun p => ⟪p.1 - c, G p.1 p.2⟫ with hh_def
  have hh : Measurable h :=
    Measurable.inner (f := fun p : E × Ξ => p.1 - c) (measurable_fst.sub_const c) hGmeas
  have hF : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hmap : μ.map (fun ω => (X ω, Y ω)) = (μ.map X).prod ν := by
    rw [← hlaw]
    exact (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).mp hind
  have hint_μ : Integrable (h ∘ fun ω => (X ω, Y ω)) μ := by
    refine Integrable.of_bound (hh.comp hF).aestronglyMeasurable (C * B) (ae_of_all _ fun ω => ?_)
    simp only [Function.comp_apply, hh_def, Real.norm_eq_abs]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hC : 0 ≤ C := (norm_nonneg _).trans (hXb ω)
    exact mul_le_mul (hXb ω) (hGbound _ _) (norm_nonneg _) hC
  have hint_prod : Integrable h ((μ.map X).prod ν) := by
    rw [← hmap]; exact (integrable_map_measure hh.aestronglyMeasurable hF.aemeasurable).mpr hint_μ
  have hGint : ∀ θ, Integrable (G θ) ν := fun θ =>
    Integrable.of_bound (hGmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      B (ae_of_all _ (hGbound θ))
  calc ∫ ω, ⟪X ω - c, G (X ω) (Y ω)⟫ ∂μ = ∫ ω, h (X ω, Y ω) ∂μ := rfl
    _ = ∫ p, h p ∂(μ.map fun ω => (X ω, Y ω)) :=
        (integral_map hF.aemeasurable hh.aestronglyMeasurable).symm
    _ = ∫ p, h p ∂((μ.map X).prod ν) := by rw [hmap]
    _ = ∫ x, ∫ y, h (x, y) ∂ν ∂(μ.map X) := integral_prod h hint_prod
    _ = ∫ ω, ∫ y, h (X ω, y) ∂ν ∂μ :=
        integral_map hX.aemeasurable hh.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    _ = ∫ ω, ⟪X ω - c, ∫ ξ, G (X ω) ξ ∂ν⟫ ∂μ :=
        integral_congr_ae (ae_of_all _ fun ω => by
          simp only [hh_def]; exact integral_inner (𝕜 := ℝ) (hGint (X ω)) _)


private theorem harmonic_gamma_bounds {B D : ℝ} (hB : 0 < B) (hD : 0 < D) {t : ℕ} (ht : 0 < t) :
    ∑ k ∈ Finset.range t, (D / (B * √((k : ℝ) + 1))) ^ 2 ≤ D ^ 2 / B ^ 2 * (1 + log t) ∧
      D * √t / B ≤ ∑ k ∈ Finset.range t, D / (B * √((k : ℝ) + 1)) := by
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  constructor
  · have hh : ∑ k ∈ Finset.range t, (D / (B * √((k : ℝ) + 1))) ^ 2 =
        D ^ 2 / B ^ 2 * (harmonic t : ℝ) := by
      rw [harmonic, Rat.cast_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [div_pow, mul_pow, sq_sqrt (by positivity)]
      push_cast
      field_simp
    rw [hh]
    gcongr
    exact harmonic_le_one_add_log t
  · have hle : ∀ k ∈ Finset.range t, D / (B * √t) ≤ D / (B * √((k : ℝ) + 1)) := by
      intro k hk
      have hk' : (k : ℝ) + 1 ≤ t := by
        have := Finset.mem_range.mp hk; exact_mod_cast this
      apply div_le_div_of_nonneg_left hD.le (by positivity)
      gcongr
    calc D * √t / B = ∑ _k ∈ Finset.range t, D / (B * √t) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          have hs : 0 < √(t : ℝ) := sqrt_pos.mpr htpos
          field_simp
          rw [sq_sqrt htpos.le]
      _ ≤ _ := Finset.sum_le_sum hle

/-- **Convergence of stochastic gradient descent** (convex, nonsmooth). Let `f` be convex on a
finite-dimensional real inner product space `E`. Let `ξ₀, ξ₁, …` be independent random variables
with common law `ν`, and let `G : E → Ξ → E` be jointly measurable with `‖G θ ξ‖ ≤ B` and with
mean `∫ G(θ, ξ) dν(ξ)` a subgradient of `f` at every `θ`. Run
`θ (t + 1) = θ t - γₜ G(θ t, ξₜ)` from a deterministic `θ₀` with `γₜ = D / (B √(t + 1))`. Then
for every point `θ⋆` with `‖θ₀ - θ⋆‖ ≤ D` (in particular a minimizer) and every `t ≥ 1`, the
weighted average `θ̄ₜ = (∑_{s<t} γₛ θₛ) / (∑_{s<t} γₛ)` satisfies
`E[f(θ̄ₜ)] - f(θ⋆) ≤ D B (2 + log t) / (2 √t)`.
Source: F. Bach, *Learning Theory from First Principles*, MIT Press (2024), Section 5.4,
Proposition 5.7, under assumptions (H-1) (unbiased gradient) and (H-2) (bounded gradient), with
the stochastic gradients given by independent gradient functions as suggested after (H-2); the
source indexes steps from `1` (`γₜ = (D / B) / √t` multiplies the gradient at `θₜ₋₁`), assumes `θ⋆`
is a minimizer and `f` is `B`-Lipschitz, which follows here from the bound on the subgradients.
Proof: as in the source, the distance recursion of the subgradient method in expectation, where
the independence of `ξₜ` from `θₜ` (a measurable function of `ξ₀, …, ξₜ₋₁`) and Fubini's theorem
give `E⟪θₜ - θ⋆, G(θₜ, ξₜ)⟫ = E⟪θₜ - θ⋆, ∫ G(θₜ, ξ) dν(ξ)⟫ ≥ E[f(θₜ)] - f(θ⋆)`, followed by
Jensen's inequality for the average iterate. -/
theorem integral_sgd_average_sub_le
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {θstar : E}
    {ν : Measure Ξ} [IsProbabilityMeasure ν] {G : E → Ξ → E}
    (hGmeas : Measurable (Function.uncurry G)) {B D : ℝ} (hB : 0 < B) (hD : 0 < D)
    (hGbound : ∀ θ ξ, ‖G θ ξ‖ ≤ B)
    (hGmean : ∀ θ y, f θ + ⟪∫ ξ, G θ ξ ∂ν, y - θ⟫ ≤ f y)
    {ξ : ℕ → Ω → Ξ} (hξmeas : ∀ t, Measurable (ξ t)) (hξindep : iIndepFun ξ μ)
    (hξlaw : ∀ t, μ.map (ξ t) = ν)
    {θ₀ : E} (hdist : ‖θ₀ - θstar‖ ≤ D) {θ : ℕ → Ω → E} (hθ0 : ∀ ω, θ 0 ω = θ₀)
    (hθ : ∀ t ω, θ (t + 1) ω = θ t ω - (D / (B * √((t : ℝ) + 1))) • G (θ t ω) (ξ t ω))
    {t : ℕ} (ht : 0 < t) :
    ∫ ω, f ((∑ s ∈ Finset.range t, D / (B * √((s : ℝ) + 1)))⁻¹ •
        ∑ s ∈ Finset.range t, (D / (B * √((s : ℝ) + 1))) • θ s ω) ∂μ - f θstar ≤
      D * B * (2 + log t) / (2 * √t) := by
  set γ : ℕ → ℝ := fun k => D / (B * √((k : ℝ) + 1)) with hγ
  have hγpos : ∀ k, 0 < γ k := fun k => by positivity
  set m : E → E := fun θ => ∫ ξ, G θ ξ ∂ν with hm
  -- Measurability.
  have hθmeas : ∀ s, Measurable (θ s) := fun s =>
    (measurable_iterate_past (γ := γ) hGmeas hθ0 hθ s).mono
      (iSup₂_le fun i _ => (hξmeas i).comap_le) le_rfl
  have hGθmeas : ∀ s, Measurable fun ω => G (θ s ω) (ξ s ω) := fun s =>
    hGmeas.comp ((hθmeas s).prodMk (hξmeas s))
  have hmmeas : Measurable m :=
    (hGmeas.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  -- `f` is `B`-Lipschitz, hence continuous.
  have hmnorm : ∀ θ, ‖m θ‖ ≤ B := fun θ => by
    have := norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all _ (hGbound θ))
    simpa using this
  have hflip : ∀ x y, f x - f y ≤ B * ‖x - y‖ := by
    intro x y
    have h1 := hGmean x y
    have h2 : ⟪m x, y - x⟫ ≥ -(B * ‖x - y‖) := by
      have := abs_real_inner_le_norm (m x) (y - x)
      have h3 : ‖y - x‖ = ‖x - y‖ := norm_sub_rev _ _
      nlinarith [abs_le.mp (this.trans (mul_le_mul_of_nonneg_right (hmnorm x) (norm_nonneg _))),
        hmnorm x]
    linarith
  have hfcont : Continuous f := by
    have : LipschitzWith ⟨B, hB.le⟩ f := LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, dist_eq_norm]
      change |f x - f y| ≤ B * ‖x - y‖
      have hyx := hflip y x
      rw [norm_sub_rev] at hyx
      exact abs_le.mpr ⟨by linarith, hflip x y⟩
    exact this.continuous
  -- Deterministic bound on the iterates.
  set K : ℝ := D + B * ∑ s ∈ Finset.range t, γ s with hK
  have hbound_iter : ∀ s ω, ‖θ s ω - θstar‖ ≤ D + B * ∑ k ∈ Finset.range s, γ k := by
    intro s ω
    induction s with
    | zero => simpa [hθ0] using hdist
    | succ s ih =>
      rw [hθ s ω, Finset.sum_range_succ,
        show θ s ω - γ s • G (θ s ω) (ξ s ω) - θstar = (θ s ω - θstar) - γ s • G (θ s ω) (ξ s ω)
          by abel]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hγpos s)]
      nlinarith [hGbound (θ s ω) (ξ s ω), hγpos s]
  have hKmono : ∀ s ≤ t, D + B * ∑ k ∈ Finset.range s, γ k ≤ K := by
    intro s hs
    have : ∑ k ∈ Finset.range s, γ k ≤ ∑ k ∈ Finset.range t, γ k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hs)
        fun k _ _ => (hγpos k).le
    nlinarith
  have hK0 : 0 ≤ K := by
    have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range t) => (hγpos k).le
    nlinarith
  -- Integrability of bounded measurable functions.
  have bint : ∀ {g : Ω → ℝ}, Measurable g → (∃ C, ∀ ω, |g ω| ≤ C) → Integrable g μ := by
    intro g hg ⟨C, hC⟩
    exact Integrable.of_bound hg.aestronglyMeasurable C (ae_of_all _ fun ω => by
      simpa [Real.norm_eq_abs] using hC ω)
  have hfbound : ∀ x, |f x| ≤ |f θstar| + B * ‖x - θstar‖ := by
    intro x
    have h1 := hflip x θstar
    have h2 := hflip θstar x
    rw [norm_sub_rev] at h2
    rw [abs_le]; constructor <;> cases abs_cases (f θstar) <;> linarith
  have hfint : ∀ s, Integrable (fun ω => f (θ s ω)) μ := fun s =>
    bint (hfcont.measurable.comp (hθmeas s))
      ⟨|f θstar| + B * (D + B * ∑ k ∈ Finset.range s, γ k), fun ω =>
        (hfbound _).trans (by gcongr; exact hbound_iter s ω)⟩
  set r : ℕ → ℝ := fun s => ∫ ω, ‖θ s ω - θstar‖ ^ 2 ∂μ with hr
  -- One step in expectation.
  have hstep : ∀ s, 2 * γ s * ((∫ ω, f (θ s ω) ∂μ) - f θstar) ≤
      r s - r (s + 1) + γ s ^ 2 * B ^ 2 := by
    intro s
    set C := D + B * ∑ k ∈ Finset.range s, γ k with hC
    have hC0 : 0 ≤ C := by
      have := Finset.sum_nonneg fun k (_ : k ∈ Finset.range s) => (hγpos k).le
      nlinarith
    have hsqint : ∀ u, Integrable (fun ω => ‖θ u ω - θstar‖ ^ 2) μ := fun u =>
      bint (((hθmeas u).sub_const θstar).norm.pow_const 2)
        ⟨(D + B * ∑ k ∈ Finset.range u, γ k) ^ 2, fun ω => by
          rw [abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hbound_iter u ω) 2⟩
    have hinnerint : Integrable (fun ω => ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫) μ :=
      bint (Measurable.inner ((hθmeas s).sub_const θstar) (hGθmeas s))
        ⟨C * B, fun ω => (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (hbound_iter s ω) (hGbound _ _) (norm_nonneg _) hC0)⟩
    have hinnerint' : Integrable (fun ω => ⟪θ s ω - θstar, m (θ s ω)⟫) μ :=
      bint (Measurable.inner ((hθmeas s).sub_const θstar) (hmmeas.comp (hθmeas s)))
        ⟨C * B, fun ω => (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (hbound_iter s ω) (hmnorm _) (norm_nonneg _) hC0)⟩
    -- Pointwise expansion.
    have hpt : ∀ ω, ‖θ (s + 1) ω - θstar‖ ^ 2 ≤ ‖θ s ω - θstar‖ ^ 2 -
        2 * γ s * ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫ + γ s ^ 2 * B ^ 2 := by
      intro ω
      rw [hθ s ω, show θ s ω - γ s • G (θ s ω) (ξ s ω) - θstar =
        (θ s ω - θstar) - γ s • G (θ s ω) (ξ s ω) by abel, norm_sub_sq_real,
        real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos (hγpos s)]
      have := pow_le_pow_left₀ (norm_nonneg _) (hGbound (θ s ω) (ξ s ω)) 2
      nlinarith [sq_nonneg (γ s)]
    have hint_step : r (s + 1) ≤ r s - 2 * γ s * ∫ ω, ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫ ∂μ +
        γ s ^ 2 * B ^ 2 := by
      have h1 : Integrable (fun ω => ‖θ s ω - θstar‖ ^ 2 -
          2 * γ s * ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫) μ :=
        (hsqint s).sub (hinnerint.const_mul _)
      have h2 : Integrable (fun ω => ‖θ s ω - θstar‖ ^ 2 -
          2 * γ s * ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫ + γ s ^ 2 * B ^ 2) μ :=
        h1.add (integrable_const _)
      have hmono := integral_mono (hsqint (s + 1)) h2 hpt
      have heq : ∫ ω, (‖θ s ω - θstar‖ ^ 2 - 2 * γ s * ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫ +
          γ s ^ 2 * B ^ 2) ∂μ = r s - 2 * γ s * ∫ ω, ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫ ∂μ +
            γ s ^ 2 * B ^ 2 := by
        rw [integral_add h1 (integrable_const _), integral_sub (hsqint s) (hinnerint.const_mul _),
          integral_const_mul, integral_const]
        simp [hr]
      rw [heq] at hmono
      exact hmono
    have hkey := integral_inner_stochastic_eq (hθmeas s) (hξmeas s)
      (indepFun_iterate hGmeas hξmeas hξindep hθ0 hθ s) (hξlaw s) hGmeas hGbound
      (c := θstar) (hbound_iter s)
    have hsub : ∫ ω, f (θ s ω) ∂μ - f θstar ≤ ∫ ω, ⟪θ s ω - θstar, m (θ s ω)⟫ ∂μ := by
      have h1 : Integrable (fun ω => f (θ s ω) - f θstar) μ := (hfint s).sub (integrable_const _)
      have hmono := integral_mono h1 hinnerint' fun ω => by
        have := hGmean (θ s ω) θstar
        have h2 : ⟪m (θ s ω), θstar - θ s ω⟫ = -⟪θ s ω - θstar, m (θ s ω)⟫ := by
          rw [real_inner_comm, ← inner_neg_left, neg_sub]
        simp only [hm] at h2 ⊢
        linarith
      rw [integral_sub (hfint s) (integrable_const _), integral_const] at hmono
      simpa using hmono
    have : ∫ ω, ⟪θ s ω - θstar, G (θ s ω) (ξ s ω)⟫ ∂μ = ∫ ω, ⟪θ s ω - θstar, m (θ s ω)⟫ ∂μ :=
      hkey
    nlinarith [hγpos s]
  -- Summing.
  have hsum : ∀ n, 2 * ∑ s ∈ Finset.range n, γ s * ((∫ ω, f (θ s ω) ∂μ) - f θstar) ≤
      r 0 - r n + B ^ 2 * ∑ s ∈ Finset.range n, γ s ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      nlinarith [hstep n]
  have hr0 : r 0 ≤ D ^ 2 := by
    simp only [hr, hθ0, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hrn : 0 ≤ r t := integral_nonneg fun ω => sq_nonneg _
  -- Jensen for the average iterate.
  set Γ := ∑ s ∈ Finset.range t, γ s with hΓ
  have hΓpos : 0 < Γ := Finset.sum_pos (fun k _ => hγpos k) (Finset.nonempty_range_iff.mpr ht.ne')
  have havg : ∀ ω, Γ⁻¹ • ∑ s ∈ Finset.range t, γ s • θ s ω =
      ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) • θ s ω := by
    intro ω; rw [Finset.smul_sum]; simp_rw [smul_smul]
  have hw0 : ∀ s ∈ Finset.range t, 0 ≤ Γ⁻¹ * γ s := fun s _ => by
    have := hγpos s; positivity
  have hw1 : ∑ s ∈ Finset.range t, Γ⁻¹ * γ s = 1 := by
    rw [← Finset.mul_sum, inv_mul_cancel₀ hΓpos.ne']
  have hjensen : ∀ ω, f (Γ⁻¹ • ∑ s ∈ Finset.range t, γ s • θ s ω) ≤
      ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) * f (θ s ω) := by
    intro ω
    rw [havg]
    simpa [smul_eq_mul] using hf.map_sum_le hw0 hw1 (fun s _ => Set.mem_univ (θ s ω))
  have hbarmeas : Measurable fun ω => f (Γ⁻¹ • ∑ s ∈ Finset.range t, γ s • θ s ω) :=
    hfcont.measurable.comp ((Finset.measurable_sum _ fun s _ =>
      (hθmeas s).const_smul (γ s)).const_smul _)
  have hbarbound : ∀ ω, ‖Γ⁻¹ • ∑ s ∈ Finset.range t, γ s • θ s ω - θstar‖ ≤ K := by
    intro ω
    rw [havg, show ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) • θ s ω - θstar =
        ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) • (θ s ω - θstar) by
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hw1, one_smul]]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ s ∈ Finset.range t, ‖(Γ⁻¹ * γ s) • (θ s ω - θstar)‖
        ≤ ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) * K := by
          refine Finset.sum_le_sum fun s hs => ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 s hs)]
          exact mul_le_mul_of_nonneg_left ((hbound_iter s ω).trans
            (hKmono s (Finset.mem_range.mp hs).le)) (hw0 s hs)
      _ = K := by rw [← Finset.sum_mul, hw1, one_mul]
  have hbarint : Integrable (fun ω => f (Γ⁻¹ • ∑ s ∈ Finset.range t, γ s • θ s ω)) μ :=
    bint hbarmeas ⟨|f θstar| + B * K, fun ω => (hfbound _).trans (by gcongr; exact hbarbound ω)⟩
  have hE : ∫ ω, f (Γ⁻¹ • ∑ s ∈ Finset.range t, γ s • θ s ω) ∂μ ≤
      ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) * ∫ ω, f (θ s ω) ∂μ := by
    calc _ ≤ ∫ ω, ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) * f (θ s ω) ∂μ :=
          integral_mono hbarint (integrable_finsetSum _ fun s _ => (hfint s).const_mul _)
            hjensen
      _ = _ := by
          rw [integral_finsetSum _ fun s _ => (hfint s).const_mul _]
          simp_rw [integral_const_mul]
  -- Final arithmetic.
  obtain ⟨hsq, hlin⟩ := harmonic_gamma_bounds hB hD ht
  have hgap : ∫ ω, f (Γ⁻¹ • ∑ s ∈ Finset.range t, γ s • θ s ω) ∂μ - f θstar ≤
      Γ⁻¹ * ∑ s ∈ Finset.range t, γ s * ((∫ ω, f (θ s ω) ∂μ) - f θstar) := by
    have : ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) * ∫ ω, f (θ s ω) ∂μ - f θstar =
        Γ⁻¹ * ∑ s ∈ Finset.range t, γ s * ((∫ ω, f (θ s ω) ∂μ) - f θstar) := by
      rw [Finset.mul_sum]
      have h1 : f θstar = ∑ s ∈ Finset.range t, (Γ⁻¹ * γ s) * f θstar := by
        rw [← Finset.sum_mul, hw1, one_mul]
      conv_lhs => rw [h1]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      ring
    linarith
  have hS := hsum t
  have htpos : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  have hlog : 0 ≤ log t := log_nonneg (by exact_mod_cast ht)
  have hs : 0 < √(t : ℝ) := sqrt_pos.mpr htpos
  have hnum : 2 * ∑ s ∈ Finset.range t, γ s * ((∫ ω, f (θ s ω) ∂μ) - f θstar) ≤
      D ^ 2 * (2 + log t) := by
    have hB2 : B ^ 2 * (D ^ 2 / B ^ 2 * (1 + log t)) = D ^ 2 * (1 + log t) := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg B)]
  refine hgap.trans ?_
  rw [inv_mul_le_iff₀ hΓpos]
  have hrhs : D * B * (2 + log t) / (2 * √t) * (D * √t / B) = D ^ 2 * (2 + log t) / 2 := by
    field_simp
  have hpos : 0 ≤ D * B * (2 + log t) / (2 * √t) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlin hpos]

end MathlibExt.Analysis.Convex.StochasticGradientDescent
