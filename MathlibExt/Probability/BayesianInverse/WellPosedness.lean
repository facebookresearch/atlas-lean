/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.HellingerDistance
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bayesian inverse problems: posterior well-posedness and approximation in Hellinger distance

In the Bayesian approach to an inverse problem `y = G(u) + η`, the posterior is the prior `μ₀`
reweighted by the likelihood: `dμ^y/dμ₀ (u) = exp(-Φ(u; y)) / Z(y)` with
`Z(y) = ∫ exp(-Φ(u; y)) μ₀(du)` (Dashti and Stuart, *The Bayesian Approach to Inverse Problems*,
arXiv:1302.6989v4, 2015, Theorem 3.4 and equation (4.1)). For Gaussian noise `η ~ N(0, Γ)` the
potential is the misfit `Φ(u; y) = ½ |Γ^{-1/2}(y - G(u))|²`.

This file proves the two stability results of their Section 4, for a finite-dimensional unknown:

* `hellingerDist_posterior_le_mul_dist` (**well-posedness**, Dashti-Stuart Theorem 4.5 with
  `X' = X` finite-dimensional): under Assumptions 4.2 and the integrability condition, the
  posterior is locally Lipschitz in the data in the Hellinger distance.
* `hellingerDist_posterior_approx_le` (**approximation**, Dashti-Stuart Theorem 4.9 with
  `X' = X` finite-dimensional): a perturbation of the potential of size `ψ(N)` moves the
  posterior by `O(ψ(N))` in the Hellinger distance.

Both rest on `hellingerDist_posterior_le`, a statement on an arbitrary measurable space: if two
potentials share a lower bound `-M₁`, differ by at most `M₂ δ`, have normalising constants at
least `z > 0`, and `exp(M₁)(1 + M₂²)` is `μ₀`-integrable, then the posteriors are within
`|δ| (W/(4z) + W²/(2z²))^{1/2}` in Hellinger distance, where `W = ∫ exp(M₁)(1 + M₂²) dμ₀`. Its
proof is the computation in the proofs of Theorems 4.5 and 4.9. The finite-dimensional
hypothesis is used only to obtain the uniform lower bound on the normalising constants
(Theorems 4.3 and 4.8), from continuity of the potential on a compact ball of positive prior
mass.

The functions `M₁`, `M₂` of Assumptions 4.2 depend on `(r, ‖u‖)`; here `r` is fixed and they are
functions of `‖u‖`. As in the source both are nondecreasing (for `M₁` this is used only for
measurability); strict positivity of `M₂` is not needed.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.BayesianInverse

open MeasureTheory Filter Topology
open MathlibExt.Probability.HellingerDistance
open scoped ENNReal

variable {U : Type*} [MeasurableSpace U]

/-- **Normalising constant of a posterior.** For a prior `μ₀` and a potential `Φ`,
`Z = ∫ exp(-Φ(u)) μ₀(du)` (Dashti and Stuart, arXiv:1302.6989v4, equation (4.1b)). When `exp(-Φ)`
is not `μ₀`-integrable the Bochner integral is `0`, and so is the posterior, as for Mathlib's
`Measure.tilted`. -/
noncomputable def normalizer (μ₀ : Measure U) (Φ : U → ℝ) : ℝ :=
  ∫ u, Real.exp (-Φ u) ∂μ₀

/-- **Posterior measure of a potential.** The measure with density `exp(-Φ(u)) / Z` with respect
to the prior `μ₀` (Dashti and Stuart, arXiv:1302.6989v4, equations (3.6) and (4.1a)). It is a
probability measure when `0 < Z` and `exp(-Φ)` is integrable
(`isProbabilityMeasure_posterior`). -/
noncomputable def posterior (μ₀ : Measure U) (Φ : U → ℝ) : Measure U :=
  μ₀.withDensity fun u ↦ ENNReal.ofReal (Real.exp (-Φ u) / normalizer μ₀ Φ)

/-- **The posterior is a probability measure.** If `exp(-Φ)` is `μ₀`-integrable and the
normalising constant is positive, then `posterior μ₀ Φ` has total mass one. -/
theorem isProbabilityMeasure_posterior {μ₀ : Measure U} {Φ : U → ℝ}
    (hint : Integrable (fun u ↦ Real.exp (-Φ u)) μ₀) (hZ : 0 < normalizer μ₀ Φ) :
    IsProbabilityMeasure (posterior μ₀ Φ) := by
  constructor
  rw [posterior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
      (Eventually.of_forall fun u ↦ by positivity), integral_div]
  simp only [normalizer] at hZ ⊢
  rw [div_self hZ.ne', ENNReal.ofReal_one]

/-- `|exp x - exp y| ≤ exp c · |x - y|` when `x, y ≤ c`. -/
private lemma abs_exp_sub_exp_le {x y c : ℝ} (hx : x ≤ c) (hy : y ≤ c) :
    |Real.exp x - Real.exp y| ≤ Real.exp c * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]; exact this hy hx (le_of_not_ge hxy)
  have h1 : Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := by
    have := Real.add_one_le_exp (x - y)
    have hxy' : Real.exp x = Real.exp y * Real.exp (x - y) := by
      rw [← Real.exp_add]; ring_nf
    rw [hxy']
    nlinarith [Real.exp_pos y]
  rw [abs_sub_comm, abs_of_nonneg (by linarith [Real.exp_le_exp.2 hxy]),
    abs_sub_comm, abs_of_nonneg (by linarith)]
  calc Real.exp y - Real.exp x ≤ Real.exp y * (y - x) := h1
    _ ≤ Real.exp c * (y - x) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hy) (by linarith)

/-- Algebraic core of the normalising-constant term: with `sᵢ = √Zᵢ`, `Zᵢ ≥ z > 0` and
`|Z₁ - Z₂| ≤ D`, one has `(1/s₁ - 1/s₂)² Z₂ ≤ D² / (2 z²)`. -/
private lemma inv_sqrt_sub_sq_mul_le {Z₁ Z₂ z D : ℝ} (hz : 0 < z) (h₁ : z ≤ Z₁) (h₂ : z ≤ Z₂)
    (hD : |Z₁ - Z₂| ≤ D) :
    (1 / √Z₁ - 1 / √Z₂) ^ 2 * Z₂ ≤ D ^ 2 / (2 * z ^ 2) := by
  have hZ₁ : 0 < Z₁ := hz.trans_le h₁
  have hZ₂ : 0 < Z₂ := hz.trans_le h₂
  set s₁ := √Z₁ with hs₁
  set s₂ := √Z₂ with hs₂
  have hs₁p : 0 < s₁ := Real.sqrt_pos.2 hZ₁
  have hs₂p : 0 < s₂ := Real.sqrt_pos.2 hZ₂
  have e₁ : s₁ ^ 2 = Z₁ := Real.sq_sqrt hZ₁.le
  have e₂ : s₂ ^ 2 = Z₂ := Real.sq_sqrt hZ₂.le
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have hsq : (Z₁ - Z₂) ^ 2 ≤ D ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hD 2
  have hsum : 2 * z ≤ (s₁ + s₂) ^ 2 := by nlinarith [mul_pos hs₁p hs₂p]
  have hdiff : (s₂ - s₁) ^ 2 * (s₁ + s₂) ^ 2 = (Z₁ - Z₂) ^ 2 := by
    rw [← e₁, ← e₂]; ring
  have step1 : (1 / s₁ - 1 / s₂) ^ 2 * Z₂ = (s₂ - s₁) ^ 2 / Z₁ := by
    rw [← e₁, ← e₂]; field_simp
  rw [step1]
  have step2 : (s₂ - s₁) ^ 2 ≤ D ^ 2 / (2 * z) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (s₂ - s₁)]
  calc (s₂ - s₁) ^ 2 / Z₁ ≤ (D ^ 2 / (2 * z)) / z := by
        gcongr
    _ = D ^ 2 / (2 * z ^ 2) := by field_simp

/-- **Hellinger perturbation bound for posteriors.** On any measurable space, let `Φ₁`, `Φ₂` be
measurable potentials with `-M₁ ≤ Φᵢ` and `|Φ₁ - Φ₂| ≤ M₂ δ` pointwise, let
`w = exp(M₁)(1 + M₂²)` be `μ₀`-integrable with integral at most `W`, and let both normalising
constants be at least `z > 0`. Then
`d_Hell(μ₁, μ₂) ≤ |δ| (W/(4z) + W²/(2z²))^{1/2}`.
This is the estimate in the proofs of Theorems 4.5 and 4.9 of Dashti and Stuart
(arXiv:1302.6989v4), with an explicit constant: `|Z₁ - Z₂| ≤ |δ| W` and the splitting of
`2 d_Hell²` into the terms `I₁` and `I₂`. -/
theorem hellingerDist_posterior_le (μ₀ : Measure U) [SigmaFinite μ₀] {Φ₁ Φ₂ M₁ M₂ : U → ℝ}
    {δ z W : ℝ} (hΦ₁ : Measurable Φ₁) (hΦ₂ : Measurable Φ₂) (hM₁ : Measurable M₁)
    (hM₂ : Measurable M₂)
    (hlow₁ : ∀ u, -M₁ u ≤ Φ₁ u) (hlow₂ : ∀ u, -M₁ u ≤ Φ₂ u)
    (hdiff : ∀ u, |Φ₁ u - Φ₂ u| ≤ M₂ u * δ)
    (hint : Integrable (fun u ↦ Real.exp (M₁ u) * (1 + M₂ u ^ 2)) μ₀)
    (hW : ∫ u, Real.exp (M₁ u) * (1 + M₂ u ^ 2) ∂μ₀ ≤ W)
    (hz : 0 < z) (hZ₁ : z ≤ normalizer μ₀ Φ₁) (hZ₂ : z ≤ normalizer μ₀ Φ₂) :
    hellingerDist (posterior μ₀ Φ₁) (posterior μ₀ Φ₂) ≤
      |δ| * √(W / (4 * z) + W ^ 2 / (2 * z ^ 2)) := by
  set Z₁ := normalizer μ₀ Φ₁ with hZ₁def
  set Z₂ := normalizer μ₀ Φ₂ with hZ₂def
  set w : U → ℝ := fun u ↦ Real.exp (M₁ u) * (1 + M₂ u ^ 2) with hwdef
  have hZ₁p : 0 < Z₁ := hz.trans_le hZ₁
  have hZ₂p : 0 < Z₂ := hz.trans_le hZ₂
  have hwm : Measurable w := by fun_prop
  have hw_ge : ∀ u, Real.exp (M₁ u) ≤ w u := fun u ↦
    le_mul_of_one_le_right (Real.exp_pos _).le (by nlinarith [sq_nonneg (M₂ u)])
  have hw0 : ∀ u, 0 ≤ w u := fun u ↦ (Real.exp_pos _).le.trans (hw_ge u)
  have hW0 : 0 ≤ W := (integral_nonneg hw0).trans hW
  have hM2abs : ∀ u, |M₂ u| * |δ| ≤ (1 + M₂ u ^ 2) * |δ| := fun u ↦
    mul_le_mul_of_nonneg_right (by nlinarith [abs_nonneg (M₂ u), sq_abs (M₂ u)]) (abs_nonneg _)
  have hdiff' : ∀ u, |Φ₁ u - Φ₂ u| ≤ |M₂ u| * |δ| := fun u ↦
    (hdiff u).trans ((le_abs_self _).trans (abs_mul _ _).le)
  -- integrability of `exp(-Φᵢ)`
  have hexp_le : ∀ (Φ : U → ℝ), (∀ u, -M₁ u ≤ Φ u) → ∀ u, Real.exp (-Φ u) ≤ w u :=
    fun Φ hl u ↦ (Real.exp_le_exp.2 (by linarith [hl u])).trans (hw_ge u)
  have hint_exp : ∀ (Φ : U → ℝ), Measurable Φ → (∀ u, -M₁ u ≤ Φ u) →
      Integrable (fun u ↦ Real.exp (-Φ u)) μ₀ := fun Φ hm hl ↦
    hint.mono' (by fun_prop) (Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hexp_le Φ hl u)
  have hi₁ := hint_exp Φ₁ hΦ₁ hlow₁
  have hi₂ := hint_exp Φ₂ hΦ₂ hlow₂
  -- the normalising constants differ by at most `|δ| W`
  have hdZ : |Z₁ - Z₂| ≤ |δ| * W := by
    have hsub : Z₁ - Z₂ = ∫ u, (Real.exp (-Φ₁ u) - Real.exp (-Φ₂ u)) ∂μ₀ :=
      (integral_sub hi₁ hi₂).symm
    rw [hsub, ← Real.norm_eq_abs]
    calc ‖∫ u, (Real.exp (-Φ₁ u) - Real.exp (-Φ₂ u)) ∂μ₀‖ ≤ ∫ u, |δ| * w u ∂μ₀ := by
          refine norm_integral_le_of_norm_le (hint.const_mul _) (Eventually.of_forall fun u ↦ ?_)
          rw [Real.norm_eq_abs]
          calc |Real.exp (-Φ₁ u) - Real.exp (-Φ₂ u)|
              ≤ Real.exp (M₁ u) * |-Φ₁ u - -Φ₂ u| :=
                abs_exp_sub_exp_le (by linarith [hlow₁ u]) (by linarith [hlow₂ u])
            _ ≤ Real.exp (M₁ u) * ((1 + M₂ u ^ 2) * |δ|) := by
                gcongr
                rw [show -Φ₁ u - -Φ₂ u = -(Φ₁ u - Φ₂ u) by ring, abs_neg]
                exact (hdiff' u).trans (hM2abs u)
            _ = |δ| * w u := by simp only [hwdef]; ring
      _ = |δ| * ∫ u, w u ∂μ₀ := integral_const_mul _ _
      _ ≤ |δ| * W := mul_le_mul_of_nonneg_left hW (abs_nonneg _)
  -- square roots of the densities
  set a₁ : U → ℝ := fun u ↦ Real.exp (-Φ₁ u / 2)
  set a₂ : U → ℝ := fun u ↦ Real.exp (-Φ₂ u / 2)
  have hsqrt : ∀ (Φ : U → ℝ) (Z : ℝ), 0 ≤ Z → ∀ u : U,
      √(ENNReal.ofReal (Real.exp (-Φ u) / Z)).toReal = Real.exp (-Φ u / 2) / √Z := by
    intro Φ Z hZ u
    have hexp : Real.exp (-Φ u) = Real.exp (-Φ u / 2) ^ 2 := by
      rw [sq, ← Real.exp_add]; ring_nf
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_div (Real.exp_pos _).le, hexp,
      Real.sqrt_sq (Real.exp_pos _).le]
  -- the Hellinger distance as an integral against the prior
  have hH : hellingerDist (posterior μ₀ Φ₁) (posterior μ₀ Φ₂) =
      √((1 / 2 : ℝ) * ∫ u, (a₁ u / √Z₁ - a₂ u / √Z₂) ^ 2 ∂μ₀) := by
    rw [posterior, posterior, hellingerDist_withDensity (by fun_prop) (by fun_prop)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_ne_top)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_ne_top)]
    simp only [hsqrt Φ₁ _ hZ₁p.le, hsqrt Φ₂ _ hZ₂p.le, a₁, a₂, Z₁, Z₂]
  -- pointwise bound on the difference of square-root likelihoods
  have hpt : ∀ u, (a₁ u - a₂ u) ^ 2 ≤ δ ^ 2 / 4 * w u := by
    intro u
    have h1 : |a₁ u - a₂ u| ≤ Real.exp (M₁ u / 2) * |Φ₁ u - Φ₂ u| / 2 := by
      have := abs_exp_sub_exp_le (x := -Φ₁ u / 2) (y := -Φ₂ u / 2) (c := M₁ u / 2)
        (by linarith [hlow₁ u]) (by linarith [hlow₂ u])
      rw [show -Φ₁ u / 2 - -Φ₂ u / 2 = -((Φ₁ u - Φ₂ u) / 2) by ring, abs_neg, abs_div,
        abs_two] at this
      calc |a₁ u - a₂ u| ≤ _ := this
        _ = _ := by ring
    have h2 : |Φ₁ u - Φ₂ u| ^ 2 ≤ M₂ u ^ 2 * δ ^ 2 := by
      calc |Φ₁ u - Φ₂ u| ^ 2 ≤ (|M₂ u| * |δ|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hdiff' u) 2
        _ = M₂ u ^ 2 * δ ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
    have h3 : Real.exp (M₁ u / 2) ^ 2 = Real.exp (M₁ u) := by
      rw [sq, ← Real.exp_add]; ring_nf
    calc (a₁ u - a₂ u) ^ 2 = |a₁ u - a₂ u| ^ 2 := (sq_abs _).symm
      _ ≤ (Real.exp (M₁ u / 2) * |Φ₁ u - Φ₂ u| / 2) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = Real.exp (M₁ u) * |Φ₁ u - Φ₂ u| ^ 2 / 4 := by rw [← h3]; ring
      _ ≤ Real.exp (M₁ u) * (M₂ u ^ 2 * δ ^ 2) / 4 := by gcongr
      _ ≤ δ ^ 2 / 4 * w u := by
          simp only [hwdef]
          nlinarith [Real.exp_pos (M₁ u), sq_nonneg δ, sq_nonneg (M₂ u),
            mul_nonneg (Real.exp_pos (M₁ u)).le (sq_nonneg δ)]
  have ha₁ : Measurable a₁ := by fun_prop
  have ha₂ : Measurable a₂ := by fun_prop
  have hint_d : Integrable (fun u ↦ (a₁ u - a₂ u) ^ 2) μ₀ :=
    (hint.const_mul (δ ^ 2 / 4)).mono' (by fun_prop) (Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt u)
  have ha₂sq : ∀ u, a₂ u ^ 2 = Real.exp (-Φ₂ u) := fun u ↦ by
    simp only [a₂]; rw [sq, ← Real.exp_add]; ring_nf
  -- dominate the integrand
  set c := (1 / √Z₁ - 1 / √Z₂) with hc
  have hdom : ∀ u, (a₁ u / √Z₁ - a₂ u / √Z₂) ^ 2 ≤
      2 / Z₁ * (a₁ u - a₂ u) ^ 2 + 2 * c ^ 2 * Real.exp (-Φ₂ u) := by
    intro u
    have hs : √Z₁ ^ 2 = Z₁ := Real.sq_sqrt hZ₁p.le
    have hs0 : 0 < √Z₁ := Real.sqrt_pos.2 hZ₁p
    have hsplit : a₁ u / √Z₁ - a₂ u / √Z₂ = (a₁ u - a₂ u) / √Z₁ + a₂ u * c := by
      simp only [hc]; ring
    rw [hsplit, ← ha₂sq]
    have : ((a₁ u - a₂ u) / √Z₁) ^ 2 = (a₁ u - a₂ u) ^ 2 / Z₁ := by rw [div_pow, hs]
    calc ((a₁ u - a₂ u) / √Z₁ + a₂ u * c) ^ 2
        ≤ 2 * ((a₁ u - a₂ u) / √Z₁) ^ 2 + 2 * (a₂ u * c) ^ 2 := by
          nlinarith [sq_nonneg ((a₁ u - a₂ u) / √Z₁ - a₂ u * c)]
      _ = 2 / Z₁ * (a₁ u - a₂ u) ^ 2 + 2 * c ^ 2 * a₂ u ^ 2 := by rw [this]; ring
  have hI : ∫ u, (a₁ u / √Z₁ - a₂ u / √Z₂) ^ 2 ∂μ₀ ≤
      δ ^ 2 * (W / (2 * z) + W ^ 2 / z ^ 2) := by
    calc ∫ u, (a₁ u / √Z₁ - a₂ u / √Z₂) ^ 2 ∂μ₀
        ≤ ∫ u, (2 / Z₁ * (a₁ u - a₂ u) ^ 2 + 2 * c ^ 2 * Real.exp (-Φ₂ u)) ∂μ₀ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _)
            ((hint_d.const_mul _).add (hi₂.const_mul _)) (Eventually.of_forall hdom)
      _ = 2 / Z₁ * ∫ u, (a₁ u - a₂ u) ^ 2 ∂μ₀ + 2 * c ^ 2 * Z₂ := by
          rw [integral_add (hint_d.const_mul _) (hi₂.const_mul _), integral_const_mul,
            integral_const_mul]
          rfl
      _ ≤ 2 / z * (δ ^ 2 / 4 * W) + 2 * (|δ| * W) ^ 2 / (2 * z ^ 2) := by
          gcongr ?_ + ?_
          · calc 2 / Z₁ * ∫ u, (a₁ u - a₂ u) ^ 2 ∂μ₀ ≤ 2 / Z₁ * (δ ^ 2 / 4 * W) := by
                  gcongr
                  calc ∫ u, (a₁ u - a₂ u) ^ 2 ∂μ₀ ≤ ∫ u, δ ^ 2 / 4 * w u ∂μ₀ :=
                        integral_mono hint_d (hint.const_mul _) hpt
                    _ = δ ^ 2 / 4 * ∫ u, w u ∂μ₀ := integral_const_mul _ _
                    _ ≤ δ ^ 2 / 4 * W := by gcongr
              _ ≤ 2 / z * (δ ^ 2 / 4 * W) := by gcongr
          · rw [mul_assoc, mul_div_assoc]
            gcongr
            exact inv_sqrt_sub_sq_mul_le hz hZ₁ hZ₂ hdZ
      _ = δ ^ 2 * (W / (2 * z) + W ^ 2 / z ^ 2) := by
          rw [mul_pow, sq_abs]; field_simp; ring
  rw [hH, show |δ| * √(W / (4 * z) + W ^ 2 / (2 * z ^ 2)) =
      √(δ ^ 2 * (W / (4 * z) + W ^ 2 / (2 * z ^ 2))) by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]]
  refine Real.sqrt_le_sqrt ?_
  calc (1 / 2 : ℝ) * ∫ u, (a₁ u / √Z₁ - a₂ u / √Z₂) ^ 2 ∂μ₀
      ≤ (1 / 2) * (δ ^ 2 * (W / (2 * z) + W ^ 2 / z ^ 2)) := by gcongr
    _ = δ ^ 2 * (W / (4 * z) + W ^ 2 / (2 * z ^ 2)) := by field_simp; ring

/-- **Lower bound for a normalising constant.** If `Φ ≤ T` on a measurable set `K` of finite
prior mass and `exp(-Φ)` is integrable, then `exp(-T) μ₀(K) ≤ Z`. This is inequality (4.2) of
Dashti and Stuart (arXiv:1302.6989v4). -/
theorem le_normalizer_of_le_on {μ₀ : Measure U} {Φ : U → ℝ} {K : Set U} {T : ℝ}
    (hK : MeasurableSet K) (hKfin : μ₀ K ≠ ∞)
    (hint : Integrable (fun u ↦ Real.exp (-Φ u)) μ₀) (hT : ∀ u ∈ K, Φ u ≤ T) :
    Real.exp (-T) * μ₀.real K ≤ normalizer μ₀ Φ := by
  calc Real.exp (-T) * μ₀.real K = μ₀.real K • Real.exp (-T) := by
        rw [smul_eq_mul, mul_comm]
    _ ≤ ∫ u in K, Real.exp (-Φ u) ∂μ₀ :=
        setIntegral_ge_of_const_le hK hKfin
          (fun u hu ↦ Real.exp_le_exp.2 (neg_le_neg (hT u hu))) hint.integrableOn
    _ ≤ normalizer μ₀ Φ :=
        setIntegral_le_integral hint (Eventually.of_forall fun _ ↦ (Real.exp_pos _).le)

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A probability measure on a finite-dimensional space charges some closed ball centred at the
origin, and that ball is compact. -/
private lemma exists_closedBall_pos (μ₀ : Measure E) [IsProbabilityMeasure μ₀] :
    ∃ R : ℝ, 0 ≤ R ∧ 0 < μ₀.real (Metric.closedBall (0 : E) R) := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hnull : ∀ n : ℕ, μ₀ (Metric.closedBall (0 : E) n) = 0 := fun n ↦ by
    have := h n (Nat.cast_nonneg n)
    have h0 : μ₀.real (Metric.closedBall (0 : E) n) = 0 :=
      le_antisymm this measureReal_nonneg
    rwa [measureReal_eq_zero_iff] at h0
  have : μ₀ Set.univ = 0 := by
    rw [← Metric.iUnion_closedBall_nat (0 : E)]; exact measure_iUnion_null hnull
  simp at this

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- `exp(-Φ)` is integrable when `-M₁ ≤ Φ`, `Φ` is measurable and `exp(M₁)` is integrable. -/
private lemma integrable_exp_neg {μ₀ : Measure E} {Φ : E → ℝ} {M₁ : ℝ → ℝ}
    (hΦ : Measurable Φ) (hlow : ∀ u, -M₁ ‖u‖ ≤ Φ u)
    (hint : Integrable (fun u ↦ Real.exp (M₁ ‖u‖)) μ₀) :
    Integrable (fun u ↦ Real.exp (-Φ u)) μ₀ :=
  hint.mono' (by fun_prop) (Eventually.of_forall fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [hlow u]))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Integrability of `exp(M₁)(1 + M₂²)` implies that of `exp(M₁)`. -/
private lemma integrable_exp_of_integrable_mul {μ₀ : Measure E} {M₁ M₂ : ℝ → ℝ}
    (hM₁ : Measurable M₁)
    (hint : Integrable (fun u ↦ Real.exp (M₁ ‖u‖) * (1 + M₂ ‖u‖ ^ 2)) μ₀) :
    Integrable (fun u ↦ Real.exp (M₁ ‖u‖)) μ₀ :=
  hint.mono' (hM₁.comp measurable_norm).exp.aestronglyMeasurable
    (Eventually.of_forall fun u ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_mul_of_one_le_right (Real.exp_pos _).le (by nlinarith [sq_nonneg (M₂ ‖u‖)]))

/-- **The normalising constants are uniformly positive on bounded data sets.** For a
finite-dimensional unknown, a prior probability measure `μ₀` and a potential `Φ(u; y)` that is
continuous in `u`, bounded below by `-M₁(‖u‖)` and Lipschitz in `y` with constant `M₂(‖u‖)` on
`‖y‖ ≤ r` (`M₂` nondecreasing), and with `exp(M₁(‖u‖))` integrable, there is `z > 0` with
`z ≤ Z(y)` for all `‖y‖ ≤ r`. Since the hypotheses also make `exp(-Φ(·; y))`
integrable, `isProbabilityMeasure_posterior` then shows that each posterior is a probability
measure: Dashti and Stuart (arXiv:1302.6989v4), Theorem 4.3, with `X' = X` finite-dimensional. -/
theorem exists_pos_le_normalizer {Y : Type*} [SeminormedAddCommGroup Y]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (Φ : E → Y → ℝ) (M₁ M₂ : ℝ → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hcont : ∀ y, Continuous fun u ↦ Φ u y) (hM₂ : Monotone M₂)
    (hlip : ∀ u y y', ‖y‖ ≤ r → ‖y'‖ ≤ r → |Φ u y - Φ u y'| ≤ M₂ ‖u‖ * ‖y - y'‖)
    (hlow : ∀ u y, ‖y‖ ≤ r → -M₁ ‖u‖ ≤ Φ u y)
    (hint : Integrable (fun u ↦ Real.exp (M₁ ‖u‖)) μ₀) :
    ∃ z > 0, ∀ y, ‖y‖ ≤ r → z ≤ normalizer μ₀ fun u ↦ Φ u y := by
  obtain ⟨R, hR, hKpos⟩ := exists_closedBall_pos μ₀
  set K := Metric.closedBall (0 : E) R
  obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : E) R).bddAbove_image (hcont 0).continuousOn
  refine ⟨Real.exp (-(S + |M₂ R| * r)) * μ₀.real K, mul_pos (Real.exp_pos _) hKpos,
    fun y hy ↦ ?_⟩
  refine le_normalizer_of_le_on Metric.isClosed_closedBall.measurableSet (measure_ne_top _ _)
    (integrable_exp_neg (hcont y).measurable (fun u ↦ hlow u y hy) hint) fun u hu ↦ ?_
  have hu' : ‖u‖ ≤ R := by simpa [K] using hu
  have h1 : Φ u 0 ≤ S := hS ⟨u, hu, rfl⟩
  have h2 := hlip u y 0 hy (by simpa using hr)
  rw [sub_zero] at h2
  have h3 : M₂ ‖u‖ * ‖y‖ ≤ |M₂ R| * r :=
    calc M₂ ‖u‖ * ‖y‖ ≤ M₂ R * ‖y‖ := mul_le_mul_of_nonneg_right (hM₂ hu') (norm_nonneg _)
      _ ≤ |M₂ R| * ‖y‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |M₂ R| * r := mul_le_mul_of_nonneg_left hy (abs_nonneg _)
  linarith [le_abs_self (Φ u y - Φ u 0)]

/-- **Well-posedness: the posterior is locally Lipschitz in the data in Hellinger distance.**
For a finite-dimensional unknown with prior probability measure `μ₀`, let the potential
`Φ(u; y)` be continuous in `u` and satisfy, for `‖y‖, ‖y'‖ ≤ r`,
`Φ(u; y) ≥ -M₁(‖u‖)` and `|Φ(u; y) - Φ(u; y')| ≤ M₂(‖u‖) ‖y - y'‖`, with `M₁`, `M₂`
nondecreasing and `exp(M₁(‖u‖))(1 + M₂(‖u‖)²)` integrable. Then there is `C` with
`d_Hell(μ^y, μ^{y'}) ≤ C ‖y - y'‖` for all `‖y‖, ‖y'‖ ≤ r`. This is Theorem 4.5 of Dashti and
Stuart (arXiv:1302.6989v4) for `X = X'` finite-dimensional (Assumptions 4.2 at the fixed
radius `r`). -/
theorem hellingerDist_posterior_le_mul_dist {Y : Type*} [SeminormedAddCommGroup Y]
    (μ₀ : Measure E) [IsProbabilityMeasure μ₀] (Φ : E → Y → ℝ) (M₁ M₂ : ℝ → ℝ) (r : ℝ)
    (hcont : ∀ y, Continuous fun u ↦ Φ u y) (hM₁ : Monotone M₁) (hM₂ : Monotone M₂)
    (hlow : ∀ u y, ‖y‖ ≤ r → -M₁ ‖u‖ ≤ Φ u y)
    (hlip : ∀ u y y', ‖y‖ ≤ r → ‖y'‖ ≤ r → |Φ u y - Φ u y'| ≤ M₂ ‖u‖ * ‖y - y'‖)
    (hint : Integrable (fun u ↦ Real.exp (M₁ ‖u‖) * (1 + M₂ ‖u‖ ^ 2)) μ₀) :
    ∃ C, ∀ y y', ‖y‖ ≤ r → ‖y'‖ ≤ r →
      hellingerDist (posterior μ₀ fun u ↦ Φ u y) (posterior μ₀ fun u ↦ Φ u y') ≤
        C * ‖y - y'‖ := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, fun y _ hy _ ↦ absurd (hy.trans_lt hr) (not_lt.2 (norm_nonneg y))⟩
  obtain ⟨z, hz, hZ⟩ := exists_pos_le_normalizer μ₀ Φ M₁ M₂ hr hcont hM₂ hlip hlow
    (integrable_exp_of_integrable_mul hM₁.measurable hint)
  set W := ∫ u, Real.exp (M₁ ‖u‖) * (1 + M₂ ‖u‖ ^ 2) ∂μ₀
  refine ⟨√(W / (4 * z) + W ^ 2 / (2 * z ^ 2)), fun y y' hy hy' ↦ ?_⟩
  have h := hellingerDist_posterior_le μ₀ (Φ₁ := fun u ↦ Φ u y) (Φ₂ := fun u ↦ Φ u y')
    (M₁ := fun u ↦ M₁ ‖u‖) (M₂ := fun u ↦ M₂ ‖u‖) (δ := ‖y - y'‖) (W := W)
    (hcont y).measurable (hcont y').measurable (hM₁.measurable.comp measurable_norm)
    (hM₂.measurable.comp measurable_norm) (fun u ↦ hlow u y hy) (fun u ↦ hlow u y' hy')
    (fun u ↦ hlip u y y' hy hy') hint le_rfl hz (hZ y hy) (hZ y' hy')
  rwa [abs_of_nonneg (norm_nonneg _), mul_comm] at h

/-- **Approximation: forward-model error controls posterior error in Hellinger distance.**
For a finite-dimensional unknown with prior probability measure `μ₀`, let `Φ` be continuous and
`Φₙ` measurable potentials with `Φ, Φₙ ≥ -M₁(‖u‖)` and
`|Φ(u) - Φₙ(u)| ≤ M₂(‖u‖) ψ(N)` with `ψ(N) → 0`, where `M₁`, `M₂` are nondecreasing and
independent of `N`, and `exp(M₁(‖u‖))(1 + M₂(‖u‖)²)` is integrable. Then there is `C` with
`d_Hell(μ, μᴺ) ≤ C |ψ(N)|` for all sufficiently large `N`. This is Theorem 4.9 of Dashti and
Stuart (arXiv:1302.6989v4) for `X = X'` finite-dimensional (Assumptions 4.7). -/
theorem hellingerDist_posterior_approx_le (μ₀ : Measure E) [IsProbabilityMeasure μ₀]
    (Φ : E → ℝ) (Φₙ : ℕ → E → ℝ) (ψ : ℕ → ℝ) (M₁ M₂ : ℝ → ℝ)
    (hcont : Continuous Φ) (hmeas : ∀ N, Measurable (Φₙ N)) (hM₁ : Monotone M₁)
    (hM₂ : Monotone M₂) (hlow : ∀ u, -M₁ ‖u‖ ≤ Φ u) (hlowN : ∀ N u, -M₁ ‖u‖ ≤ Φₙ N u)
    (hdiff : ∀ N u, |Φ u - Φₙ N u| ≤ M₂ ‖u‖ * ψ N) (hψ : Tendsto ψ atTop (𝓝 0))
    (hint : Integrable (fun u ↦ Real.exp (M₁ ‖u‖) * (1 + M₂ ‖u‖ ^ 2)) μ₀) :
    ∃ C, ∀ᶠ N in atTop, hellingerDist (posterior μ₀ Φ) (posterior μ₀ (Φₙ N)) ≤ C * |ψ N| := by
  obtain ⟨R, hR, hKpos⟩ := exists_closedBall_pos μ₀
  set K := Metric.closedBall (0 : E) R
  obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : E) R).bddAbove_image hcont.continuousOn
  set B := |M₂ 0| + |M₂ R|
  have hB : ∀ u ∈ K, |M₂ ‖u‖| ≤ B := fun u hu ↦ by
    have hu' : ‖u‖ ≤ R := by simpa [K] using hu
    have h0 := hM₂ (norm_nonneg u)
    have h1 := hM₂ hu'
    rw [abs_le]; constructor <;>
      linarith [neg_abs_le (M₂ 0), le_abs_self (M₂ R), abs_nonneg (M₂ 0), abs_nonneg (M₂ R)]
  set z := Real.exp (-(S + 1)) * μ₀.real K
  have hz : 0 < z := mul_pos (Real.exp_pos _) hKpos
  set W := ∫ u, Real.exp (M₁ ‖u‖) * (1 + M₂ ‖u‖ ^ 2) ∂μ₀
  refine ⟨√(W / (4 * z) + W ^ 2 / (2 * z ^ 2)), ?_⟩
  have hsmall : ∀ᶠ N in atTop, |ψ N| < 1 / (B + 1) := by
    have hB0 : 0 < B + 1 := by positivity
    filter_upwards [Metric.tendsto_nhds.1 hψ _ (one_div_pos.2 hB0)] with N hN
    simpa [Real.dist_eq] using hN
  filter_upwards [hsmall] with N hN
  have hB0 : 0 ≤ B := by positivity
  have hZ₁ : z ≤ normalizer μ₀ Φ := by
    refine le_trans ?_ (le_normalizer_of_le_on (T := S) Metric.isClosed_closedBall.measurableSet
      (measure_ne_top _ _) (integrable_exp_neg hcont.measurable hlow
        (integrable_exp_of_integrable_mul hM₁.measurable hint))
      fun u hu ↦ hS ⟨u, hu, rfl⟩)
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) measureReal_nonneg
  have hZ₂ : z ≤ normalizer μ₀ (Φₙ N) := by
    refine le_normalizer_of_le_on Metric.isClosed_closedBall.measurableSet (measure_ne_top _ _)
      (integrable_exp_neg (hmeas N) (hlowN N)
        (integrable_exp_of_integrable_mul hM₁.measurable hint)) fun u hu ↦ ?_
    have h1 : Φ u ≤ S := hS ⟨u, hu, rfl⟩
    have h2 : M₂ ‖u‖ * ψ N ≤ 1 := by
      calc M₂ ‖u‖ * ψ N ≤ |M₂ ‖u‖ * ψ N| := le_abs_self _
        _ = |M₂ ‖u‖| * |ψ N| := abs_mul _ _
        _ ≤ B * (1 / (B + 1)) := mul_le_mul (hB u hu) hN.le (abs_nonneg _) hB0
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith [hdiff N u, neg_abs_le (Φ u - Φₙ N u)]
  have h := hellingerDist_posterior_le μ₀ (Φ₁ := Φ) (Φ₂ := Φₙ N)
    (M₁ := fun u ↦ M₁ ‖u‖) (M₂ := fun u ↦ M₂ ‖u‖) (δ := ψ N) (W := W)
    hcont.measurable (hmeas N) (hM₁.measurable.comp measurable_norm)
    (hM₂.measurable.comp measurable_norm) hlow (hlowN N) (hdiff N) hint le_rfl hz hZ₁ hZ₂
  rwa [mul_comm] at h

end FiniteDimensional

end MathlibExt.Probability.BayesianInverse
