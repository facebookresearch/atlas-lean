/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Lyapunov's direct method: exponential stability on a set

Let `γ` be a forward solution of `x' = f(t, x)`, i.e. `IsIntegralCurveOn γ f (Set.Ici 0)`, that
stays in a set `s` of a real normed space `E`. Let `V : E → ℝ` have Fréchet derivative `V' x` at
every `x ∈ s` (no continuity of `V'` is needed), and suppose the orbital derivative satisfies
`V' x (f t x) ≤ -a * V x` on `s`. Then `V (γ t) ≤ exp (-a t) * V (γ 0)` for `t ≥ 0`. If moreover
`c₁ ‖x - x₀‖² ≤ V x ≤ c₂ ‖x - x₀‖²` on `s` with `c₁ > 0`, then

  `‖γ t - x₀‖ ≤ √(c₂ / c₁) * exp (-(a / 2) * t) * ‖γ 0 - x₀‖`,

so for `a > 0` the point `x₀` is exponentially stable and attracting for every initial value
whose forward solution remains in `s`. With `a = 0` (orbital derivative `≤ 0`) the same argument
gives sublevel invariance and Lyapunov stability.

## Scope

The theorems take a given forward solution and the hypothesis that it stays in `s`; they do not
construct solutions, and they do not show that solutions starting near `x₀` remain in `s`.
A merely negative *semi*definite orbital derivative (`V' x (f t x) ≤ 0`) gives only stability,
not attraction: asymptotic statements in that case need LaSalle's invariance principle
(`Flow.lasalle` in `MathlibExt.Dynamics.LaSalle`) and are not covered here. Equilibria without the
two-sided quadratic comparison bounds and global convergence on noncompact sets are also out of
scope.

## Main results

* `le_exp_mul_of_hasDerivWithinAt_Ici`: a differential inequality `u' ≤ -a u` on `[0, ∞)` gives
  `u t ≤ exp (-a t) u 0` (Grönwall).
* `IsIntegralCurveOn.lyapunov_le_exp`: exponential decay of `V` along the solution.
* `IsIntegralCurveOn.norm_sub_le_of_lyapunov`: exponential decay of `‖γ t - x₀‖`.
* `IsIntegralCurveOn.tendsto_of_lyapunov`: convergence to `x₀` when `a > 0`.
* `IsIntegralCurveOn.lyapunov_le_of_nonpos`, `IsIntegralCurveOn.mapsTo_sublevel_of_lyapunov`,
  `IsIntegralCurveOn.norm_sub_le_of_lyapunov_nonpos`, `lyapunov_stable`: the non-asymptotic
  version (orbital derivative `≤ 0`).
* `lyapunov_asymptotically_stable`: stability and attraction when `a > 0`.
* `IsIntegralCurveOn.abs_le_exp_neg_mul`: the scalar linear equation `x' = -k x`, by the
  criterion with `V x = x²`.

## References

* A. M. Lyapunov, *The general problem of the stability of motion* (1892); English
  translation, Internat. J. Control 55 (1992) 531–773.
* H. K. Khalil, *Nonlinear Systems*, 3rd ed., Prentice Hall (2002), §4.1, Theorem 4.1, and §4.5,
  Theorem 4.10.
-/

@[expose] public section

open Set Filter Real
open scoped Topology

/-- **Exponential decay from a linear differential inequality.** If `u` has right derivative
`u' t` within `[0, ∞)` at every `t ≥ 0` and `u' t ≤ -a * u t` there, then
`u t ≤ exp (-a * t) * u 0` for `t ≥ 0`. No sign condition on `a` or `u` is needed. -/
theorem le_exp_mul_of_hasDerivWithinAt_Ici {u u' : ℝ → ℝ} {a : ℝ}
    (hu : ∀ t, 0 ≤ t → HasDerivWithinAt u (u' t) (Ici 0) t)
    (hbound : ∀ t, 0 ≤ t → u' t ≤ -a * u t) {t : ℝ} (ht : 0 ≤ t) :
    u t ≤ exp (-a * t) * u 0 := by
  have h := le_gronwallBound_of_liminf_deriv_right_le (f := u) (f' := u') (δ := u 0) (K := -a)
    (ε := 0) (a := 0) (b := t)
    (fun x hx => (hu x hx.1).continuousWithinAt.mono Icc_subset_Ici_self)
    (fun x hx _r hr => ((hu x hx.1).mono (Ici_subset_Ici.2 hx.1)).liminf_right_slope_le hr)
    le_rfl (fun x hx => by simpa using hbound x hx.1) t ⟨ht, le_rfl⟩
  rwa [gronwallBound_ε0, sub_zero, mul_comm] at h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {γ : ℝ → E} {f : ℝ → E → E} {V : E → ℝ} {V' : E → E →L[ℝ] ℝ} {s : Set E} {a : ℝ}

namespace IsIntegralCurveOn

/-- **Orbital derivative.** Along an integral curve of `f` on a set of times `I`, the function
`V ∘ γ` has derivative `V' (γ t) (f t (γ t))` within `I` at every `t ∈ I` where `V` has Fréchet
derivative `V' (γ t)`. -/
theorem hasDerivWithinAt_comp {I : Set ℝ} (hγ : IsIntegralCurveOn γ f I) {t : ℝ} (ht : t ∈ I)
    (hV : HasFDerivAt V (V' (γ t)) (γ t)) :
    HasDerivWithinAt (V ∘ γ) (V' (γ t) (f t (γ t))) I t :=
  hV.comp_hasDerivWithinAt t (hγ t ht)

/-- **Lyapunov's direct method, decay of `V`.** Let `γ` be a forward solution of `x' = f(t, x)`
that stays in `s`. If `V` has derivative `V' x` at each `x ∈ s` and the orbital derivative
satisfies `V' x (f t x) ≤ -a * V x` on `s` for `t ≥ 0`, then `V (γ t) ≤ exp (-a * t) * V (γ 0)`
for every `t ≥ 0`. -/
theorem lyapunov_le_exp (hγ : IsIntegralCurveOn γ f (Ici 0)) (hγs : ∀ t, 0 ≤ t → γ t ∈ s)
    (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ -a * V x) {t : ℝ} (ht : 0 ≤ t) :
    V (γ t) ≤ exp (-a * t) * V (γ 0) :=
  le_exp_mul_of_hasDerivWithinAt_Ici (u := V ∘ γ)
    (fun τ hτ => hγ.hasDerivWithinAt_comp (mem_Ici.2 hτ) (hV _ (hγs τ hτ)))
    (fun τ hτ => hdV τ hτ _ (hγs τ hτ)) ht

/-- **Lyapunov's direct method, exponential decay of the state.** In addition to the hypotheses
of `lyapunov_le_exp`, assume the quadratic comparison bounds
`c₁ ‖x - x₀‖² ≤ V x ≤ c₂ ‖x - x₀‖²` on `s` with `c₁ > 0`. Then for every `t ≥ 0`,
`‖γ t - x₀‖ ≤ √(c₂ / c₁) * exp (-(a / 2) * t) * ‖γ 0 - x₀‖`. -/
theorem norm_sub_le_of_lyapunov (hγ : IsIntegralCurveOn γ f (Ici 0))
    (hγs : ∀ t, 0 ≤ t → γ t ∈ s) (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ -a * V x) {x₀ : E} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ x ∈ s, c₁ * ‖x - x₀‖ ^ 2 ≤ V x) (hup : ∀ x ∈ s, V x ≤ c₂ * ‖x - x₀‖ ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖γ t - x₀‖ ≤ √(c₂ / c₁) * exp (-(a / 2) * t) * ‖γ 0 - x₀‖ := by
  set d := ‖γ t - x₀‖
  set d₀ := ‖γ 0 - x₀‖
  have hexp : exp (-a * t) = exp (-(a / 2) * t) ^ 2 := by
    rw [← exp_nat_mul]; congr 1; push_cast; ring
  have hsq : d ^ 2 ≤ c₂ / c₁ * (exp (-(a / 2) * t) * d₀) ^ 2 := by
    have h1 : c₁ * d ^ 2 ≤ exp (-a * t) * (c₂ * d₀ ^ 2) :=
      (hlow _ (hγs t ht)).trans <| (hγ.lyapunov_le_exp hγs hV hdV ht).trans <|
        mul_le_mul_of_nonneg_left (hup _ (hγs 0 le_rfl)) (exp_pos _).le
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁, mul_pow, ← hexp]
    linarith
  calc d = √(d ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(c₂ / c₁ * (exp (-(a / 2) * t) * d₀) ^ 2) := sqrt_le_sqrt hsq
    _ = √(c₂ / c₁) * (exp (-(a / 2) * t) * d₀) := by
      rw [sqrt_mul' _ (sq_nonneg _), sqrt_sq (by positivity)]
    _ = √(c₂ / c₁) * exp (-(a / 2) * t) * d₀ := by ring

/-- **Lyapunov's direct method, attraction.** Under the hypotheses of `norm_sub_le_of_lyapunov`
with decay rate `a > 0`, the solution converges to `x₀`. -/
theorem tendsto_of_lyapunov (hγ : IsIntegralCurveOn γ f (Ici 0))
    (hγs : ∀ t, 0 ≤ t → γ t ∈ s) (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ -a * V x) (ha : 0 < a) {x₀ : E} {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hlow : ∀ x ∈ s, c₁ * ‖x - x₀‖ ^ 2 ≤ V x)
    (hup : ∀ x ∈ s, V x ≤ c₂ * ‖x - x₀‖ ^ 2) :
    Tendsto γ atTop (𝓝 x₀) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun t => √(c₂ / c₁) * exp (-(a / 2) * t) * ‖γ 0 - x₀‖) atTop (𝓝 0) := by
    have he : Tendsto (fun t => exp (-(a / 2) * t)) atTop (𝓝 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop (half_pos ha))
      refine this.congr fun t => ?_
      simp [neg_mul]
    simpa using (he.const_mul (√(c₂ / c₁))).mul_const ‖γ 0 - x₀‖
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact hγ.norm_sub_le_of_lyapunov hγs hV hdV hc₁ hlow hup ht

/-- **Lyapunov's direct method, nonincreasing `V`.** If the orbital derivative is `≤ 0` on `s`,
then `V` does not increase along a forward solution that stays in `s`. -/
theorem lyapunov_le_of_nonpos (hγ : IsIntegralCurveOn γ f (Ici 0))
    (hγs : ∀ t, 0 ≤ t → γ t ∈ s) (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ 0) {t : ℝ} (ht : 0 ≤ t) :
    V (γ t) ≤ V (γ 0) := by
  simpa using hγ.lyapunov_le_exp (a := 0) hγs hV (by simpa using hdV) ht

/-- **Sublevel invariance.** If the orbital derivative is `≤ 0` on `s`, a forward solution that
stays in `s` and starts in the sublevel set `{x | V x ≤ c}` remains in it. -/
theorem mapsTo_sublevel_of_lyapunov (hγ : IsIntegralCurveOn γ f (Ici 0))
    (hγs : ∀ t, 0 ≤ t → γ t ∈ s) (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ 0) {c : ℝ} (h₀ : V (γ 0) ≤ c) :
    MapsTo γ (Ici 0) {x | V x ≤ c} :=
  fun _ ht => (hγ.lyapunov_le_of_nonpos hγs hV hdV ht).trans h₀

/-- **Lyapunov's direct method, stability bound.** If the orbital derivative is `≤ 0` on `s` and
`c₁ ‖x - x₀‖² ≤ V x ≤ c₂ ‖x - x₀‖²` on `s` with `c₁ > 0`, then a forward solution that stays in
`s` satisfies `‖γ t - x₀‖ ≤ √(c₂ / c₁) * ‖γ 0 - x₀‖` for `t ≥ 0`. -/
theorem norm_sub_le_of_lyapunov_nonpos (hγ : IsIntegralCurveOn γ f (Ici 0))
    (hγs : ∀ t, 0 ≤ t → γ t ∈ s) (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ 0) {x₀ : E} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ x ∈ s, c₁ * ‖x - x₀‖ ^ 2 ≤ V x) (hup : ∀ x ∈ s, V x ≤ c₂ * ‖x - x₀‖ ^ 2)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖γ t - x₀‖ ≤ √(c₂ / c₁) * ‖γ 0 - x₀‖ := by
  simpa using hγ.norm_sub_le_of_lyapunov (a := 0) hγs hV (by simpa using hdV) hc₁ hlow hup ht

end IsIntegralCurveOn

/-- **Lyapunov stability on a set.** If the orbital derivative of `V` is `≤ 0` on `s` and
`c₁ ‖x - x₀‖² ≤ V x ≤ c₂ ‖x - x₀‖²` on `s` with `c₁ > 0`, then for every `ε > 0` there is
`δ > 0` such that every forward solution that stays in `s` and starts within `δ` of `x₀` stays
within `ε` of `x₀`. -/
theorem lyapunov_stable (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ 0) {x₀ : E} {c₁ c₂ : ℝ} (hc₁ : 0 < c₁)
    (hlow : ∀ x ∈ s, c₁ * ‖x - x₀‖ ^ 2 ≤ V x) (hup : ∀ x ∈ s, V x ≤ c₂ * ‖x - x₀‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ γ : ℝ → E, IsIntegralCurveOn γ f (Ici 0) → (∀ t, 0 ≤ t → γ t ∈ s) →
      ‖γ 0 - x₀‖ < δ → ∀ t, 0 ≤ t → ‖γ t - x₀‖ < ε := by
  have hC : 0 < √(c₂ / c₁) + 1 := by positivity
  refine ⟨ε / (√(c₂ / c₁) + 1), div_pos hε hC, fun γ hγ hγs h₀ t ht => ?_⟩
  calc ‖γ t - x₀‖ ≤ √(c₂ / c₁) * ‖γ 0 - x₀‖ :=
        hγ.norm_sub_le_of_lyapunov_nonpos hγs hV hdV hc₁ hlow hup ht
    _ ≤ (√(c₂ / c₁) + 1) * ‖γ 0 - x₀‖ := by nlinarith [norm_nonneg (γ 0 - x₀)]
    _ < (√(c₂ / c₁) + 1) * (ε / (√(c₂ / c₁) + 1)) := mul_lt_mul_of_pos_left h₀ hC
    _ = ε := mul_div_cancel₀ _ hC.ne'

/-- **Exponential asymptotic stability on a set.** If `V' x (f t x) ≤ -a * V x` on `s` with
`a > 0` and `c₁ ‖x - x₀‖² ≤ V x ≤ c₂ ‖x - x₀‖²` on `s` with `c₁ > 0`, then `x₀` is stable (in
the `ε`-`δ` sense of `lyapunov_stable`) and attracting for forward solutions that stay in `s`.
The rate `‖γ t - x₀‖ ≤ √(c₂ / c₁) e^{-a t / 2} ‖γ 0 - x₀‖` is
`IsIntegralCurveOn.norm_sub_le_of_lyapunov`. -/
theorem lyapunov_asymptotically_stable (hV : ∀ x ∈ s, HasFDerivAt V (V' x) x)
    (hdV : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ -a * V x) (ha : 0 < a) {x₀ : E} {c₁ c₂ : ℝ}
    (hc₁ : 0 < c₁) (hlow : ∀ x ∈ s, c₁ * ‖x - x₀‖ ^ 2 ≤ V x)
    (hup : ∀ x ∈ s, V x ≤ c₂ * ‖x - x₀‖ ^ 2) :
    (∀ ε > 0, ∃ δ > 0, ∀ γ : ℝ → E, IsIntegralCurveOn γ f (Ici 0) → (∀ t, 0 ≤ t → γ t ∈ s) →
      ‖γ 0 - x₀‖ < δ → ∀ t, 0 ≤ t → ‖γ t - x₀‖ < ε) ∧
    ∀ γ : ℝ → E, IsIntegralCurveOn γ f (Ici 0) → (∀ t, 0 ≤ t → γ t ∈ s) →
      Tendsto γ atTop (𝓝 x₀) := by
  have hdV' : ∀ t, 0 ≤ t → ∀ x ∈ s, V' x (f t x) ≤ 0 := fun t ht x hx => by
    have hVx : 0 ≤ V x := (by positivity : 0 ≤ c₁ * ‖x - x₀‖ ^ 2).trans (hlow x hx)
    nlinarith [hdV t ht x hx]
  exact ⟨fun ε hε => lyapunov_stable hV hdV' hc₁ hlow hup hε,
    fun γ hγ hγs => hγ.tendsto_of_lyapunov hγs hV hdV ha hc₁ hlow hup⟩

/-- **Scalar linear decay via the Lyapunov criterion.** Every forward solution of `x' = -k x`
satisfies `|x t| ≤ exp (-k * t) * |x 0|` for `t ≥ 0`; this follows from
`IsIntegralCurveOn.norm_sub_le_of_lyapunov` with `V x = x²`, `s = univ`, `x₀ = 0`, `a = 2k`,
`c₁ = c₂ = 1`. No sign condition on `k` is needed. -/
theorem IsIntegralCurveOn.abs_le_exp_neg_mul {k : ℝ} {x : ℝ → ℝ}
    (hx : IsIntegralCurveOn x (fun _ y => -k * y) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    |x t| ≤ exp (-k * t) * |x 0| := by
  have hV : ∀ y ∈ (univ : Set ℝ), HasFDerivAt (fun z : ℝ => z ^ 2)
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * y)) y := fun y _ => by
    simpa using (hasDerivAt_pow 2 y).hasFDerivAt
  have h := hx.norm_sub_le_of_lyapunov (s := univ) (a := 2 * k) (x₀ := 0) (c₁ := 1) (c₂ := 1)
    (fun _ _ => mem_univ _) hV (fun _ _ y _ => by simp; ring_nf; rfl) one_pos
    (fun y _ => by simp) (fun y _ => by simp) ht
  simpa [Real.norm_eq_abs, mul_div_cancel_left₀ k (two_ne_zero' ℝ)] using h
