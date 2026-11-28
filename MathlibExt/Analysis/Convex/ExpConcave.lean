/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Quadratic lower bound for exp-concave functions

A function `f` is `α`-exp-concave on a convex set `K` when `z ↦ exp (-(α * f z))` is concave on
`K`. Such a function is strongly convex in the direction of its subgradients: if `K` is bounded
with diameter at most `D`, `g` is a subgradient of `f` at `y ∈ K` relative to `K`
(`f y + ⟪g, z - y⟫ ≤ f z` for every `z ∈ K`) with `‖g‖ ≤ G`, and `2 * γ ≤ α` and
`2 * γ * (G * D) ≤ 1`, then for every `x ∈ K`

`f y + ⟪g, x - y⟫ + γ / 2 * ⟪g, x - y⟫ ^ 2 ≤ f x`.

This is Lemma 4.3 (Section 4.2) of E. Hazan, *Introduction to Online Convex Optimization*, 2nd
ed. (arXiv:1909.05207), the step behind the logarithmic regret of the Online Newton Step.

## Main results

* `quadratic_lower_bound`: the bound above, in a real inner product space.
* `quadratic_lower_bound_of_hasGradientWithinAt`: the same bound for a gradient of `f` at `y`
  within `K`, which is a subgradient there, in a real Hilbert space.

## Implementation notes

Hazan's condition `γ ≤ ½ min {1 / (G D), α}` is stated as the two hypotheses `2 * γ ≤ α` and
`2 * γ * (G * D) ≤ 1`, which read `1 / (G D)` as `+∞` when `G D = 0`. As in Hazan (Section 2.1),
`g` is any subgradient, such as the gradient `∇f(y)` when `f` is differentiable at `y`; the
bound `G` is needed only at `y`. Convexity of `f`, part of Hazan's definition of exp-concavity,
is not assumed: it follows from exp-concavity. `γ` may be zero or negative.

The proof follows Hazan: `h = exp (-(2 * γ * f))` is the power `2 * γ / α` of
`exp (-(α * f))`, hence concave. Along the segment from `y` to `x`, concavity of `h` and the
subgradient inequality bound `h x - h y` by the difference quotients of
`t ↦ h y * exp (-(2 * γ * t * ⟪g, x - y⟫))` at `0⁺`, whose limit gives
`exp (-(2 * γ * (f x - f y))) ≤ 1 - u` with `u = 2 * γ * ⟪g, x - y⟫ ≥ -1`; and
`1 - u ≤ exp (-(u + u ^ 2 / 4))` for `u ≥ -1`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.ExpConcave

open Real Set Filter Topology
open scoped InnerProductSpace

/-- `(1 - u) * exp (u + u ^ 2 / 4)` increases on `[-1, 0]` and decreases on `[0, ∞)`, so it is at
most its value `1` at `0`. -/
private theorem one_sub_le_exp_neg {u : ℝ} (hu : -1 ≤ u) :
    1 - u ≤ exp (-(u + u ^ 2 / 4)) := by
  set φ : ℝ → ℝ := fun v ↦ (1 - v) * exp (v + v ^ 2 / 4) with hφ
  have hd : ∀ v, HasDerivAt φ (-(v * (1 + v) / 2) * exp (v + v ^ 2 / 4)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ ↦ 1 - v) (-1) v := by
      simpa using (hasDerivAt_id' v).const_sub (1 : ℝ)
    have h2 : HasDerivAt (fun v : ℝ ↦ v + v ^ 2 / 4) (1 + v / 2) v := by
      have := (hasDerivAt_id' v).add ((hasDerivAt_pow 2 v).div_const 4)
      convert this using 1
      push_cast
      ring
    convert h1.mul h2.exp using 1
    ring
  have hcont : Continuous φ := continuous_iff_continuousAt.2 fun v ↦ (hd v).continuousAt
  have hdiff : Differentiable ℝ φ := fun v ↦ (hd v).differentiableAt
  have hφ0 : φ 0 = 1 := by simp [hφ]
  have hle : φ u ≤ 1 := by
    rcases le_total u 0 with h | h
    · have hmono : MonotoneOn φ (Icc (-1) 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont.continuousOn
          hdiff.differentiableOn fun v hv ↦ ?_
        rw [interior_Icc] at hv
        rw [(hd v).deriv]
        have : v * (1 + v) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv.2.le (by linarith [hv.1])
        have := exp_pos (v + v ^ 2 / 4)
        nlinarith
      rw [← hφ0]
      exact hmono ⟨hu, h⟩ ⟨by norm_num, le_rfl⟩ h
    · have hanti : AntitoneOn φ (Ici 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
          hdiff.differentiableOn fun v hv ↦ ?_
        rw [interior_Ici] at hv
        rw [(hd v).deriv]
        have : 0 ≤ v * (1 + v) := mul_nonneg (le_of_lt hv) (by linarith [mem_Ioi.1 hv])
        have := exp_pos (v + v ^ 2 / 4)
        nlinarith
      rw [← hφ0]
      exact hanti (mem_Ici.2 le_rfl) (mem_Ici.2 h) h
  have hexp : exp (-(u + u ^ 2 / 4)) * exp (u + u ^ 2 / 4) = 1 := by
    rw [← exp_add]; simp
  have hpos := exp_pos (u + u ^ 2 / 4)
  nlinarith [hle, hexp]

/-- Lowering the exponent keeps exp-concavity: if `exp (-(α * f))` is concave and `0 ≤ β ≤ α`,
then `exp (-(β * f))`, its power `β / α`, is concave. -/
private theorem concaveOn_exp_neg_mul_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} {f : E → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hβα : β ≤ α)
    (h : ConcaveOn ℝ K fun z ↦ exp (-(α * f z))) :
    ConcaveOn ℝ K fun z ↦ exp (-(β * f z)) := by
  have hp0 : 0 ≤ β / α := div_nonneg hβ hα.le
  have hp1 : β / α ≤ 1 := (div_le_one hα).2 hβα
  have key : ∀ z, exp (-(β * f z)) = exp (-(α * f z)) ^ (β / α) := by
    intro z
    rw [← exp_mul]
    congr 1
    field_simp
  refine ⟨h.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simp only [key, smul_eq_mul]
  have h1 := (concaveOn_rpow hp0 hp1).2 (mem_Ici.2 (exp_pos (-(α * f x))).le)
    (mem_Ici.2 (exp_pos (-(α * f y))).le) ha hb hab
  have h2 := h.2 hx hy ha hb hab
  simp only [smul_eq_mul] at h1 h2
  exact h1.trans (rpow_le_rpow (by positivity) h2 hp0)

/-- Exp-concavity implies convexity: `f = -log (exp (-(α * f))) / α` with `exp (-(α * f))`
positive and concave. -/
private theorem convexOn_of_concaveOn_exp_neg_mul {E : Type*} [AddCommGroup E] [Module ℝ E]
    {K : Set E} {f : E → ℝ} {α : ℝ} (hα : 0 < α)
    (h : ConcaveOn ℝ K fun z ↦ exp (-(α * f z))) : ConvexOn ℝ K f := by
  refine ⟨h.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have h2 := h.2 hx hy ha hb hab
  have hgm := geom_mean_le_arith_mean2_weighted ha hb (exp_pos (-(α * f x))).le
    (exp_pos (-(α * f y))).le hab
  simp only [smul_eq_mul] at h2 ⊢
  rw [← exp_mul, ← exp_mul, ← exp_add] at hgm
  have := exp_le_exp.1 (hgm.trans h2)
  nlinarith

/-- First-order condition for a concave function with a derivative within its domain. -/
private theorem le_add_of_concaveOn_of_hasFDerivWithinAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} {h : E → ℝ} {h' : E →L[ℝ] ℝ} {x y : E}
    (hh : ConcaveOn ℝ K h) (hx : x ∈ K) (hy : y ∈ K) (hd : HasFDerivWithinAt h h' K y) :
    h x ≤ h y + h' (x - y) := by
  let ℓ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap y x
  have hℓ0 : ℓ 0 = y := AffineMap.lineMap_apply_zero y x
  have hℓ1 : ℓ 1 = x := AffineMap.lineMap_apply_one y x
  have h0 : (0 : ℝ) ∈ ℓ ⁻¹' K := by rw [mem_preimage, hℓ0]; exact hy
  have h1 : (1 : ℝ) ∈ ℓ ⁻¹' K := by rw [mem_preimage, hℓ1]; exact hx
  have hℓd : HasDerivWithinAt ℓ (x - y) (ℓ ⁻¹' K) 0 :=
    AffineMap.hasDerivAt_lineMap.hasDerivWithinAt
  have hd' : HasFDerivWithinAt h h' K (ℓ 0) := by rw [hℓ0]; exact hd
  have hcomp : HasDerivWithinAt (h ∘ ℓ) (h' (x - y)) (ℓ ⁻¹' K) 0 :=
    hd'.comp_hasDerivWithinAt 0 hℓd (mapsTo_preimage ℓ K)
  have hslope := (hh.comp_affineMap ℓ).slope_le_of_hasDerivWithinAt h0 h1 zero_lt_one hcomp
  rw [slope_def_field] at hslope
  simp only [Function.comp_apply, hℓ0, hℓ1, sub_zero, div_one] at hslope
  linarith

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- First-order condition for `exp (-(β * f))` from a subgradient `g` of `f` at `y`: the
difference quotients of `t ↦ exp (-(β * f y)) * exp (-(β * ⟪g, x - y⟫) * t)` at `0⁺` bound
`exp (-(β * f x)) - exp (-(β * f y))`. -/
private theorem exp_neg_le_of_subgradient {K : Set F} {f : F → ℝ} {β : ℝ} {x y g : F}
    (hconc : ConcaveOn ℝ K fun z ↦ exp (-(β * f z))) (hβ : 0 < β) (hx : x ∈ K) (hy : y ∈ K)
    (hg : ∀ z ∈ K, f y + ⟪g, z - y⟫_ℝ ≤ f z) :
    exp (-(β * f x)) ≤ exp (-(β * f y)) * (1 - β * ⟪g, x - y⟫_ℝ) := by
  set c := ⟪g, x - y⟫_ℝ with hc
  set A := exp (-(β * f y)) with hA
  set ψ : ℝ → ℝ := fun t ↦ A * exp (-(β * c) * t) with hψdef
  have hψ : HasDerivAt ψ (A * (exp (-(β * c) * 0) * (-(β * c) * 1))) 0 :=
    (((hasDerivAt_id (0 : ℝ)).const_mul (-(β * c))).exp).const_mul A
  have key : ∀ t ∈ Ioc (0 : ℝ) 1, exp (-(β * f x)) - A ≤ t⁻¹ • (ψ (0 + t) - ψ 0) := by
    intro t ht
    have ht0 := ht.1
    have hmem := hconc.2 hy hx (sub_nonneg.2 ht.2) ht0.le (by ring)
    have hsub := hg _ (hconc.1 hy hx (sub_nonneg.2 ht.2) ht0.le (by ring))
    have hin : ⟪g, (1 - t) • y + t • x - y⟫_ℝ = t * c := by
      have : (1 - t) • y + t • x - y = t • (x - y) := by module
      rw [this, inner_smul_right]
    rw [hin] at hsub
    have hup : exp (-(β * f ((1 - t) • y + t • x))) ≤ A * exp (-(β * c) * t) := by
      rw [hA, ← exp_add]
      exact exp_le_exp.2 (by nlinarith)
    simp only [smul_eq_mul] at hmem
    simp only [hψdef, zero_add, mul_zero, exp_zero, mul_one, smul_eq_mul]
    rw [le_inv_mul_iff₀ ht0]
    nlinarith
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), exp (-(β * f x)) - A ≤ t⁻¹ • (ψ (0 + t) - ψ 0) := by
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using key t ht
  have hlim := ge_of_tendsto hψ.tendsto_slope_zero_right hev
  simp only [mul_zero, exp_zero, one_mul, mul_one] at hlim
  linarith

/-- **Quadratic lower bound for exp-concave functions.** Let `K` be a bounded set in a real inner
product space with `Metric.diam K ≤ D`, let `α > 0`, and let `f` be `α`-exp-concave on `K`:
`z ↦ exp (-(α * f z))` is concave on `K` (Mathlib's `ConcaveOn` includes convexity of `K`). Let
`x, y ∈ K` and let `g` be a subgradient of `f` at `y` relative to `K` (for instance `∇f(y)` when
`f` is differentiable at `y`): `f y + ⟪g, z - y⟫ ≤ f z` for every `z ∈ K`, with `‖g‖ ≤ G`. If
`2 * γ ≤ α` and `2 * γ * (G * D) ≤ 1`, that is `γ ≤ ½ min {1 / (G D), α}` with `1 / (G D) = +∞`
when `G D = 0`, then `f y + ⟪g, x - y⟫ + γ / 2 * ⟪g, x - y⟫ ^ 2 ≤ f x`. Convexity of `f`, part of
Hazan's definition of exp-concavity, is not assumed: it follows from exp-concavity. `γ` may be
zero or negative.

Source: E. Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207,
Section 4.2, Lemma 4.3. -/
theorem quadratic_lower_bound {K : Set F} {f : F → ℝ} {α γ G D : ℝ} {x y g : F}
    (hα : 0 < α) (hexp : ConcaveOn ℝ K fun z ↦ exp (-(α * f z)))
    (hK : Bornology.IsBounded K) (hD : Metric.diam K ≤ D) (hx : x ∈ K) (hy : y ∈ K)
    (hg : ∀ z ∈ K, f y + ⟪g, z - y⟫_ℝ ≤ f z) (hgG : ‖g‖ ≤ G) (hγα : 2 * γ ≤ α)
    (hγGD : 2 * γ * (G * D) ≤ 1) :
    f y + ⟪g, x - y⟫_ℝ + γ / 2 * ⟪g, x - y⟫_ℝ ^ 2 ≤ f x := by
  rcases le_or_gt γ 0 with hγ | hγ
  · -- The quadratic term is nonpositive, and the rest is the subgradient inequality.
    have := hg x hx
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hγ (sq_nonneg ⟪g, x - y⟫_ℝ)]
  set z := ⟪g, x - y⟫_ℝ with hz
  have hconc := concaveOn_exp_neg_mul_of_le hα (by linarith) hγα hexp
  have hfirst := exp_neg_le_of_subgradient hconc (by linarith) hx hy hg
  rw [← hz] at hfirst
  -- `u = 2 * γ * z` is at least `-1`.
  have hzabs : |z| ≤ G * D := by
    have hxy : ‖x - y‖ ≤ D := by
      rw [← dist_eq_norm]; exact (Metric.dist_le_diam_of_mem hK hx hy).trans hD
    calc |z| ≤ ‖g‖ * ‖x - y‖ := abs_real_inner_le_norm g (x - y)
      _ ≤ G * D := mul_le_mul hgG hxy (norm_nonneg _) ((norm_nonneg g).trans hgG)
  have hu : -1 ≤ 2 * γ * z := by
    have := neg_abs_le z
    nlinarith
  have htaylor := one_sub_le_exp_neg hu
  have hmain :
      exp (-(2 * γ * f x)) ≤ exp (-(2 * γ * f y) - (2 * γ * z + (2 * γ * z) ^ 2 / 4)) := by
    rw [sub_eq_add_neg, exp_add]
    calc exp (-(2 * γ * f x)) ≤ exp (-(2 * γ * f y)) * (1 - 2 * γ * z) := hfirst
      _ ≤ exp (-(2 * γ * f y)) * exp (-(2 * γ * z + (2 * γ * z) ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left htaylor (exp_pos _).le
  rw [exp_le_exp] at hmain
  nlinarith

-- The gradient case: `f` is convex on `K` by exp-concavity, so a gradient of `f` at `y` within
-- `K` is a subgradient there.
theorem quadratic_lower_bound_of_hasGradientWithinAt [CompleteSpace F] {K : Set F} {f : F → ℝ}
    {α γ G D : ℝ} {x y g : F} (hα : 0 < α) (hexp : ConcaveOn ℝ K fun z ↦ exp (-(α * f z)))
    (hK : Bornology.IsBounded K) (hD : Metric.diam K ≤ D) (hx : x ∈ K) (hy : y ∈ K)
    (hg : HasGradientWithinAt f g K y) (hgG : ‖g‖ ≤ G) (hγα : 2 * γ ≤ α)
    (hγGD : 2 * γ * (G * D) ≤ 1) :
    f y + ⟪g, x - y⟫_ℝ + γ / 2 * ⟪g, x - y⟫_ℝ ^ 2 ≤ f x := by
  refine quadratic_lower_bound hα hexp hK hD hx hy (fun z hz ↦ ?_) hgG hγα hγGD
  have h := le_add_of_concaveOn_of_hasFDerivWithinAt
    (convexOn_of_concaveOn_exp_neg_mul hα hexp).neg hz hy hg.hasFDerivWithinAt.neg
  simp only [Pi.neg_apply, neg_apply, InnerProductSpace.toDual_apply_apply] at h
  linarith

end MathlibExt.Analysis.Convex.ExpConcave
