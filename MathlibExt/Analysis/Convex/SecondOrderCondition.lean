/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import MathlibExt.Analysis.Convex.FirstOrderCondition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Module

/-!
# The second-order condition for convexity

A twice differentiable function on an open convex set is convex if and only if its Hessian is
positive semidefinite at every point (Boyd–Vandenberghe §3.1.4). We pass the first and second
derivatives explicitly: `f' y : E →L[ℝ] ℝ` is the derivative of `f` at `y` and
`f'' y : E →L[ℝ] E →L[ℝ] ℝ` the derivative of `f'` at `y`, so `f'' y v v` is the Hessian quadratic
form `vᵀ ∇²f(y) v`.

The proof restricts `f` to lines: `g t = f (x + t d)` has `g' t = f' (x + t d) d` and
`g'' t = f'' (x + t d) d d`. Nonnegative `g''` makes `g'` monotone and `g` convex; conversely,
for convex `f` the first-order condition makes `t ↦ f' (y + t v) v` nondecreasing, so its
derivative `f'' y v v` at `0` is nonnegative.

## Main results

* `convexOn_of_hessian_nonneg`: PSD Hessian on an open convex set implies convexity.
* `hessian_nonneg_of_convexOn`: convexity on an open set implies a PSD Hessian.
* `convexOn_iff_hessian_nonneg`: the equivalence (Boyd–Vandenberghe §3.1.4, exercise 3.8).
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.SecondOrderCondition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem hasDerivAt_line_point (x d : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • d) d t := by
  simpa using ((hasDerivAt_id t).smul_const d).const_add x

/-- Along a line, the derivative of `t ↦ f' (x + t d) d` is `f'' (x + t d) d d`. -/
private theorem hasDerivAt_line_deriv {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    {x d : E} {t : ℝ} (h : HasFDerivAt f' (f'' (x + t • d)) (x + t • d)) :
    HasDerivAt (fun s : ℝ => f' (x + s • d) d) (f'' (x + t • d) d d) t := by
  have hc : HasDerivAt (fun s : ℝ => f' (x + s • d)) (f'' (x + t • d) d) t := by
    simpa [Function.comp_def] using (h.comp t (hasDerivAt_line_point x d t).hasFDerivAt).hasDerivAt
  simpa using hc.clm_apply (hasDerivAt_const t d)

/-- **Positive semidefinite Hessian implies convexity.** Let `s` be open and convex, and let `f`
have derivative `f' y` and second derivative `f'' y` at every `y ∈ s`. If
`0 ≤ f'' y v v` for all `y ∈ s` and all `v`, then `f` is convex on `s`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.4 (proof left as exercise 3.8). -/
theorem convexOn_of_hessian_nonneg {s : Set E} {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hso : IsOpen s) (hs : Convex ℝ s)
    (hf : ∀ y ∈ s, HasFDerivAt f (f' y) y) (hf' : ∀ y ∈ s, HasFDerivAt f' (f'' y) y)
    (hpsd : ∀ y ∈ s, ∀ v, 0 ≤ f'' y v v) : ConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  set d := y - x with hd
  set T : Set ℝ := {t | x + t • d ∈ s} with hT
  have hTo : IsOpen T := hso.preimage (by fun_prop)
  have hTc : Convex ℝ T := by
    intro t₁ ht₁ t₂ ht₂ p q hp hq hpq
    have h := hs ht₁ ht₂ hp hq hpq
    have : p • (x + t₁ • d) + q • (x + t₂ • d) = x + (p • t₁ + q • t₂) • d := by
      calc p • (x + t₁ • d) + q • (x + t₂ • d) = (p + q) • x + (p * t₁ + q * t₂) • d := by
            module
        _ = x + (p • t₁ + q • t₂) • d := by rw [hpq, one_smul, smul_eq_mul, smul_eq_mul]
    rw [this] at h
    exact h
  have h0 : (0 : ℝ) ∈ T := by simp [hT, hx]
  have h1 : (1 : ℝ) ∈ T := by simp [hT, hd, hy]
  set g : ℝ → ℝ := fun t => f (x + t • d) with hg
  have hgd : ∀ t ∈ T, HasDerivAt g (f' (x + t • d) d) t := by
    intro t ht
    simpa [hg, Function.comp_def] using
      ((hf _ ht).comp t (hasDerivAt_line_point x d t).hasFDerivAt).hasDerivAt
  have hφd : ∀ t ∈ T, HasDerivAt (fun s : ℝ => f' (x + s • d) d) (f'' (x + t • d) d d) t :=
    fun t ht => hasDerivAt_line_deriv (hf' _ ht)
  have hmono : MonotoneOn (fun s : ℝ => f' (x + s • d) d) T := by
    refine monotoneOn_of_deriv_nonneg hTc (fun t ht => (hφd t ht).continuousAt.continuousWithinAt)
      ?_ ?_
    · rw [hTo.interior_eq]
      exact fun t ht => (hφd t ht).differentiableAt.differentiableWithinAt
    · rw [hTo.interior_eq]
      intro t ht
      rw [(hφd t ht).deriv]
      exact hpsd _ ht d
  have hgconv : ConvexOn ℝ T g := by
    refine MonotoneOn.convexOn_of_deriv hTc
      (fun t ht => (hgd t ht).continuousAt.continuousWithinAt) ?_ ?_
    · rw [hTo.interior_eq]
      exact fun t ht => (hgd t ht).differentiableAt.differentiableWithinAt
    · rw [hTo.interior_eq]
      intro t₁ ht₁ t₂ ht₂ h12
      rw [(hgd t₁ ht₁).deriv, (hgd t₂ ht₂).deriv]
      exact hmono ht₁ ht₂ h12
  have key := hgconv.2 h0 h1 ha hb hab
  simp only [hg, smul_eq_mul, mul_zero, mul_one, zero_smul, add_zero, one_smul, zero_add] at key
  have hpt : x + b • d = a • x + b • y := by
    obtain rfl : a = 1 - b := by linarith
    rw [hd]
    module
  have hy' : x + d = y := by rw [hd]; abel
  rw [hpt, hy'] at key
  simpa [smul_eq_mul] using key

/-- **Convexity implies a positive semidefinite Hessian.** Let `s` be open, let `f` be convex on
`s`, with derivative `f' z` at every `z ∈ s` and second derivative `f'' y` at `y ∈ s`. Then
`0 ≤ f'' y v v` for every `v`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.4 (proof left as exercise 3.8). -/
theorem hessian_nonneg_of_convexOn {s : Set E} {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hso : IsOpen s) (hconv : ConvexOn ℝ s f)
    (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z) {y : E} (hy : y ∈ s)
    (hf'' : HasFDerivAt f' (f'' y) y) (v : E) : 0 ≤ f'' y v v := by
  have hφ : HasDerivAt (fun t : ℝ => f' (y + t • v) v) (f'' y v v) 0 := by
    have h : HasFDerivAt f' (f'' (y + (0 : ℝ) • v)) (y + (0 : ℝ) • v) := by simpa using hf''
    simpa using hasDerivAt_line_deriv (x := y) (d := v) (t := 0) h
  have hlim := hφ.tendsto_slope_zero_right
  have hnear : ∀ᶠ t in nhds (0 : ℝ), y + t • v ∈ s := by
    have hc : Continuous (fun t : ℝ => y + t • v) := by fun_prop
    exact hc.continuousAt (x := 0) (hso.mem_nhds (by simpa using hy))
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      0 ≤ t⁻¹ • (f' (y + (0 + t) • v) v - f' (y + (0 : ℝ) • v) v) := by
    filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    -- First-order condition at `y` and at `y + t v`.
    have h1 := FirstOrderCondition.add_fderiv_le_of_convexOn hconv hy ht (hf y hy)
    have h2 := FirstOrderCondition.add_fderiv_le_of_convexOn hconv ht hy (hf _ ht)
    simp only [add_sub_cancel_left, map_smul, smul_eq_mul] at h1
    have h2' : f' (y + t • v) (y - (y + t • v)) = -(t * f' (y + t • v) v) := by
      rw [show y - (y + t • v) = -(t • v) by abel, map_neg, map_smul, smul_eq_mul]
    rw [h2'] at h2
    have : t * f' y v ≤ t * f' (y + t • v) v := by linarith
    have := le_of_mul_le_mul_left this htpos'
    exact mul_nonneg (inv_nonneg.2 htpos'.le) (by linarith)
  exact ge_of_tendsto hlim hev

/-- **Second-order characterization of convexity.** On an open convex set `s` where `f` is twice
differentiable, `f` is convex if and only if its Hessian is positive semidefinite at every point:
`0 ≤ f'' y v v` for all `y ∈ s` and all `v`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§3.1.4 (proof left as exercise 3.8). -/
theorem convexOn_iff_hessian_nonneg {s : Set E} {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hso : IsOpen s) (hs : Convex ℝ s)
    (hf : ∀ y ∈ s, HasFDerivAt f (f' y) y) (hf' : ∀ y ∈ s, HasFDerivAt f' (f'' y) y) :
    ConvexOn ℝ s f ↔ ∀ y ∈ s, ∀ v, 0 ≤ f'' y v v :=
  ⟨fun h y hy v => hessian_nonneg_of_convexOn hso h hf hy (hf' y hy) v,
    convexOn_of_hessian_nonneg hso hs hf hf'⟩

end MathlibExt.Analysis.Convex.SecondOrderCondition
