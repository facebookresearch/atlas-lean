/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Ring
import MathlibExt.Analysis.Calculus.TangentSpaceLevelSet

/-!
# Amari's interface equation for neural-field bump widths

For a continuously differentiable solution of the one-dimensional Heaviside neural-field equation
with a continuous, even, integrable kernel and constant input, suppose the strict superlevel set
at the firing threshold is a nonempty interval with differentiable endpoints at all times. If the
spatial slope is positive at the left endpoint and negative at the right endpoint, the rate of
change of the interval's width is the common time derivative of the field at the two endpoints
multiplied by the sum of the reciprocals of the absolute spatial slopes.

Time is measured in units of the relaxation time in the source. Shifting the firing threshold to
zero turns the constant input and threshold into a single baseline `s - h`, the `h` of Eq. (10).
The identity does not require the additional kernel shape conditions used in the source to
classify equilibria.

## References

* Shun-ichi Amari, *Dynamics of Pattern Formation in Lateral-Inhibition Type Neural Fields*,
  Biological Cybernetics 27 (1977), 77–87, §3, Eq. (3), and §5, Eqs. (8)–(10).
* `MathlibExt.Analysis.Calculus.TangentSpaceLevelSet` supplies
  `MetaMathlibExt.levelSet_tangent_vel_of_curve` for the moving interfaces.
-/

namespace WantedExt.Biology.Neuroscience.AmariBumpWanted

open MeasureTheory Set

@[expose] public section

/-- `W(a) = ∫_0^a w(x) dx`. -/
noncomputable def kernelPrimitive (w : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a, w x

/-- The Heaviside firing function `H(z) = 1` for `z > 0` and `0` otherwise. -/
noncomputable def heaviside (z : ℝ) : ℝ :=
  if 0 < z then 1 else 0

/-- The field input `∫ w(x - y) H(u(y) - h) dy + s` at position `x` for the state `u`. -/
noncomputable def fieldInput (w : ℝ → ℝ) (h s : ℝ) (u : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ y, w (x - y) * heaviside (u y - h)) + s

/-- Standing hypotheses on the kernel: `w` is continuous, even and integrable. -/
structure IsKernel (w : ℝ → ℝ) : Prop where
  continuous : Continuous w
  even : ∀ x, w (-x) = w x
  integrable : Integrable w

end

/-- **Primitive of the zero kernel.** There is no integrated coupling at any width. -/
@[simp] public theorem kernelPrimitive_zero_kernel (a : ℝ) :
    kernelPrimitive (fun _ ↦ 0) a = 0 := by
  simp [kernelPrimitive]

/-- **Field input without coupling.** With zero kernel, only the external input remains. -/
@[simp] public theorem fieldInput_zero_kernel (h s : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    fieldInput (fun _ ↦ 0) h s u x = s := by
  simp [fieldInput]

private theorem level_at_endpoints {U : ℝ → ℝ} {h a b : ℝ} (hU : Continuous U) (hab : a < b)
    (hex : {x | h < U x} = Ioo a b) : U a = h ∧ U b = h := by
  have hboundary := frontier_lt_subset_eq (f := fun _ : ℝ ↦ h) continuous_const hU
  rw [hex, frontier_Ioo hab] at hboundary
  exact ⟨(hboundary (by simp : a ∈ ({a, b} : Set ℝ))).symm,
    (hboundary (by simp : b ∈ ({a, b} : Set ℝ))).symm⟩

private theorem fieldInput_eq_interval {w U : ℝ → ℝ} {h s a b : ℝ} (hab : a ≤ b)
    (hex : {y | h < U y} = Ioo a b) (x : ℝ) :
    fieldInput w h s U x = (∫ z in (x - b)..(x - a), w z) + s := by
  classical
  have hfun : (fun y ↦ w (x - y) * heaviside (U y - h)) =
      (Ioo a b).indicator (fun y ↦ w (x - y)) := by
    funext y
    have hy : 0 < U y - h ↔ y ∈ Ioo a b := by
      rw [← hex, mem_ofPred_eq, sub_pos]
    by_cases hm : y ∈ Ioo a b
    · simp [heaviside, hy.mpr hm, indicator_of_mem hm]
    · simp [heaviside, mt hy.mp hm, indicator_of_notMem hm]
  rw [fieldInput, hfun, integral_indicator measurableSet_Ioo, restrict_Ioo_eq_restrict_Ioc,
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_comp_sub_left]

private theorem interface_velocity {u : ℝ → ℝ → ℝ} {X : ℝ → ℝ} {h v t : ℝ}
    (hu : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ u p.1 p.2) (X t, t))
    (hX : DifferentiableAt ℝ X t) (hlevel : ∀ τ, u (X τ) τ = h)
    (htime : HasDerivAt (u (X t)) v t) (hslope : deriv (fun x ↦ u x t) (X t) ≠ 0) :
    HasDerivAt X (-v / deriv (fun x ↦ u x t) (X t)) t := by
  let D := fderiv ℝ (fun p : ℝ × ℝ ↦ u p.1 p.2) (X t, t)
  have hD : HasFDerivAt (fun p : ℝ × ℝ ↦ u p.1 p.2) D (X t, t) := hu.hasFDerivAt
  have hx : HasDerivAt (fun x ↦ (x, t)) (1, 0) (X t) :=
    (hasDerivAt_id (X t)).prodMk (hasDerivAt_const (X t) t)
  have ht : HasDerivAt (fun τ ↦ (X t, τ)) (0, 1) t :=
    (hasDerivAt_const t (X t)).prodMk (hasDerivAt_id t)
  have hDx : D (1, 0) = deriv (fun x ↦ u x t) (X t) :=
    (hD.comp_hasDerivAt (X t) hx).deriv.symm
  have hDt : D (0, 1) = v := (hD.comp_hasDerivAt t ht).unique htime
  have hcurve := hX.hasDerivAt.prodMk (hasDerivAt_id t)
  have htranslate : HasDerivAt (fun τ : ℝ ↦ τ + t) 1 0 := (hasDerivAt_id 0).add_const t
  have hshift : HasDerivAt (fun τ ↦ (X (τ + t), τ + t)) (deriv X t, 1) 0 := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      hcurve.scomp_of_eq 0 htranslate (zero_add t).symm
  have htangent : D (deriv X t, 1) = 0 :=
    MetaMathlibExt.levelSet_tangent_vel_of_curve hu (by rw [zero_add]) hshift
      (fun τ ↦ hlevel (τ + t))
  have hsplit : (deriv X t, (1 : ℝ)) = deriv X t • ((1 : ℝ), (0 : ℝ)) + (0, 1) := by
    simp
  have hzero : deriv X t * deriv (fun x ↦ u x t) (X t) + v = 0 := by
    simpa only [hsplit, map_add, map_smul, smul_eq_mul, hDx, hDt] using htangent
  have hvelocity : deriv X t = -v / deriv (fun x ↦ u x t) (X t) :=
    (eq_div_iff hslope).2 (eq_neg_of_add_eq_zero_left hzero)
  simpa only [← hvelocity] using hX.hasDerivAt

/-- **Amari's interface equation** (Amari 1977). Let `w` be continuous, even and integrable and
`h, s ∈ ℝ`. Let `u : ℝ → ℝ → ℝ` be `C¹` in `(x, t)` and solve
`∂_t u(x, t) = -u(x, t) + fieldInput w h s (u · t) x` for all `x, t`. Let `x₁, x₂ : ℝ → ℝ` be
differentiable with `x₁ t < x₂ t` and `{x | h < u x t} = (x₁ t, x₂ t)` for all `t`, and let the
slopes `c₁ t = ∂_x u(x₁ t, t)` and `c₂ t = -∂_x u(x₂ t, t)` be positive for all `t`. Then for every
`t` the width `a = x₂ - x₁` has derivative `(W(a(t)) + s - h) (1 / c₁ t + 1 / c₂ t)` at `t`.

Source: S. Amari, "Dynamics of pattern formation in lateral-inhibition type neural fields",
Biol. Cybern. 27 (1977) 77–87. -/
public theorem hasDerivAt_width {w : ℝ → ℝ} (hw : IsKernel w) (h s : ℝ)
    (u : ℝ → ℝ → ℝ) (hu : ContDiff ℝ 1 (fun p : ℝ × ℝ => u p.1 p.2))
    (heq : ∀ x t, HasDerivAt (fun t => u x t) (-u x t + fieldInput w h s (fun y => u y t) x) t)
    (x₁ x₂ : ℝ → ℝ) (hx₁ : Differentiable ℝ x₁) (hx₂ : Differentiable ℝ x₂)
    (hlt : ∀ t, x₁ t < x₂ t) (hex : ∀ t, {x | h < u x t} = Set.Ioo (x₁ t) (x₂ t))
    (hc₁ : ∀ t, 0 < deriv (fun x => u x t) (x₁ t)) (hc₂ : ∀ t, deriv (fun x => u x t) (x₂ t) < 0)
    (t : ℝ) :
    HasDerivAt (fun t => x₂ t - x₁ t)
      ((kernelPrimitive w (x₂ t - x₁ t) + s - h) *
        (1 / deriv (fun x => u x t) (x₁ t) + 1 / -deriv (fun x => u x t) (x₂ t))) t := by
  have hlevels (τ : ℝ) : u (x₁ τ) τ = h ∧ u (x₂ τ) τ = h :=
    level_at_endpoints (hu.continuous.comp (continuous_id.prodMk continuous_const)) (hlt τ) (hex τ)
  have hinput (x : ℝ) (hx : x = x₁ t ∨ x = x₂ t) :
      fieldInput w h s (fun y ↦ u y t) x = kernelPrimitive w (x₂ t - x₁ t) + s := by
    rw [fieldInput_eq_interval (hlt t).le (hex t)]
    rcases hx with rfl | rfl
    · simp only [sub_self]
      congr 1
      calc
        (∫ z in (x₁ t - x₂ t)..(0 : ℝ), w z) = ∫ z in (0 : ℝ)..(x₂ t - x₁ t), w (-z) := by
          rw [intervalIntegral.integral_comp_neg, neg_sub, neg_zero]
        _ = kernelPrimitive w (x₂ t - x₁ t) := by simp only [hw.even, kernelPrimitive]
    · simp [kernelPrimitive]
  let v := kernelPrimitive w (x₂ t - x₁ t) + s - h
  have htime (x : ℝ) (hx : x = x₁ t ∨ x = x₂ t) : HasDerivAt (u x) v t := by
    have hlevel : u x t = h := hx.elim (fun e ↦ e.symm ▸ (hlevels t).1)
      (fun e ↦ e.symm ▸ (hlevels t).2)
    simpa only [hlevel, hinput x hx, v, sub_eq_add_neg, add_comm] using heq x t
  have h₁ := interface_velocity (hu.differentiable one_ne_zero _) (hx₁ t)
    (fun τ ↦ (hlevels τ).1) (htime _ (Or.inl rfl)) (hc₁ t).ne'
  have h₂ := interface_velocity (hu.differentiable one_ne_zero _) (hx₂ t)
    (fun τ ↦ (hlevels τ).2) (htime _ (Or.inr rfl)) (hc₂ t).ne
  have hwidth : HasDerivAt (fun τ ↦ x₂ τ - x₁ τ) _ t := h₂.sub h₁
  convert hwidth using 2
  simp only [div_neg]
  ring

end WantedExt.Biology.Neuroscience.AmariBumpWanted
