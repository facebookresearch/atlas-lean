/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Nonlinear 1D shallow water: Riemann-invariant transport

At a wet point of a classical solution of the primitive shallow-water
equations, each Riemann invariant `u ± 2√(g h)` is transported along its
paired characteristic speed `u ± √(g h)`. At nonpositive depth both
transports can fail while the primitive equations still hold.

## i. Overview

One horizontal dimension, flat frictionless bed, no rotation, and constant
gravitational acceleration `g`, in the conventions of
`PhyslibExt.EarthScience.ShallowWaterNonlinear`: fields are functions of
time first, then space; `h t x` is the total fluid depth (not the surface
elevation) and `u t x` is the depth-averaged velocity, positive towards
increasing `x`. The statement is classical and pointwise at one point
`(t, x)`: the four first partials are the `HasDerivAt` slice witnesses
`hₜ`, `hₓ`, `uₜ`, `uₓ` of that module, and the primitive form is its pair
`hₜ + u hₓ + h uₓ = 0` (mass) and `uₜ + u uₓ + g hₓ = 0` (momentum),
verbatim. A conservative solution at a wet point therefore feeds the
transport theorem through
`EarthScience.shallow_water_conservative_iff_primitive`.

With gravity-wave speed `c = √(g h)`, the Riemann invariants are written
inline as `u ± 2 * √(g * h)` (no new definition), and the transport
operator `∂ₜ + (u ± c) ∂ₓ` is written with Mathlib's `deriv` of the time
and space slices. Signs are paired: speed `u + c` transports `u + 2 c`,
and speed `u - c` transports `u - 2 c`; these speeds are the roots in
`EarthScience.shallow_water_characteristic_speeds`. The invariants and
their transport are derived here from the primitive form above, not
quoted from the reference.

Admission is `0 < g` and `0 < h t x`. Positivity of `g` is the physical
premise: at `g = 0` the identity degenerates to `uₜ + u uₓ = 0`, while for
`g < 0` it fails. `Real.sqrt` is totalized (`√y = 0` for `y ≤ 0`), and the
control in section B shows both transports fail at every nonpositive
depth value even when the primitive equations hold, so positive depth
cannot be weakened. No solution existence, weak or discontinuous
solutions, invariants across shocks, bed slope, friction, rotation,
entropy, or convergence claim is made.

## ii. Key results

- `EarthScience.shallow_water_riemann_invariant_transport`: both paired
  transport equations at a wet point.
- `EarthScience.exists_nonpos_depth_primitive_not_riemann_transport`: at
  nonpositive depth the primitive equations do not imply either transport.

## iii. Table of contents

- A. Riemann-invariant transport
- B. Nonpositive-depth control

## iv. References

- G. K. Vallis, *Atmospheric and Oceanic Fluid Dynamics*, 2nd ed.,
  Cambridge University Press (2017), Ch. 3, §3.1, eqs. (3.1.1) and
  (3.1.2), for the shallow-water equations in primitive form.
- `PhyslibExt.EarthScience.ShallowWaterNonlinear` and
  `PhyslibExt.EarthScience.ShallowWaterCharacteristics`.

## A. Riemann-invariant transport
-/

@[expose] public section

namespace EarthScience

/-- Riemann-invariant transport for 1D flat-bed shallow water at a wet
point. Let `h` be the depth and `u` the velocity, with time and space
slices differentiable at `(t, x)` with partials `hₜ`, `hₓ`, `uₜ`, `uₓ`,
let gravity and the depth there be positive, and let the primitive
equations `hₜ + u hₓ + h uₓ = 0` and `uₜ + u uₓ + g hₓ = 0` hold at
`(t, x)`. Then, with `c = √(g h)`, both paired transport equations
`(∂ₜ + (u + c) ∂ₓ)(u + 2 c) = 0` and `(∂ₜ + (u - c) ∂ₓ)(u - 2 c) = 0`
hold at `(t, x)`. -/
theorem shallow_water_riemann_invariant_transport
    {h u : ℝ → ℝ → ℝ} {g t x hₜ hₓ uₜ uₓ : ℝ}
    (hg : 0 < g) (hpos : 0 < h t x)
    (dht : HasDerivAt (fun τ => h τ x) hₜ t)
    (dhx : HasDerivAt (h t) hₓ x)
    (dut : HasDerivAt (fun τ => u τ x) uₜ t)
    (dux : HasDerivAt (u t) uₓ x)
    (hprim : hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
      uₜ + u t x * uₓ + g * hₓ = 0) :
    deriv (fun τ => u τ x + 2 * √(g * h τ x)) t +
        (u t x + √(g * h t x)) *
          deriv (fun y => u t y + 2 * √(g * h t y)) x = 0 ∧
      deriv (fun τ => u τ x - 2 * √(g * h τ x)) t +
        (u t x - √(g * h t x)) *
          deriv (fun y => u t y - 2 * √(g * h t y)) x = 0 := by
  have hgh : 0 < g * h t x := mul_pos hg hpos
  have hne : g * h t x ≠ 0 := ne_of_gt hgh
  have hc : √(g * h t x) ≠ 0 := (Real.sqrt_pos.mpr hgh).ne'
  have hc2 : √(g * h t x) ^ 2 = g * h t x := Real.sq_sqrt hgh.le
  have hTs : HasDerivAt (fun τ => √(g * h τ x)) ((g * hₜ) / (2 * √(g * h t x))) t :=
    (dht.const_mul g).sqrt hne
  have hXs : HasDerivAt (fun y => √(g * h t y)) ((g * hₓ) / (2 * √(g * h t x))) x :=
    (dhx.const_mul g).sqrt hne
  have hT : HasDerivAt (fun τ => u τ x + 2 * √(g * h τ x))
      (uₜ + 2 * ((g * hₜ) / (2 * √(g * h t x)))) t :=
    dut.fun_add (hTs.const_mul 2)
  have hX : HasDerivAt (fun y => u t y + 2 * √(g * h t y))
      (uₓ + 2 * ((g * hₓ) / (2 * √(g * h t x)))) x :=
    dux.fun_add (hXs.const_mul 2)
  have hTm : HasDerivAt (fun τ => u τ x - 2 * √(g * h τ x))
      (uₜ - 2 * ((g * hₜ) / (2 * √(g * h t x)))) t :=
    dut.fun_sub (hTs.const_mul 2)
  have hXm : HasDerivAt (fun y => u t y - 2 * √(g * h t y))
      (uₓ - 2 * ((g * hₓ) / (2 * √(g * h t x)))) x :=
    dux.fun_sub (hXs.const_mul 2)
  rw [hT.deriv, hX.deriv, hTm.deriv, hXm.deriv]
  constructor
  · field_simp
    linear_combination (√(g * h t x)) * hprim.2 + g * hprim.1 + uₓ * hc2
  · field_simp
    linear_combination (√(g * h t x)) * hprim.2 - g * hprim.1 - uₓ * hc2

/-! ## B. Nonpositive-depth control -/

/-- Nonpositive depth rejected: for positive gravity and every depth
value `d ≤ 0`, there are fields with `h t x = d` whose slice
partials exist and which satisfy both primitive equations at `(t, x)`,
but for which both paired transport equations fail there (with `√y = 0`
for `y ≤ 0`, and `deriv` equal to `0` where a slice is not differentiable). So the
positive-depth admission of `shallow_water_riemann_invariant_transport`
cannot be weakened to `0 ≤ h t x` or dropped. -/
lemma exists_nonpos_depth_primitive_not_riemann_transport
    {g : ℝ} (hg : 0 < g) (t x d : ℝ) (hd : d ≤ 0) :
    ∃ (h u : ℝ → ℝ → ℝ) (hₜ hₓ uₜ uₓ : ℝ), h t x = d ∧
      HasDerivAt (fun τ => h τ x) hₜ t ∧ HasDerivAt (h t) hₓ x ∧
      HasDerivAt (fun τ => u τ x) uₜ t ∧ HasDerivAt (u t) uₓ x ∧
      (hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
        uₜ + u t x * uₓ + g * hₓ = 0) ∧
      deriv (fun τ => u τ x + 2 * √(g * h τ x)) t +
          (u t x + √(g * h t x)) *
            deriv (fun y => u t y + 2 * √(g * h t y)) x ≠ 0 ∧
      deriv (fun τ => u τ x - 2 * √(g * h τ x)) t +
          (u t x - √(g * h t x)) *
            deriv (fun y => u t y - 2 * √(g * h t y)) x ≠ 0 := by
  refine ⟨fun τ y => d + (y - x), fun τ y => -g * (τ - t), 0, 1, -g, 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show d + (x - x) = d
    ring
  · show HasDerivAt (fun _ : ℝ => d + (x - x)) 0 t
    exact hasDerivAt_const t _
  · show HasDerivAt (fun y : ℝ => d + (y - x)) 1 x
    exact ((hasDerivAt_id x).sub_const x).const_add d
  · show HasDerivAt (fun τ : ℝ => -g * (τ - t)) (-g) t
    simpa using ((hasDerivAt_id t).sub_const t).const_mul (-g)
  · show HasDerivAt (fun _ : ℝ => -g * (t - t)) 0 x
    exact hasDerivAt_const x _
  · show (0 : ℝ) + -g * (t - t) * 1 + (d + (x - x)) * 0 = 0 ∧
        -g + -g * (t - t) * 0 + g * 1 = 0
    constructor <;> simp
  · show deriv (fun τ : ℝ => -g * (τ - t) + 2 * √(g * (d + (x - x)))) t +
        (-g * (t - t) + √(g * (d + (x - x)))) *
          deriv (fun y : ℝ => -g * (t - t) + 2 * √(g * (d + (y - x)))) x ≠ 0
    have h1 : HasDerivAt (fun τ : ℝ => -g * (τ - t)) (-g) t := by
      simpa using ((hasDerivAt_id t).sub_const t).const_mul (-g)
    have h2 : HasDerivAt (fun _ : ℝ => 2 * √(g * (d + (x - x)))) 0 t :=
      hasDerivAt_const t _
    have hT : HasDerivAt (fun τ : ℝ => -g * (τ - t) + 2 * √(g * (d + (x - x)))) (-g) t := by
      simpa using h1.fun_add h2
    have hgd : g * (d + (x - x)) ≤ 0 := by
      have hxx : d + (x - x) = d := by ring
      rw [hxx]
      exact mul_nonpos_of_nonneg_of_nonpos hg.le hd
    have hsqrt : √(g * (d + (x - x))) = 0 := Real.sqrt_eq_zero_of_nonpos hgd
    have hcoeff : -g * (t - t) + √(g * (d + (x - x))) = 0 := by
      rw [hsqrt]
      simp
    rw [hT.deriv, hcoeff, zero_mul, add_zero]
    exact neg_ne_zero.mpr hg.ne'
  · show deriv (fun τ : ℝ => -g * (τ - t) - 2 * √(g * (d + (x - x)))) t +
        (-g * (t - t) - √(g * (d + (x - x)))) *
          deriv (fun y : ℝ => -g * (t - t) - 2 * √(g * (d + (y - x)))) x ≠ 0
    have h1 : HasDerivAt (fun τ : ℝ => -g * (τ - t)) (-g) t := by
      simpa using ((hasDerivAt_id t).sub_const t).const_mul (-g)
    have h2 : HasDerivAt (fun _ : ℝ => 2 * √(g * (d + (x - x)))) 0 t :=
      hasDerivAt_const t _
    have hT : HasDerivAt (fun τ : ℝ => -g * (τ - t) - 2 * √(g * (d + (x - x)))) (-g) t := by
      simpa using h1.fun_sub h2
    have hgd : g * (d + (x - x)) ≤ 0 := by
      have hxx : d + (x - x) = d := by ring
      rw [hxx]
      exact mul_nonpos_of_nonneg_of_nonpos hg.le hd
    have hsqrt : √(g * (d + (x - x))) = 0 := Real.sqrt_eq_zero_of_nonpos hgd
    have hcoeff : -g * (t - t) - √(g * (d + (x - x))) = 0 := by
      rw [hsqrt]
      simp
    rw [hT.deriv, hcoeff, zero_mul, add_zero]
    exact neg_ne_zero.mpr hg.ne'

end EarthScience
