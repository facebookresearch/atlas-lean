/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Traveling profiles solve constant-speed advection

For a differentiable profile `f` and speed `c`, the traveling wave
`u(t, x) = f (x - c * t)` satisfies the constant-speed advection
equation `u_t + c * u_x = 0`: the chain rule gives `u_t = -c * f'` and
`u_x = f'`, so the two terms cancel. The selected smooth profile
`u(t, x) = sin (x - c * t)` is the concrete instance.

## i. Overview

The general theorem takes the derivative of `f` as a hypothesis
(`HasDerivAt f (f' s) s` at every `s`) and computes both slice
derivatives by composing with the affine inner maps `t ↦ x - c * t`
and `x ↦ x - c * t`, then closes with `ring`. The sine case specializes
it with `Real.hasDerivAt_sin`. This is an exact traveling solution, not
a well-posedness or stability claim: no boundary or initial data are
imposed, and the profile is not required to decay.

## ii. Key results

- `EarthScience.traveling_profile_solves_advection`: a general
  differentiable traveling profile solves advection.
- `EarthScience.sine_traveling_profile_solves_advection`: the sine
  traveling profile solves advection.

## iii. Table of contents

- A. General traveling profile
- B. Sine profile

## iv. References

- `HasDerivAt.comp`, `HasDerivAt.const_sub`, `Real.hasDerivAt_sin`
  (Mathlib).
-/

@[expose] public section

namespace EarthScience

/-! ## A. General traveling profile -/

/-- A general traveling profile solves constant-speed advection: if `f`
is differentiable everywhere with derivative `f'`, then for
`u t x = f (x - c * t)` the advection residual `u_t + c * u_x` is `0`,
with derivatives taken as `deriv` of the `t`- and `x`-slices. -/
theorem traveling_profile_solves_advection {f f' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (c t x : ℝ) :
    deriv (fun t => f (x - c * t)) t
      + c * deriv (fun x => f (x - c * t)) x = 0 := by
  have hid_t : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id' t
  have hmul : HasDerivAt (fun t : ℝ => c * t) (c * 1) t := hid_t.const_mul c
  have hinner_t : HasDerivAt (fun t : ℝ => x - c * t) (-(c * 1)) t :=
    hmul.const_sub x
  have hinner_x : HasDerivAt (fun x_ : ℝ => x_ - c * t) 1 x :=
    (hasDerivAt_id' x).sub_const (c * t)
  have ht : HasDerivAt (fun t => f (x - c * t)) (f' (x - c * t) * (-(c * 1))) t :=
    (hf _).comp t hinner_t
  have hx : HasDerivAt (fun x_ => f (x_ - c * t)) (f' (x - c * t) * 1) x :=
    (hf _).comp x hinner_x
  rw [ht.deriv, hx.deriv]
  ring

/-! ## B. Sine profile -/

/-- The selected smooth profile `u t x = sin (x - c * t)` solves
constant-speed advection: `u_t + c * u_x = 0`. -/
theorem sine_traveling_profile_solves_advection (c t x : ℝ) :
    deriv (fun t => Real.sin (x - c * t)) t
      + c * deriv (fun x => Real.sin (x - c * t)) x = 0 := by
  exact traveling_profile_solves_advection (fun s => Real.hasDerivAt_sin s) c t x

end EarthScience
