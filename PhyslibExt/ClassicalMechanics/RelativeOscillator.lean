/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Relative-coordinate oscillator identities

## i. Overview

For a base-excited oscillator, the relative displacement `u = x - y`
satisfies the relative equation and the relative-energy power
identity `E' = u' (p - m a_g) - c (u')^2`.

## ii. Key results

- `RelativeOscillator.relative_equation_and_energy`: velocity,
  relative equation, and energy identity in one package.

## iii. Table of contents

- A. Relative oscillator

## iv. References

- A. K. Chopra, *Dynamics of Structures: Theory and Applications
  to Earthquake Engineering*, 5th edition, Pearson, 2017,
  Chapter 6: earthquake excitation in relative coordinates
  (relative displacement equation and its energy form).

## A. Relative oscillator
-/

@[expose] public section

namespace RelativeOscillator

/-- Relative-coordinate oscillator identities at one time `t`.
The absolute coordinate `x` obeys the base-excited equation
`m * xa + c * (xv - yv) + k * (x - y) = pf` at `t`, where `y` is the
base displacement with acceleration value `ya t`. For the relative
displacement `u = x - y` (all times, so `u` is identified near `t`):
(1) `u` has velocity `xv t - yv t` at `t`, and the supplied relative
    velocity function `s ↦ xv s - yv s` has derivative
    `xa t - ya t` at `t`;
(2) the relative equation `m * (xa t - ya t) + c * (xv t - yv t)
    + k * u t = pf t - m * ya t` holds at `t`;
(3) the energy expression `m/2 * (xv-yv)^2 + k/2 * u^2` has
    derivative `(xv t - yv t) * (pf t - m * ya t) - c * (xv t - yv t)^2`
    at `t`.
Here `xa t - ya t` is `u''(t)`, and the energy expression is the
relative energy, when `xv` and `yv` are the velocities of `x` and
`y` on a neighborhood of `t`. -/
theorem relative_equation_and_energy {m c k : ℝ}
    (x y u xv yv xa ya pf : ℝ → ℝ)
    (hu : ∀ t, u t = x t - y t)
    (t : ℝ)
    (hx : HasDerivAt x (xv t) t)
    (hy : HasDerivAt y (yv t) t)
    (hxv : HasDerivAt xv (xa t) t)
    (hyv : HasDerivAt yv (ya t) t)
    (habs : m * xa t + c * (xv t - yv t) + k * (x t - y t) = pf t) :
    HasDerivAt u (xv t - yv t) t
      ∧ HasDerivAt (fun s => xv s - yv s) (xa t - ya t) t
      ∧ m * (xa t - ya t) + c * (xv t - yv t) + k * u t
          = pf t - m * ya t
      ∧ HasDerivAt (fun s => m / 2 * (xv s - yv s) ^ 2
            + k / 2 * (u s) ^ 2)
          ((xv t - yv t) * (pf t - m * ya t) - c * (xv t - yv t) ^ 2) t := by
  have hv : HasDerivAt (fun s => xv s - yv s) (xa t - ya t) t := hxv.sub hyv
  have hu' : HasDerivAt u (xv t - yv t) t :=
    (hx.sub hy).congr_of_eventuallyEq (Filter.Eventually.of_forall hu)
  have h3 : m * (xa t - ya t) + c * (xv t - yv t) + k * u t
      = pf t - m * ya t := by
    rw [hu t]
    linear_combination habs
  refine ⟨hu', hv, h3, ?_⟩
  have hE := (HasDerivAt.const_mul (m / 2) (hv.pow 2)).add
    (HasDerivAt.const_mul (k / 2) (hu'.pow 2))
  convert hE using 2
  linear_combination (yv t - xv t) * h3

end RelativeOscillator
