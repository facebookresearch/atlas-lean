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

- Standard structural-dynamics treatments of base excitation
  (relative-coordinate formulation).

## A. Relative oscillator
-/

@[expose] public section

namespace RelativeOscillator

/-- Relative-coordinate oscillator identities. The absolute
coordinate `x` obeys the base-excited equation
`m * xa + c * (xv - yv) + k * (x - y) = pf`, where `y` is the base
displacement with acceleration `ag = ya`. For the relative
displacement `u = x - y`:
(1) `u` has velocity `xv - yv` and acceleration `xa - ya`;
(2) the relative equation is `m * (xa - ya) + c * (xv - yv) + k * u
    = pf - m * ag`;
(3) the relative energy `E = m/2 * (xv-yv)^2 + k/2 * u^2` satisfies
    `E' = (xv - yv) * (pf - m * ag) - c * (xv - yv)^2`. -/
theorem relative_equation_and_energy {m c k : ℝ}
    (x y u xv yv xa ya pf : ℝ → ℝ)
    (hu : ∀ t, u t = x t - y t)
    (hx : ∀ t, HasDerivAt x (xv t) t)
    (hy : ∀ t, HasDerivAt y (yv t) t)
    (hxv : ∀ t, HasDerivAt xv (xa t) t)
    (hyv : ∀ t, HasDerivAt yv (ya t) t)
    (habs : ∀ t, m * xa t + c * (xv t - yv t) + k * (x t - y t) = pf t)
    (t : ℝ) :
    HasDerivAt u (xv t - yv t) t
      ∧ m * (xa t - ya t) + c * (xv t - yv t) + k * u t
          = pf t - m * ya t
      ∧ HasDerivAt (fun s => m / 2 * (xv s - yv s) ^ 2
            + k / 2 * (u s) ^ 2)
          ((xv t - yv t) * (pf t - m * ya t) - c * (xv t - yv t) ^ 2) t := by
  have hfun : u = x - y := funext hu
  have hvel : HasDerivAt u (xv t - yv t) t := by
    rw [hfun]
    exact (hx t).sub (hy t)
  have heq : m * (xa t - ya t) + c * (xv t - yv t) + k * u t
      = pf t - m * ya t := by
    linear_combination habs t + k * hu t
  have hv : HasDerivAt (fun s => xv s - yv s) (xa t - ya t) t :=
    (hxv t).sub (hyv t)
  refine ⟨hvel, heq, ?_⟩
  simp_rw [pow_two]
  have hE : HasDerivAt (fun s => m / 2 * ((xv s - yv s) * (xv s - yv s))
      + k / 2 * (u s * u s)) (_ : ℝ) t :=
    ((hv.mul hv).const_mul (m / 2)).add ((hvel.mul hvel).const_mul (k / 2))
  convert hE using 1
  linear_combination (-(xv t - yv t)) * habs t - k * (xv t - yv t) * hu t

end RelativeOscillator
