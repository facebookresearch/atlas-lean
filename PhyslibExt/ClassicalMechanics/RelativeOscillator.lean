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
    (t : ℝ)
    (hx : ∀ᶠ s in nhds t, HasDerivAt x (xv s) s)
    (hy : ∀ᶠ s in nhds t, HasDerivAt y (yv s) s)
    (hxv : ∀ᶠ s in nhds t, HasDerivAt xv (xa s) s)
    (hyv : ∀ᶠ s in nhds t, HasDerivAt yv (ya s) s)
    (habs : m * xa t + c * (xv t - yv t) + k * (x t - y t) = pf t) :
    HasDerivAt u (xv t - yv t) t
      ∧ m * (xa t - ya t) + c * (xv t - yv t) + k * u t
          = pf t - m * ya t
      ∧ HasDerivAt (fun s => m / 2 * (xv s - yv s) ^ 2
            + k / 2 * (u s) ^ 2)
          ((xv t - yv t) * (pf t - m * ya t) - c * (xv t - yv t) ^ 2) t := by
  have hxt : HasDerivAt x (xv t) t := hx.self_of_nhds
  have hyt : HasDerivAt y (yv t) t := hy.self_of_nhds
  have hxvt : HasDerivAt xv (xa t) t := hxv.self_of_nhds
  have hyvt : HasDerivAt yv (ya t) t := hyv.self_of_nhds
  have huv : HasDerivAt (x - y) (xv t - yv t) t := hxt.sub hyt
  have heq_u : u =ᶠ[nhds t] (x - y) := by
    filter_upwards with s
    simp [hu s, Pi.sub_apply]
  have hu_deriv : HasDerivAt u (xv t - yv t) t :=
    huv.congr_of_eventuallyEq heq_u
  have hut : u t = x t - y t := hu t
  have hrel : m * (xa t - ya t) + c * (xv t - yv t) + k * u t
      = pf t - m * ya t := by
    rw [hut] at *
    linarith
  refine ⟨hu_deriv, hrel, ?_⟩
  have hvv : HasDerivAt (xv - yv) (xa t - ya t) t := hxvt.sub hyvt
  have hpow1 : HasDerivAt ((xv - yv) ^ 2) (2 * (xv t - yv t) * (xa t - ya t)) t := by
    have h := hvv.pow 2
    simpa using h
  have hpow2 : HasDerivAt (u ^ 2) (2 * u t * (xv t - yv t)) t := by
    have h := hu_deriv.pow 2
    simpa using h
  have hE1 : HasDerivAt (fun s => m / 2 * (((xv - yv) ^ 2) s))
      (m / 2 * (2 * (xv t - yv t) * (xa t - ya t))) t :=
    HasDerivAt.const_mul (m / 2) hpow1
  have hE2 : HasDerivAt (fun s => k / 2 * ((u ^ 2) s))
      (k / 2 * (2 * u t * (xv t - yv t))) t :=
    HasDerivAt.const_mul (k / 2) hpow2
  have hEadd : HasDerivAt ((fun s => m / 2 * (((xv - yv) ^ 2) s))
      + (fun s => k / 2 * ((u ^ 2) s)))
      (m / 2 * (2 * (xv t - yv t) * (xa t - ya t))
        + k / 2 * (2 * u t * (xv t - yv t))) t :=
    hE1.add hE2
  have heq_E : (fun s => m / 2 * (xv s - yv s) ^ 2 + k / 2 * (u s) ^ 2)
      =ᶠ[nhds t] (((fun s => m / 2 * (((xv - yv) ^ 2) s))
        + (fun s => k / 2 * ((u ^ 2) s)))) := by
    filter_upwards with s
    simp [Pi.add_apply, Pi.pow_apply, Pi.sub_apply]
  have hE : HasDerivAt (fun s => m / 2 * (xv s - yv s) ^ 2 + k / 2 * (u s) ^ 2)
      (m / 2 * (2 * (xv t - yv t) * (xa t - ya t))
        + k / 2 * (2 * u t * (xv t - yv t))) t :=
    hEadd.congr_of_eventuallyEq heq_E
  have hder : m / 2 * (2 * (xv t - yv t) * (xa t - ya t))
        + k / 2 * (2 * u t * (xv t - yv t))
      = (xv t - yv t) * (pf t - m * ya t) - c * (xv t - yv t) ^ 2 := by
    have hrel' : m * (xa t - ya t) + k * u t
        = (pf t - m * ya t) - c * (xv t - yv t) := by linarith
    have hcalc : m / 2 * (2 * (xv t - yv t) * (xa t - ya t))
        + k / 2 * (2 * u t * (xv t - yv t))
        = (xv t - yv t) * (m * (xa t - ya t) + k * u t) := by ring
    rw [hcalc, hrel']
    ring
  rw [hder] at hE
  exact hE

end RelativeOscillator
