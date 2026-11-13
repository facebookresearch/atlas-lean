/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.RotatingFrames

/-!
# Rotating-frame checks

Concrete consumers of `PhyslibExt.EarthScience.RotatingFrames`: the
Coriolis dot product for rotation about the `z`-axis and the transport law
for a curve in the `y–z` plane.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`Ω = (0, 0, 1)` and `v = (1, 2, 3)`, `2 Ω × v = (-4, 2, 0)` and
`v ⬝ᵥ (2 Ω × v) = -4 + 4 + 0 = 0`. The curve `r(t) = (0, t, 0)` has
`Ω × r(t) = (0, 0, t)` with derivative `(0, 0, 1) = Ω × r'(t)` (for
`Ω = (1, 0, 0)`).

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Coriolis perpendicularity for rotation about `z`
- B. Transport

## iv. References

- `PhyslibExt.EarthScience.RotatingFrames`
-/

open Matrix

/-- Rotation about `z`: `v = (1, 2, 3)` gives `2 Ω × v = (-4, 2, 0)` and
the dot product vanishes. -/
example : (![1, 2, 3] : Fin 3 → ℝ) ⬝ᵥ (2 • ![(-2 : ℝ), 1, 0]) = 0 := by
  have h := EarthScience.dot_coriolis_eq_zero ![0, 0, 1] ![1, 2, 3]
  have hv : (![0, 0, 1] : Fin 3 → ℝ) ⨯₃ ![1, 2, 3] = ![(-2 : ℝ), 1, 0] := by
    rw [cross_apply]
    ext j
    fin_cases j <;> simp
  rw [hv] at h
  exact h

/-- Zero rotation: the Coriolis term vanishes identically. -/
example (v : Fin 3 → ℝ) : v ⬝ᵥ (2 • ((0 : Fin 3 → ℝ) ⨯₃ v)) = 0 :=
  EarthScience.dot_coriolis_eq_zero 0 v

/-- Transport: for `Ω = (1, 0, 0)` and `r(t) = (0, t, 0)`, `Ω × r(t) =
(0, 0, t)` has derivative `(0, 0, 1)`. -/
example (t : ℝ) :
    HasDerivAt (fun t => ![0, 0, t]) ![0, 0, 1] t := by
  have h : ∀ i, HasDerivAt (fun t => ![0, t, 0] i) (![0, 1, 0] i) t := by
    intro i
    fin_cases i
    · exact hasDerivAt_const t (0 : ℝ)
    · exact hasDerivAt_id t
    · exact hasDerivAt_const t (0 : ℝ)
  have h2 := EarthScience.hasDerivAt_cross_const ![1, 0, 0] (fun t => ![0, t, 0])
    ![0, 1, 0] t h
  have eF : (fun t : ℝ => (![1, 0, 0] : Fin 3 → ℝ) ⨯₃ ![0, t, 0]) =
      (fun t : ℝ => ![0, 0, t]) := by
    funext s
    rw [cross_apply]
    ext j
    fin_cases j <;> simp
  have eG : (![1, 0, 0] : Fin 3 → ℝ) ⨯₃ ![0, 1, 0] = ![0, 0, 1] := by
    rw [cross_apply]
    ext j
    fin_cases j <;> simp
  exact (h2.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq eF.symm)).congr_deriv eG
