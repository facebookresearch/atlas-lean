/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Steady diffusive hillslope profile (H08)

## i. Overview

For the linear diffusive hillslope model `z_t = U + D * z_xx` on `[-L, L]`
with fixed base level `z(±L) = 0`, the profile
`z(x) = U * (L ^ 2 - x ^ 2) / (2 * D)` is steady: its first derivative is
`-U * x / D`, its second derivative is `-U / D`, and so
`U + D * z''(x) = 0`. Here `D > 0` is the diffusivity, `L > 0` the
half-width, and `U ≥ 0` the uplift rate. The source law is empirical;
no claim about real landscapes is made.

## ii. Key results

- `EarthScience.h08_profile_boundary`: the profile meets `z(±L) = 0`.
- `EarthScience.h08_profile_hasDerivAt`: `z'(x) = -U * x / D`.
- `EarthScience.h08_profile_steady`: `z''(x) = -U / D` and `U + D * z'' = 0`.
- `EarthScience.h08_profile_witness`: `U = 2, D = 1, L = 3` gives `z(0) = 9`.

## iii. Table of contents

- A. Boundary values
- B. Derivatives and steadiness

## iv. References

- `HasDerivAt.const_mul` / `sub` / `div_const`, `hasDerivAt_pow` in Mathlib.
-/

@[expose] public section

namespace EarthScience

set_option linter.unusedVariables false in
/-- Steady diffusive hillslope profile: `z(x) = U*(L^2 - x^2)/(2*D)`. -/
theorem h08_profile_boundary {D L U : ℝ} (hD : 0 < D) (hL : 0 < L) (hU : 0 ≤ U) :
    (U * (L ^ 2 - L ^ 2) / (2 * D) = 0) ∧
    (U * (L ^ 2 - (-L) ^ 2) / (2 * D) = 0) := by
  constructor
  · have h : L ^ 2 - L ^ 2 = (0 : ℝ) := by ring
    rw [h]
    simp
  · have h : L ^ 2 - (-L) ^ 2 = (0 : ℝ) := by ring
    rw [h]
    simp

set_option linter.unusedVariables false in
/-- The profile has derivative `-U*x/D` at every `x`. -/
theorem h08_profile_hasDerivAt {D L U : ℝ} (hD : 0 < D) (hL : 0 < L) (hU : 0 ≤ U) (x : ℝ) :
    HasDerivAt (fun x => U * (L ^ 2 - x ^ 2) / (2 * D)) (-U * x / D) x := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hsub : HasDerivAt (fun x : ℝ => L ^ 2 - x ^ 2) (0 - 2 * x) x :=
    (hasDerivAt_const x (L ^ 2)).sub hpow
  have hmul : HasDerivAt (fun y : ℝ => U * (L ^ 2 - y ^ 2)) (U * (0 - 2 * x)) x :=
    HasDerivAt.const_mul U hsub
  have hdiv : HasDerivAt (fun y : ℝ => U * (L ^ 2 - y ^ 2) / (2 * D))
      (U * (0 - 2 * x) / (2 * D)) x :=
    HasDerivAt.div_const hmul (2 * D)
  have hder : U * (0 - 2 * x) / (2 * D) = -U * x / D := by
    field_simp
    ring
  rw [hder] at hdiv
  exact hdiv

set_option linter.unusedVariables false in
/-- The derivative function has derivative `-U/D` at every `x`, so
`U + D * z''(x) = 0`: the profile is steady for `z_t = U + D*z_xx`. -/
theorem h08_profile_steady {D L U : ℝ} (hD : 0 < D) (hL : 0 < L) (hU : 0 ≤ U) (x : ℝ) :
    HasDerivAt (fun x => -U * x / D) (-U / D) x ∧ U + D * (-U / D) = 0 := by
  have hD' : D ≠ 0 := ne_of_gt hD
  have h1 : HasDerivAt (fun x : ℝ => x) 1 x := hasDerivAt_id x
  have h2 : HasDerivAt (fun y : ℝ => -U * y) (-U * 1) x :=
    HasDerivAt.const_mul (-U) h1
  have h3 : HasDerivAt (fun y : ℝ => -U * y / D) (-U * 1 / D) x :=
    HasDerivAt.div_const h2 D
  have hder : -U * 1 / D = -U / D := by ring
  rw [hder] at h3
  refine ⟨h3, ?_⟩
  field_simp
  ring

/-- Non-vacuous witness: `U = 2, D = 1, L = 3` gives `z(0) = 9`. -/
theorem h08_profile_witness :
    (2 : ℝ) * ((3 : ℝ) ^ 2 - (0 : ℝ) ^ 2) / (2 * 1) = 9 := by
  norm_num

end EarthScience
