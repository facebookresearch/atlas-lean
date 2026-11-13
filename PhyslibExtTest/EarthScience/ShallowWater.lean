/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ShallowWater

/-!
# Shallow-water waves, tides, and sea level

Concrete consumers of `PhyslibExt.EarthScience.ShallowWater`.

## i. Overview

Wave speed for `g = 9.8`, `H = 10`, the zero-field instance of the algebraic core, the public
shape of the wave-equation theorem, and the nonzero smooth solution `g = H = 1`,
`η t x = t ^ 2 + x ^ 2`, `u t x = -2 * t * x`, whose second derivatives are both `2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric and boundary checks
- B. Nonzero shallow-water solution

## iv. References

- `PhyslibExt.EarthScience.ShallowWater`
-/

/-! ## A. Numeric and boundary checks -/

/-- Wave speed for `g = 9.8`, `H = 10`: `√98 > 0` and `(√98)² = 98`. -/
example : 0 < Real.sqrt ((9.8 : ℝ) * 10) ∧ Real.sqrt ((9.8 : ℝ) * 10) ^ 2 = (9.8 : ℝ) * 10 :=
  EarthScience.shallow_water_wave_speed (by norm_num) (by norm_num)

/-- Zero-field instance of the algebraic core: `η = u = 0` satisfies its hypotheses. -/
example : deriv (fun t' => deriv (fun s => (0 : ℝ → ℝ → ℝ) s (0 : ℝ)) t') (0 : ℝ) =
    (9.8 : ℝ) * 10 * deriv (fun x' => deriv (fun x'' => (0 : ℝ → ℝ → ℝ) (0 : ℝ) x'') x') (0 : ℝ) :=
  EarthScience.wave_eq_of_deriv_system (η := fun _ _ => 0) (u := fun _ _ => 0) (H := 10)
    (g := 9.8) 0 0
    (by intro t x; simpa using (hasDerivAt_const t (0 : ℝ)))
    (by intro t x; simpa using (hasDerivAt_const t (0 : ℝ)))
    (by intro t x; simpa using (hasDerivAt_const t (0 : ℝ)))
    (by intro t x; simp)

/-- Public shape of the wave-equation theorem, with spatial `HasDerivAt` hypotheses. -/
example {η u ηx ux : ℝ → ℝ → ℝ} {H g : ℝ} (t x : ℝ)
    (hηx : ∀ t x, HasDerivAt (fun x' => η t x') (ηx t x) x)
    (hux : ∀ t x, HasDerivAt (fun x' => u t x') (ux t x) x)
    (hcont : ∀ t x, HasDerivAt (fun t' => η t' x) (-H * ux t x) t)
    (hmom : ∀ t x, HasDerivAt (fun t' => u t' x) (-g * ηx t x) t)
    (hcomm : ∀ t x, HasDerivAt (fun t' => ux t' x)
      (deriv (fun x' => deriv (fun t' => u t' x') t) x) t)
    (hdiff : ∀ t x, DifferentiableAt ℝ (fun x' => ηx t x') x) :
    deriv (fun t' => deriv (fun s => η s x) t') t = g * H * deriv (fun x' => ηx t x') x :=
  EarthScience.shallow_water_wave_eq t x hηx hux hcont hmom hcomm hdiff

/-! ## B. Nonzero shallow-water solution -/

/-- Nonzero smooth solution with `g = H = 1`: `η t x = t ^ 2 + x ^ 2` and `u t x = -2 * t * x`,
with `ηx t x = 2 * x` and `ux t x = -2 * t`. Continuity `∂ₜη = 2 * t = -∂ₓu` and momentum
`∂ₜu = -2 * x = -∂ₓη` both hold, and the theorem gives `∂ₜ²η = ∂ₓ²η`. -/
example (t x : ℝ) :
    deriv (fun t' => deriv (fun s => s ^ 2 + x ^ 2) t') t = 1 * 1 * deriv (fun x' => 2 * x') x :=
  EarthScience.shallow_water_wave_eq (η := fun t x => t ^ 2 + x ^ 2)
    (u := fun t x => -2 * t * x) (ηx := fun _ x => 2 * x) (ux := fun t _ => -2 * t)
    (H := 1) (g := 1) t x
    (fun t x => by simpa using (hasDerivAt_pow 2 x).const_add (t ^ 2))
    (fun t x => by simpa using (hasDerivAt_id' x).const_mul (-2 * t))
    (fun t x => by
      convert (hasDerivAt_pow 2 t).add_const (x ^ 2) using 1
      norm_num)
    (fun t x => by
      convert ((hasDerivAt_id' t).const_mul (-2)).mul_const x using 1
      ring)
    (fun t x => by
      have hin : ∀ x' : ℝ, deriv (fun t' => -2 * t' * x') t = -2 * x' := fun x' => by
        rw [(((hasDerivAt_id' t).const_mul (-2)).mul_const x').deriv]
        ring
      simp only [hin]
      rw [((hasDerivAt_id' x).const_mul (-2)).deriv]
      simpa using (hasDerivAt_id' t).const_mul (-2))
    (fun t x => (differentiableAt_id.const_mul 2))

/-- In that solution both sides of the wave equation equal `2`, so it is not a zero instance. -/
example (t x : ℝ) :
    deriv (fun t' => deriv (fun s => s ^ 2 + x ^ 2) t') t = 2 ∧
      (1 : ℝ) * 1 * deriv (fun x' => 2 * x') x = 2 := by
  have hin : ∀ t' : ℝ, deriv (fun s => s ^ 2 + x ^ 2) t' = 2 * t' := fun t' => by
    rw [((hasDerivAt_pow 2 t').add_const (x ^ 2)).deriv]
    norm_num
  simp only [hin]
  constructor
  · rw [((hasDerivAt_id' t).const_mul 2).deriv]
    ring
  · rw [((hasDerivAt_id' x).const_mul 2).deriv]
    ring
