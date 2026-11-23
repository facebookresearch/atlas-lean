/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ShallowWaterCharacteristics
import PhyslibExt.EarthScience.ShallowWaterNonlinear
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Shallow-water characteristic speed checks

Consumers of `PhyslibExt.EarthScience.ShallowWaterCharacteristics`:
public shapes of all five results, the conservative-to-quasilinear
producer chain, and rest, dry, and negative-depth instances.

## i. Overview

These are elaboration and boundary checks, not new results. The numeric
instances use gravity `4` so the rest wave speed at unit depth is the
rational number `2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Public shapes and the producer chain
- B. Rest, dry, and negative-depth instances

## iv. References

- `PhyslibExt.EarthScience.ShallowWaterCharacteristics`
- `PhyslibExt.EarthScience.ShallowWaterNonlinear`
-/

open Matrix MathlibExt.Analysis.ODE.ContinuumBalances

/-! ## A. Public shapes and the producer chain -/

/-- Public shape of the quasilinear bridge. -/
example {h u : ℝ → ℝ → ℝ} {g t x hₜ hₓ uₜ uₓ : ℝ} :
    (hₜ + u t x * hₓ + h t x * uₓ = 0 ∧
      uₜ + u t x * uₓ + g * hₓ = 0) ↔
    ![hₜ, uₜ] + EarthScience.shallowWaterPrimitiveMatrix g (h t x) (u t x)
      *ᵥ ![hₓ, uₓ] = 0 :=
  EarthScience.shallow_water_primitive_iff_quasilinear

/-- Producer chain: conservative form at a wet point is the quasilinear
system for the primitive coefficient matrix. -/
example {h u : ℝ → ℝ → ℝ} {g t x hₜ hₓ uₜ uₓ : ℝ}
    (hpos : 0 < h t x)
    (dht : HasDerivAt (fun τ => h τ x) hₜ t)
    (dhx : HasDerivAt (h t) hₓ x)
    (dut : HasDerivAt (fun τ => u τ x) uₜ t)
    (dux : HasDerivAt (u t) uₓ x) :
    (localConservation h (fun τ y => h τ y * u τ y) 0 t x ∧
      localConservation (fun τ y => h τ y * u τ y)
        (fun τ y => h τ y * u τ y ^ 2 + g * h τ y ^ 2 / 2) 0 t x) ↔
    ![hₜ, uₜ] + EarthScience.shallowWaterPrimitiveMatrix g (h t x) (u t x)
      *ᵥ ![hₓ, uₓ] = 0 :=
  (EarthScience.shallow_water_conservative_iff_primitive
    hpos dht dhx dut dux).trans
    EarthScience.shallow_water_primitive_iff_quasilinear

/-- Public shape of the characteristic speeds. -/
example {g h u : ℝ} (hgh : 0 ≤ g * h) :
    (EarthScience.shallowWaterPrimitiveMatrix g h u).charpoly.roots =
      {u - √(g * h), u + √(g * h)} :=
  EarthScience.shallow_water_characteristic_speeds hgh

/-- Public shape of the eigenvector relations. -/
example {g h u : ℝ} (hgh : 0 ≤ g * h) :
    EarthScience.shallowWaterPrimitiveMatrix g h u *ᵥ ![h, √(g * h)] =
        (u + √(g * h)) • ![h, √(g * h)] ∧
      EarthScience.shallowWaterPrimitiveMatrix g h u *ᵥ ![h, -√(g * h)] =
        (u - √(g * h)) • ![h, -√(g * h)] :=
  EarthScience.shallow_water_characteristic_eigenvectors hgh

/-- Public shape of distinctness exactly at positive depth. -/
example {g h u : ℝ} (hg : 0 < g) (hh : 0 ≤ h) :
    (EarthScience.shallowWaterPrimitiveMatrix g h u).charpoly.roots.Nodup
      ↔ 0 < h :=
  EarthScience.shallow_water_characteristic_speeds_nodup_iff hg hh

/-- Public shape of the negative-depth control. -/
example {g h u : ℝ} (hgh : g * h < 0) :
    (EarthScience.shallowWaterPrimitiveMatrix g h u).charpoly.roots = 0 :=
  EarthScience.shallow_water_no_real_characteristic_speeds hgh

/-! ## B. Rest, dry, and negative-depth instances -/

/-- Rest state at unit depth with gravity `4`: speeds `-2` and `2`. -/
example :
    (EarthScience.shallowWaterPrimitiveMatrix 4 1 0).charpoly.roots
      = {-2, 2} := by
  rw [EarthScience.shallow_water_characteristic_speeds
    (by norm_num : (0 : ℝ) ≤ 4 * 1)]
  have hs : √(4 * 1 : ℝ) = 2 := by
    rw [show (4 * 1 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs]
  norm_num

/-- The rest-state speeds are distinct. -/
example :
    (EarthScience.shallowWaterPrimitiveMatrix 4 1 0).charpoly.roots.Nodup :=
  (EarthScience.shallow_water_characteristic_speeds_nodup_iff
    (by norm_num) (by norm_num)).mpr (by norm_num)

/-- Dry state: both speeds collapse to the velocity (double root). -/
example :
    (EarthScience.shallowWaterPrimitiveMatrix 4 0 3).charpoly.roots
      = {3, 3} := by
  rw [EarthScience.shallow_water_characteristic_speeds
    (by norm_num : (0 : ℝ) ≤ 4 * 0)]
  simp

/-- Negative depth: no real characteristic speed. -/
example :
    (EarthScience.shallowWaterPrimitiveMatrix 4 (-1) 0).charpoly.roots
      = 0 :=
  EarthScience.shallow_water_no_real_characteristic_speeds (by norm_num)

/-- Eigenvector instance at the rest state. -/
example :
    EarthScience.shallowWaterPrimitiveMatrix 4 1 0 *ᵥ ![1, 2]
      = (2 : ℝ) • ![1, 2] := by
  have h := (EarthScience.shallow_water_characteristic_eigenvectors
    (g := 4) (h := 1) (u := 0) (by norm_num)).1
  have hs : √(4 * 1 : ℝ) = 2 := by
    rw [show (4 * 1 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [hs] at h
  simpa using h

/-- The characteristic-direction vectors are nonzero at nonzero depth. -/
example {g h : ℝ} (hh : h ≠ 0) :
    ![h, √(g * h)] ≠ 0 ∧ ![h, -√(g * h)] ≠ 0 := by
  constructor <;> intro hv <;> exact hh (by simpa using congrFun hv 0)
