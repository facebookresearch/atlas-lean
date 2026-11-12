 /-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.G14RemoteSensing

/-!
# Remote-sensing observation operators checks

Concrete consumers of `PhyslibExt.EarthScience.G14RemoteSensing`:
the trivial zero solution, the empty basis, and the integral
`∫ _x in 0..2, 1 = 2`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Concrete checks

## iv. References

- `PhyslibExt.EarthScience.G14RemoteSensing`
-/

/-- Trivial zero solution: integrating-factor identity at `L = 2`. -/
example :
    Real.exp (∫ _x in (0:ℝ)..(2:ℝ), (1:ℝ)) * (fun _ => (0:ℝ)) 2
      = 0 + ∫ s in (0:ℝ)..(2:ℝ), Real.exp (∫ _x in (0:ℝ)..s, (1:ℝ)) * (0:ℝ) :=
  EarthScience.g14_integrating_factor (κ := fun _ => 1) (j := fun _ => 0)
    (I := fun _ => 0) (L := 2) (I0 := 0) (by norm_num) continuous_const continuous_const
    (fun t => by simpa using hasDerivAt_const t (0:ℝ)) rfl

/-- Trivial zero solution: explicit Duhamel form at `L = 2`. -/
example :
    (fun _ => (0:ℝ)) 2 = 0 * Real.exp (-∫ _x in (0:ℝ)..(2:ℝ), (1:ℝ))
      + ∫ s in (0:ℝ)..(2:ℝ), (0:ℝ) * Real.exp (-∫ _x in s..(2:ℝ), (1:ℝ)) :=
  EarthScience.g14_explicit_form (κ := fun _ => 1) (j := fun _ => 0)
    (I := fun _ => 0) (L := 2) (I0 := 0) (by norm_num) continuous_const continuous_const
    (fun t => by simpa using hasDerivAt_const t (0:ℝ)) rfl

/-- Empty basis: the affine observation operator reduces to the homogeneous term. -/
example (L : ℝ) (hL : 0 ≤ L) :
    (fun _ => (0:ℝ)) L = 0 * Real.exp (-∫ _x in (0:ℝ)..L, (1:ℝ))
      + ∑ _i ∈ (∅ : Finset (Fin 1)),
        (0:ℝ) * (∫ t in (0:ℝ)..L, (0:ℝ) * Real.exp (-∫ _x in t..L, (1:ℝ))) := by
  have h := EarthScience.g14_finite_basis (κ := fun _ => 1) (s := (∅ : Finset (Fin 1)))
    (a := fun _ => 0) (b := fun _ _ => 0) (L := L) (I0 := 0)
    (I := fun _ => 0) hL continuous_const (fun _i hi => by simp at hi)
    (fun t => by simpa using hasDerivAt_const t (0:ℝ)) rfl
  rw [Finset.sum_empty, add_zero] at h ⊢
  exact h

/-- Integral evaluation: `∫ _x in 0..2, 1 = 2`. -/
example : (∫ _x in (0:ℝ)..(2:ℝ), (1:ℝ)) = 2 := by simp

