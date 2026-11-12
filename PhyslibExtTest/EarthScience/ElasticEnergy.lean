/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ElasticEnergy

/-!
# Isotropic elastic energy checks

Concrete consumers of `PhyslibExt.EarthScience.ElasticEnergy`: pure
shear, hydrostatic compression, and the singular-modulus boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results. Pure
shear (unit off-diagonal entries, trace `0`) has positive energy for
positive moduli; hydrostatic compression (identity strain, deviator
`0`) has nonnegative energy; zero moduli give zero energy.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Pure shear and hydrostatic compression
- B. Boundary cases
-/

/-- Pure shear with `K = 2, mu = 3`: positive energy. -/
example : 0 < (2 / 2 : ℝ) * (∑ i, (fun a b : Fin 3 =>
      if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then (1 : ℝ) else 0) i i) ^ 2 +
    3 * ∑ i, ∑ j, ((fun a b : Fin 3 =>
        if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then (1 : ℝ) else 0) i j -
      (∑ k, (fun a b : Fin 3 =>
        if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then (1 : ℝ) else 0) k k) / 3 *
      (if i = j then (1 : ℝ) else 0)) ^ 2 :=
  EarthScience.elastic_energy_pos
    (fun a b : Fin 3 => if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then (1 : ℝ) else 0)
    2 3 (by norm_num) (by norm_num) ⟨0, 1, by simp⟩

/-- Hydrostatic compression (identity strain): nonnegative energy. -/
example : 0 ≤ (2 / 2 : ℝ) * (∑ i, (fun _ _ : Fin 3 => (1 : ℝ)) i i) ^ 2 +
    3 * ∑ i, ∑ j, ((fun _ _ : Fin 3 => (1 : ℝ)) i j -
      (∑ k, (fun _ _ : Fin 3 => (1 : ℝ)) k k) / 3 *
      (if i = j then (1 : ℝ) else 0)) ^ 2 :=
  EarthScience.elastic_energy_nonneg (fun _ _ => (1 : ℝ)) 2 3
    (by norm_num) (by norm_num)

/-- Singular boundary: zero moduli give zero energy for any strain. -/
example (ε : Fin 3 → Fin 3 → ℝ) :
    (0 / 2 : ℝ) * (∑ i, ε i i) ^ 2 +
      0 * ∑ i, ∑ j, (ε i j - (∑ k, ε k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 0 := by
  simp
