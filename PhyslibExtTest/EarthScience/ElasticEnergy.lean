/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import PhyslibExt.EarthScience.ElasticEnergy

/-!
# Isotropic elastic energy checks

Concrete consumers of `PhyslibExt.EarthScience.ElasticEnergy`: pure shear,
hydrostatic compression, an infinitesimal rigid rotation, and the boundary cases
that show why both moduli must be positive.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The strains are
small strains `Elasticity.smallStrain H` of explicit displacement gradients `H`,
with moduli `K = 2`, `μ = 3`:

- pure shear (simple-shear gradient `H 0 1 = 2`, so `ε 0 1 = ε 1 0 = 1`, trace `0`)
  has energy exactly `6`, and positive energy by `elastic_energy_pos`;
- hydrostatic compression (tensile-positive, `H = -1`, so `ε = -1`) has zero
  deviator and energy exactly `9`;
- the rotation gradient `W 0 1 = 1`, `W 1 0 = -1` has zero energy, while the
  algebraic form evaluated on the raw gradient `W` is `6 > 0`;
- with `μ = 0` pure shear has zero energy, and with `K = 0` hydrostatic
  compression has zero energy, so neither positivity hypothesis of
  `elastic_energy_pos` can be dropped.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Pure shear and hydrostatic compression
- B. Rigid rotation
- C. Boundary cases
-/

open scoped Matrix
open Elasticity

/-! ## A. Pure shear and hydrostatic compression -/

/-- Pure shear: `ε = smallStrain H` for the simple-shear gradient `H 0 1 = 2` has
`ε 0 1 = ε 1 0 = 1` and every other entry `0`. -/
lemma pureShear_smallStrain :
    smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] = !![0, 1, 0; 1, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [smallStrain_apply]

/-- Pure shear with `K = 2`, `μ = 3` has positive energy. -/
example : 0 < (2 / 2 : ℝ) * (∑ i, smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] i i) ^ 2 +
    3 * ∑ i, ∑ j, (smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] i j -
      (∑ k, smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 := by
  refine EarthScience.elastic_energy_pos _ 2 3 (by norm_num) (by norm_num) ?_
  rw [pureShear_smallStrain]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num at h01

/-- Pure shear with `K = 2`, `μ = 3` has energy exactly `μ * (1 ^ 2 + 1 ^ 2) = 6`. -/
example : (2 / 2 : ℝ) * (∑ i, smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] i i) ^ 2 +
    3 * ∑ i, ∑ j, (smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] i j -
      (∑ k, smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 6 := by
  rw [pureShear_smallStrain]
  norm_num [Fin.sum_univ_three]

/-- The algebraic lemma also applies to the pure-shear array directly. -/
example : 0 < (2 / 2 : ℝ) * (∑ i, !![(0 : ℝ), 1, 0; 1, 0, 0; 0, 0, 0] i i) ^ 2 +
    3 * ∑ i, ∑ j, (!![(0 : ℝ), 1, 0; 1, 0, 0; 0, 0, 0] i j -
      (∑ k, !![(0 : ℝ), 1, 0; 1, 0, 0; 0, 0, 0] k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 :=
  EarthScience.trace_sq_add_deviator_sq_pos _ 2 3 (by norm_num) (by norm_num)
    ⟨0, 1, by norm_num⟩

/-- Hydrostatic compression: the gradient `H = -1` has small strain `ε = -1`. -/
lemma compression_smallStrain : smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [smallStrain_apply]

/-- Hydrostatic compression `ε = -1` has zero deviator. -/
example (i j : Fin 3) :
    smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) i j -
      (∑ k, smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) k k) / 3 *
        (if i = j then (1 : ℝ) else 0) = 0 := by
  rw [compression_smallStrain]
  fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_three]

/-- Hydrostatic compression `ε = -1` with `K = 2`, `μ = 3` has energy exactly
`(K / 2) * (tr ε) ^ 2 = 9`, from the bulk term alone. -/
example : (2 / 2 : ℝ) * (∑ i, smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) i i) ^ 2 +
    3 * ∑ i, ∑ j, (smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) i j -
      (∑ k, smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 9 := by
  rw [compression_smallStrain]
  norm_num [Fin.sum_univ_three]

/-! ## B. Rigid rotation -/

/-- The rotation gradient `W 0 1 = 1`, `W 1 0 = -1` stores no energy. -/
example : (2 / 2 : ℝ) * (∑ i, smallStrain !![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, 0] i i) ^ 2 +
    3 * ∑ i, ∑ j, (smallStrain !![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, 0] i j -
      (∑ k, smallStrain !![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, 0] k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 0 := by
  refine EarthScience.elastic_energy_of_skew _ ?_ 2 3
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The algebraic form on the raw rotation gradient is `2 * μ = 6`, not zero: only the
small strain gives the elastic energy. -/
example : (2 / 2 : ℝ) * (∑ i, !![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, 0] i i) ^ 2 +
    3 * ∑ i, ∑ j, (!![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, 0] i j -
      (∑ k, !![(0 : ℝ), 1, 0; -1, 0, 0; 0, 0, 0] k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 6 := by
  norm_num [Fin.sum_univ_three]

/-! ## C. Boundary cases -/

/-- With `μ = 0`, nonzero pure shear has zero energy: `elastic_energy_pos` needs
`0 < μ`. -/
example : (2 / 2 : ℝ) * (∑ i, smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] i i) ^ 2 +
    0 * ∑ i, ∑ j, (smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] i j -
      (∑ k, smallStrain !![0, 2, 0; 0, 0, 0; 0, 0, 0] k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 0 := by
  rw [pureShear_smallStrain]
  norm_num [Fin.sum_univ_three]

/-- With `K = 0`, nonzero hydrostatic compression has zero energy:
`elastic_energy_pos` needs `0 < K`. -/
example : (0 / 2 : ℝ) * (∑ i, smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) i i) ^ 2 +
    3 * ∑ i, ∑ j, (smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) i j -
      (∑ k, smallStrain (-1 : Matrix (Fin 3) (Fin 3) ℝ) k k) / 3 *
        (if i = j then (1 : ℝ) else 0)) ^ 2 = 0 := by
  rw [compression_smallStrain]
  norm_num [Fin.sum_univ_three]
