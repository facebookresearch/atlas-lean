/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.MassMoleFractions

/-!
# Mass/mole fraction conversion checks

Concrete consumers of `PhyslibExt.EarthScience.MassMoleFractions`:
mole fractions `[1/2, 1/2]` with molar masses `[2, 32]` give mass
fractions `[1/17, 16/17]`, and converting back recovers the mole
fractions; the single-species boundary gives fraction `1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.MassMoleFractions`
-/

/-- Mole fractions `[1/2, 1/2]`, molar masses `[2, 32]`: mass fractions sum to `1`. -/
example :
    ∑ i : Fin 2, ((1 / 2 : ℝ) * (if i = 0 then (2 : ℝ) else 32)) /
      (∑ j : Fin 2, (1 / 2 : ℝ) * (if j = 0 then (2 : ℝ) else 32)) = 1 := by
  apply EarthScience.mass_fractions_sum (fun _ => (1 / 2 : ℝ))
    (fun i => if i = 0 then (2 : ℝ) else 32)
  · norm_num [Fin.sum_univ_two]
  · norm_num [Fin.sum_univ_two]

/-- The first mass fraction is `1/17`. -/
example :
    ((1 / 2 : ℝ) * (2 : ℝ)) /
      (∑ j : Fin 2, (1 / 2 : ℝ) * (if j = 0 then (2 : ℝ) else 32)) = 1 / 17 := by
  norm_num [Fin.sum_univ_two]

/-- From mass fractions `[1/17, 16/17]`, the mole fraction of species `0` is `1/2`. -/
example :
    ((1 / 17 : ℝ) / (2 : ℝ)) / (∑ j : Fin 2, (if j = 0 then (1 / 17 : ℝ) else 16 / 17) /
      (if j = 0 then (2 : ℝ) else 32)) = 1 / 2 := by
  norm_num [Fin.sum_univ_two]

/-- Recovery: mass fractions computed from those mole fractions give back `1/17`. -/
example :
    (((1 / 17 : ℝ) / (2 : ℝ)) / (∑ j : Fin 2, (if j = 0 then (1 / 17 : ℝ) else 16 / 17) /
      (if j = 0 then (2 : ℝ) else 32)) * (2 : ℝ)) /
      (∑ j : Fin 2, (((if j = 0 then (1 / 17 : ℝ) else 16 / 17) / (if j = 0 then (2 : ℝ) else 32)) /
        (∑ k : Fin 2, (if k = 0 then (1 / 17 : ℝ) else 16 / 17) /
          (if k = 0 then (2 : ℝ) else 32))) * (if j = 0 then (2 : ℝ) else 32)) = 1 / 17 := by
  have h := (EarthScience.mole_fractions_sum_and_recovery
    (fun i : Fin 2 => if i = 0 then (1 / 17 : ℝ) else 16 / 17)
    (fun i : Fin 2 => if i = 0 then (2 : ℝ) else 32)
    (by norm_num [Fin.sum_univ_two])
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two])).2 0
  simpa using h

/-- Boundary case: a single species has mass and mole fraction `1`. -/
example :
    ∑ _i : Fin 1, ((1 : ℝ) * (18 : ℝ)) / (∑ _j : Fin 1, (1 : ℝ) * (18 : ℝ)) = 1 := by
  apply EarthScience.mass_fractions_sum (fun _ => (1 : ℝ)) (fun _ => (18 : ℝ))
  · norm_num [Fin.sum_univ_one]
  · norm_num [Fin.sum_univ_one]
