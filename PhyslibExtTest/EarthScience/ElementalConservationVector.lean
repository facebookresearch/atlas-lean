/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.ElementalConservationVector

/-!
# Elemental conservation vector checks

Concrete consumers of
`PhyslibExt.EarthScience.ElementalConservationVector`: the two-species
one-reaction conversion, the zero-extent boundary, and the empty system.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
two-species example has the single reaction converting species `0` into
species `1`; the vector `(1, 1)` is a conservation vector, so every
extent leaves the weighted total unchanged.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.ElementalConservationVector`
-/

/-- Two-species conversion: `(1, 1)` annihilates every extent. -/
example (ξ : Fin 1 → ℝ) :
    ∑ i : Fin 2, (1 : ℝ) * (∑ j : Fin 1, (if i = 0 then (-1 : ℝ) else 1) * ξ j) = 0 := by
  apply EarthScience.elemental_conservation_vector_annihilates
    (fun i _ => if i = 0 then (-1 : ℝ) else 1) (fun _ => (1 : ℝ))
  intro j
  norm_num [Fin.sum_univ_two]

/-- Boundary case: zero extent gives zero weighted change. -/
example :
    ∑ i : Fin 2, (1 : ℝ) * (∑ _j : Fin 1, (if i = 0 then (-1 : ℝ) else 1) * (0 : ℝ)) = 0 := by
  apply EarthScience.elemental_conservation_vector_annihilates
    (fun i _ => if i = 0 then (-1 : ℝ) else 1) (fun _ => (1 : ℝ))
  intro j
  norm_num [Fin.sum_univ_two]

/-- Boundary case: the empty species system has weighted change `0`. -/
example (ξ : Fin 1 → ℝ) :
    ∑ _i : Fin 0, (1 : ℝ) * (∑ j : Fin 1, (0 : ℝ) * ξ j) = 0 :=
  EarthScience.elemental_conservation_vector_annihilates
    (fun _ _ => (0 : ℝ)) (fun _ => (1 : ℝ)) (fun j => by simp) ξ
