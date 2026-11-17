/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

import PhyslibExt.ClassicalMechanics.Acoustics.Transmission

/-!
# Acoustic transmission checks

Focused checks for `PhyslibExt.ClassicalMechanics.Acoustics.Transmission`:
two equal-area patches with coefficients `1 / 2` and `1` under uniform
intensity give effective coefficient `3 / 4`, within `(0, 1]`.

These are elaboration and non-vacuity checks, not new results.
-/

open Acoustics

/-- Equal-area two-patch average, through the public theorems. -/
example : effectivePowerTransmission (fun _ : Fin 2 => (1 : ℝ))
      (fun _ : Fin 2 => (1 : ℝ)) ![1 / 2, 1] Finset.univ = 3 / 4 := by
  rw [effectivePowerTransmission_eq_of_uniform _ _ _ _
    (show (0 : ℝ) < 1 by norm_num) (fun i _ => rfl)
    (fun i _ => by norm_num) Finset.univ_nonempty]
  norm_num [Fin.sum_univ_two]
