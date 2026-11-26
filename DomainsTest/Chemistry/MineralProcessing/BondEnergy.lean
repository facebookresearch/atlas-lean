/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.MineralProcessing.BondEnergy
import Mathlib.Tactic.NormNum

open Domains.Chemistry.MineralProcessing.BondEnergy

-- Equality of sizes lies on the nonnegative side of the sign criterion.
example : (0 : ℝ) ≤ 10 * 1 * (1 / Real.sqrt 4 - 1 / Real.sqrt 4) :=
  (bond_energy_identities 1 4 9 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1.2 le_rfl

-- The stipulated equation is negative when the product size is larger.
example : ¬ ((0 : ℝ) ≤ 10 * 1 * (1 / Real.sqrt 4 - 1 / Real.sqrt 1)) := by
  intro h
  have hle :=
    (bond_energy_identities 1 1 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1.1 h
  norm_num at hle
