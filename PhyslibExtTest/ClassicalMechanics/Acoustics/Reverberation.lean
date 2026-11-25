/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.ClassicalMechanics.Acoustics.Reverberation

/-!
# Sabine reverberation checks

Focused checks for
`PhyslibExt.ClassicalMechanics.Acoustics.Reverberation`: for
`V = 100`, `c = 343`, `A_abs = 20`, the decay rate and `T60` are
positive, and the energy at `T60` is `E0 / 10 ^ 6`.

These are elaboration and non-vacuity checks, not new results.
-/

open Acoustics

/-- Positive decay rate and reverberation time for a room. -/
example : 0 < sabineRate 100 343 20 ∧ 0 < sabineT60 100 343 20 :=
  ⟨sabineRate_pos (by norm_num) (by norm_num) (by norm_num),
   sabineT60_pos (by norm_num) (by norm_num) (by norm_num)⟩

/-- Energy at `T60` for `E0 = 2`. -/
example : sabineEnergy 2 (sabineRate 100 343 20)
    (sabineT60 100 343 20) = 2 / 10 ^ 6 :=
  sabine_energy_at_T60 (by norm_num) (by norm_num) (by norm_num)
