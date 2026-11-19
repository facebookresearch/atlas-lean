/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.ScalarShockPorts

/-!
# Tests for `PhyslibExt.FluidDynamics.ScalarShockPorts`

Checked consumers:

- the Burgers front with states `2 | 0` moving at speed `1` conserves mass on `[-1, 1]`;
- the same states with a stationary front do not: the incorrect speed leaves the nonzero
  interface residual `0 * (0 - 2) - (0 ^ 2 / 2 - 2 ^ 2 / 2) = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.FluidDynamics.ScalarShockPorts

open ScalarShock

/-- Burgers flux `u ^ 2 / 2`, states `2 | 0`, front `x = τ` (speed `1`): the mass on `[-1, 1]`
changes at the conservation rate `f 2 - f 0` at time `0`. -/
example :
    HasDerivAt (fun τ : ℝ => (∫ _x in (-1 : ℝ)..τ, (2 : ℝ)) + (∫ _x in τ..(1 : ℝ), (0 : ℝ)))
      ((2 : ℝ) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2) 0 := by
  have key := conservation_iff_rankineHugoniot (f := fun u : ℝ => u ^ 2 / 2)
    (uL := fun _ _ => 2) (uR := fun _ _ => 0) (vL := fun _ _ => 0) (vR := fun _ _ => 0)
    (gL := fun _ => 0) (gR := fun _ => 0) (s := fun τ => τ) (c := 1) (a := -1) (b := 1)
    (t := 0) (UL := Set.univ) (UR := Set.univ) (hasDerivAt_id' 0)
    (by norm_num) (by norm_num) isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
    isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
  exact key.mpr (by norm_num)

/-- The same states with a stationary front (speed `0`) do not conserve mass on `[-1, 1]`: the
Rankine-Hugoniot identity `0 * (0 - 2) = 0 ^ 2 / 2 - 2 ^ 2 / 2` fails. -/
example :
    ¬ HasDerivAt
      (fun _τ : ℝ => (∫ _x in (-1 : ℝ)..(0 : ℝ), (2 : ℝ)) + (∫ _x in (0 : ℝ)..(1 : ℝ), (0 : ℝ)))
      ((2 : ℝ) ^ 2 / 2 - (0 : ℝ) ^ 2 / 2) 0 := by
  have key := conservation_iff_rankineHugoniot (f := fun u : ℝ => u ^ 2 / 2)
    (uL := fun _ _ => 2) (uR := fun _ _ => 0) (vL := fun _ _ => 0) (vR := fun _ _ => 0)
    (gL := fun _ => 0) (gR := fun _ => 0) (s := fun _ => 0) (c := 0) (a := -1) (b := 1)
    (t := 0) (UL := Set.univ) (UR := Set.univ) (hasDerivAt_const 0 0)
    (by norm_num) (by norm_num) isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
    isOpen_univ (Set.subset_univ _) continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) continuousOn_const continuousOn_const
    (fun _ _ => hasDerivAt_const _ _) (fun _ _ => by simp)
  intro h
  have hRH := key.mp h
  norm_num at hRH

end PhyslibExtTest.FluidDynamics.ScalarShockPorts
