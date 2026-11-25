/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.FurstenbergTopological
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order

namespace MathlibExt.Dynamics.FurstenbergTopologicalTest

open Filter Function Topology
open FurstenbergTopologicalWanted.Dynamics

example : ∃ x : PUnit, IsMultiplyRecurrent (Homeomorph.refl PUnit : PUnit → PUnit) x :=
  furstenberg_topological_recurrence (T := Homeomorph.refl PUnit)

-- Both points in a two-cycle return at the same sequence of even times for every power.
example (x : Bool) : IsMultiplyRecurrent Bool.not x := by
  intro d hd
  refine ⟨fun k => 2 * (k + 1), strictMono_nat_of_lt_succ (fun k => by omega), ?_⟩
  intro j hj hjd
  have hperiod : Bool.not^[2] = id := by
    funext y
    cases y <;> rfl
  have hreturn (k : ℕ) : Bool.not^[j * (2 * (k + 1))] x = x := by
    rw [show j * (2 * (k + 1)) = 2 * (j * (k + 1)) by ac_rfl,
      iterate_mul, hperiod, iterate_id]
    rfl
  simpa only [hreturn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

end MathlibExt.Dynamics.FurstenbergTopologicalTest
