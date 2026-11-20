/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































import Mathlib
import Code.Lattice.TurningNumber
import Code.Lattice.DartOrbit

open SimpleGraph Function

namespace StatMech.Walls

open StatMech.Lattice











theorem jwd_step_turn_le_one (K : Set (Site 2)) (e : Dart) : |turnZ K e| ≤ 1 :=
  abs_turnZ_le_one K e



theorem jwd_step_turn_mem (K : Set (Site 2)) (e : Dart) :
    turnZ K e = 1 ∨ turnZ K e = 0 ∨ turnZ K e = -1 :=
  turnZ_mem K e











theorem jwd_totalTurn_le_steps (K : Set (Site 2)) (e : Dart) (p : ℕ) :
    |totalTurnZ K e p| ≤ (p : ℤ) :=
  abs_totalTurnZ_le K e p























theorem jwd_turn_period_bound (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) :=
  abs_orbit_totalTurnZ_le K a













theorem jwd_turn_period_bound_explicit (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) := by
  set p := dartOrbitPeriod K a with hp
  unfold totalTurnZ
  calc |∑ i ∈ Finset.range p, turnZ K ((dartNext K)^[i] a.1)|
      ≤ ∑ i ∈ Finset.range p, |turnZ K ((dartNext K)^[i] a.1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range p, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => jwd_step_turn_le_one K _)
    _ = (p : ℤ) := by simp













theorem jwd_turn_bracketed (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) :
    (4 : ℤ) ∣ totalTurnZ K a.1 (dartOrbitPeriod K a) ∧
      |totalTurnZ K a.1 (dartOrbitPeriod K a)| ≤ (dartOrbitPeriod K a : ℤ) :=
  ⟨four_dvd_orbit_totalTurnZ K a, jwd_turn_period_bound K a⟩

end StatMech.Walls
