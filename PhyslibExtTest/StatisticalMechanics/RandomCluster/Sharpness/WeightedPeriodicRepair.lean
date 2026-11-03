/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodicRepair

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodicRepair`

For the homogeneous coupling `J = 1` with one phase on `ℤ²`, box radius `5`, `q = 2`, `β = 1`:
* `weightedPhaseOffCentreStrict_of_covariant`: strict off-centre domination holds;
* `periodicWeightedNestedDominationStrict_of_covariant`: strict nested domination holds;
* the domination specialized at the origin and radius `k = 2`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodicRepair

open _root_.StatMech _root_.StatMech.OSSS
open Lattice FK RevealmentConstruction RevealmentTranslation
open WiredBoxDifferential WiredBoxLocalized WiredBoxOffCentre
open FKSharpnessWeightedPeriodic FKSharpnessWeightedDomain FKSharpnessWeightedPeriodicRepair

/-- The homogeneous one-phase coupling on `ℤ^d`. -/
def unitJ (d : ℕ) : Unit → Sym2 (Site d) → ℝ := fun _ _ => 1

/-- The homogeneous coupling with one phase is phase-covariant. -/
theorem unit_phaseCovariant (d : ℕ) :
    PhaseCovariant (fun _ : Sym2 (Site d) => (1 : ℝ)) (fun _ => ()) (unitJ d) :=
  fun _ _ => rfl

-- Strict off-centre domination holds for the homogeneous coupling (`d = 2`, `n = 5`).
example : WeightedPhaseOffCentreStrict 2 5 (fun _ => 1) (fun _ => ())
    (fun a => weightedPhaseWiredTheta 2 (unitJ 2) a 2 1) 2 1 :=
  weightedPhaseOffCentreStrict_of_covariant 2 5 _ (fun _ => one_pos) _ _ (unit_phaseCovariant 2) 2
    1 (by norm_num) one_pos

-- Strict nested domination holds for the homogeneous coupling.
example : PeriodicWeightedNestedDominationStrict 2 5 (fun _ => 1) (fun _ => ()) (unitJ 2) 2 1 :=
  periodicWeightedNestedDominationStrict_of_covariant 2 5 _ (fun _ => one_pos) _ _
    (unit_phaseCovariant 2) 2 1 (by norm_num) one_pos

-- Unfolding strict domination at the origin and `k = 2` (`2 * 2 < 5`).
example : weightedOuterInnerConn 2 5 (fun _ => 1) 2 1 0 2 ≤
    weightedPhaseWiredTheta 2 (unitJ 2) () 2 1 2 :=
  weightedPhaseOffCentreStrict_of_covariant 2 5 _ (fun _ => one_pos) _ _ (unit_phaseCovariant 2) 2
    1 (by norm_num) one_pos 0 (by simp [Percolation.mem_boxFinset]) 2 (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodicRepair
