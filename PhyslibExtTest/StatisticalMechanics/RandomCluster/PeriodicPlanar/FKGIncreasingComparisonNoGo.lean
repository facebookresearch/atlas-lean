/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.FKGIncreasingComparisonNoGo

/-!
# Tests for
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.FKGIncreasingComparisonNoGo`

* `isFKG_dirac` at the all-open configuration on `Fin 3`;
* the counterexample Dirac mass gives the certain event mass `1` and the edge-open event mass `0`,
  so the comparison `μ.real A ≤ μ.real B` fails for it;
* the library refutation `not_fkg_implies_increasing_event_orientation_comparison` applied.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar
namespace FKGIncreasingComparisonNoGo

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

-- A Dirac mass at the all-open configuration is FKG.
example : IsFKG (Measure.dirac (fun _ => true : ConfigSpace (Sym2 (Fin 3)))) :=
  isFKG_dirac _

-- The counterexample violates the comparison of the certain and the edge-open events.
example : ¬ (Measure.dirac fkgComparisonCounterexampleConfig).real fkgComparisonCertainEvent ≤
    (Measure.dirac fkgComparisonCounterexampleConfig).real fkgComparisonEdgeOpenEvent := by
  rw [aspectOrientationCertainEvent_measureReal, aspectOrientationAbsentEvent_measureReal]
  norm_num

-- The library refutation, specialized to `A = univ`, `B = {ω | ω s(0, 1)}` is impossible.
example : ¬ (∀ (mu : Measure (ConfigSpace (Sym2 (Fin 2)))), IsFKG mu →
      ∀ A B : Set (ConfigSpace (Sym2 (Fin 2))),
        MeasurableSet A → MeasurableSet B → IsIncreasing A → IsIncreasing B →
        mu.real A ≤ mu.real B) :=
  not_fkg_implies_increasing_event_orientation_comparison

end FKGIncreasingComparisonNoGo
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar
