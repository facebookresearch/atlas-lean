/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DeepConnectorMeasureClosure

/-!
# Tests for `Sheffield.DeepConnectorMeasureClosure`

Module under test: `Sheffield.DeepConnectorMeasureClosure` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `measure_eq_zero_of_disjoint_measureReal_tendsto_one` on `Bool` with the Dirac mass at `true`,
  the constant events `{true}` and the disjoint set `{false}`.
* `PeriodicPlanarDualPair.FiniteDeepConnectorBandSchedule` and
  `complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules` elaborate
  (check-only; no concrete planar dual pair is available).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace DeepConnectorMeasureClosure

open _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

-- A set disjoint from events of probability one has measure zero.
example : Measure.dirac true ({false} : Set Bool) = 0 :=
  measure_eq_zero_of_disjoint_measureReal_tendsto_one (Measure.dirac true) (fun _ => {true})
    {false} (measurableSet_singleton _) (fun _ => by simp)
    (by simp [Measure.real])

-- `PeriodicPlanarDualPair.FiniteDeepConnectorBandSchedule` elaborates.
example := @PeriodicPlanarDualPair.FiniteDeepConnectorBandSchedule

open PeriodicPlanarDualPair in
example :=
  @complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules

end DeepConnectorMeasureClosure
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
