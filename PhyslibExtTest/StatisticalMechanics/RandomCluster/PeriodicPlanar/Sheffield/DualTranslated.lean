/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualTranslated

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualTranslated`

* `PeriodicPlanarDualPair.exists_uniformRadius_highProbability_complementaryDualFiniteEvent` with
  `ε = 1/2` and translation invariance discharged by the all-open Dirac mass (proved here); dual
  uniqueness stays a hypothesis.
* `translatedFiniteStripPrimal_dualPairConnection_disjoint` and
  `exists_verticalGap_not_both_translatedFiniteEvents_highProbability` elaborate (check-only).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualTranslated

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

/-- The all-open bond configuration. -/
def allOpen {V : Type*} : ConfigSpace (Sym2 V) := fun _ => true

/-- The Dirac mass on the all-open configuration is translation invariant. -/
theorem allOpen_translationInvariant {V : Type*} [DecidableEq V] (P : PeriodicGraph V) :
    P.IsTranslationInvariant (Measure.dirac allOpen) := fun z =>
  ⟨P.measurable_configTranslate z, by
    rw [Measure.map_dirac' (P.measurable_configTranslate z)]
    rfl⟩

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

-- Uniform high-probability dual connections for the all-open Dirac mass (`ε = 1/2`).
example (D : PeriodicPlanarDualPair P Pdual)
    (hdualUnique : D.dualMeasure (Measure.dirac allOpen)
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :=
  D.exists_uniformRadius_highProbability_complementaryDualFiniteEvent (Measure.dirac allOpen)
    (allOpen_translationInvariant P) hdualUnique (by norm_num : (0 : ℝ) < 1 / 2)

-- `translatedFiniteStripPrimal_dualPairConnection_disjoint` elaborates.
example := @PeriodicPlanarDualPair.translatedFiniteStripPrimal_dualPairConnection_disjoint

-- `exists_verticalGap_not_both_translatedFiniteEvents_highProbability` elaborates.
example :=
  @PeriodicPlanarDualPair.exists_verticalGap_not_both_translatedFiniteEvents_highProbability

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.DualTranslated
