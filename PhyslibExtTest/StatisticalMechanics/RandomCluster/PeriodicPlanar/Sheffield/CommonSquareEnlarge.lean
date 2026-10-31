/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.CommonSquareEnlarge

/-!
# Tests for `Sheffield.CommonSquareEnlarge`

Module under test: `Sheffield.CommonSquareEnlarge` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.exists_enlarge` with translation
  invariance discharged by the all-open Dirac mass, enlarging an arbitrary data package by one.
* `exists_commonHalfWidth_connectorReadyData` with both translation-invariance hypotheses
  discharged the same way.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace CommonSquareEnlarge

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

-- Enlarging connector-ready data by one, for the all-open Dirac mass.
example (E : PeriodicPlaneEmbedding P) (radius : ℕ → ℕ)
    (data : E.ConnectorReadyCommonSquareData (Measure.dirac allOpen) radius) :
    ∃ enlarged : E.ConnectorReadyCommonSquareData (Measure.dirac allOpen) radius,
      enlarged.M = fun n => data.M n + 1 :=
  data.exists_enlarge E (allOpen_translationInvariant P) _ fun _ => Nat.le_succ _

-- Primal and dual data with a common half-width, for the all-open Dirac masses.
example (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (radius radiusDual : ℕ → ℕ)
    (primal : E.ConnectorReadyCommonSquareData (Measure.dirac allOpen) radius)
    (dual : Edual.ConnectorReadyCommonSquareData (Measure.dirac allOpen) radiusDual) :=
  exists_commonHalfWidth_connectorReadyData E Edual (allOpen_translationInvariant P)
    (allOpen_translationInvariant Pdual) primal dual

end CommonSquareEnlarge
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
