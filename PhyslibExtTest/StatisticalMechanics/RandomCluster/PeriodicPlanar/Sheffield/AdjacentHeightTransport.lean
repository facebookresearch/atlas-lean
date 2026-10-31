/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.AdjacentHeightTransport

/-!
# Tests for `Sheffield.AdjacentHeightTransport`

Module under test: `Sheffield.AdjacentHeightTransport` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_transport_tendsto_one` with its `IsFKG`
  and translation-invariance hypotheses discharged by the Dirac mass on the all-open
  configuration (`isFKG_dirac`, `allOpen_translationInvariant`, proved here); the remaining
  geometric and limit hypotheses stay arguments of the specialization.
* The hypothesis set itself, as an explicit non-vacuity example.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace AdjacentHeightTransport

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory

/-- The all-open bond configuration. -/
def allOpen {V : Type*} : ConfigSpace (Sym2 V) := fun _ => true

/-- Every Dirac mass on bond configurations is FKG. -/
theorem isFKG_dirac {V : Type*} (ω : ConfigSpace (Sym2 V)) : IsFKG (Measure.dirac ω) := by
  intro A B hA hB _ _
  rw [Measure.real, Measure.real, Measure.real, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hB, Measure.dirac_apply' _ (hA.inter hB)]
  by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]

/-- The Dirac mass on the all-open configuration is translation invariant. -/
theorem allOpen_translationInvariant {V : Type*} [DecidableEq V] (P : PeriodicGraph V) :
    P.IsTranslationInvariant (Measure.dirac allOpen) := fun z =>
  ⟨P.measurable_configTranslate z, by
    rw [Measure.map_dirac' (P.measurable_configTranslate z)]
    rfl⟩

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- Both hypotheses hold for the all-open Dirac mass (non-vacuity witness).
example : IsFKG (Measure.dirac (allOpen (V := V))) ∧
    P.IsTranslationInvariant (Measure.dirac allOpen) :=
  ⟨isFKG_dirac _, allOpen_translationInvariant P⟩

-- The transport lemma for the all-open Dirac mass.
example (E : PeriodicPlaneEmbedding P) :=
  E.adjacentHeightVerticalCrossing_transport_tendsto_one (Measure.dirac allOpen) (isFKG_dirac _)
    (allOpen_translationInvariant P)

end AdjacentHeightTransport
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
