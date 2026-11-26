/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectanglePreference

/-!
# Tests for `Sheffield.RectanglePreference`

Module under test: `Sheffield.RectanglePreference` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.rectSideConnectionEvent` and `rectanglePairMergeErrorUnion` are events
  for the unit square.
* `PeriodicPlaneEmbedding.verticalCrossing_measureReal_ge_side_mul_sub_mergeError` and
  `verticalCrossing_ge_preferredSide_transfer` for the Dirac mass on the all-open configuration,
  which is FKG (`isFKG_dirac`, proved here), on the unit square.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace RectanglePreference

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

/-- The all-open bond configuration. -/
def allOpen {V : Type*} : ConfigSpace (Sym2 V) := fun _ => true

/-- Every Dirac mass on bond configurations is FKG. -/
theorem isFKG_dirac {V : Type*} (ω : ConfigSpace (Sym2 V)) : IsFKG (Measure.dirac ω) := by
  intro A B hA hB _ _
  rw [Measure.real, Measure.real, Measure.real, Measure.dirac_apply' _ hA,
    Measure.dirac_apply' _ hB, Measure.dirac_apply' _ (hA.inter hB)]
  by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;> simp [hωA, hωB]

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- Side-connection and merge-error events of the unit square.
example (E : PeriodicPlaneEmbedding P) (S side : Set V) (L R : Finset V) :
    Set (ConfigSpace (Sym2 V)) × Set (ConfigSpace (Sym2 V)) :=
  (E.rectSideConnectionEvent 0 1 0 1 S side, E.rectanglePairMergeErrorUnion 0 1 0 1 L R)

-- The FKG lower bound on vertical crossings of the unit square.
example (E : PeriodicPlaneEmbedding P) (L R : Finset V) :=
  E.verticalCrossing_measureReal_ge_side_mul_sub_mergeError (Measure.dirac allOpen)
    (isFKG_dirac _) 0 1 0 1 L R

-- The preferred-side transfer on the unit square.
example (E : PeriodicPlaneEmbedding P) (L R : Finset V) :=
  E.verticalCrossing_ge_preferredSide_transfer (Measure.dirac allOpen) (isFKG_dirac _) 0 1 0 1 L R

end RectanglePreference
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
