/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleTranslation

/-!
# Tests for `Sheffield.RectangleTranslation`

Module under test: `Sheffield.RectangleTranslation` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.shift_image_rectVertices` for the translation `(1, 2)` of `[0, 1]²`.
* `PeriodicPlaneEmbedding.rectSideConnectionEvent_translate_measureReal_eq` and
  `rectLeftConnection_translate_measureReal_eq` for the Dirac mass on the all-open configuration
  (translation invariance proved here) and the translation `(1, 2)`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace RectangleTranslation

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

/-- The all-open bond configuration. -/
def allOpen {V : Type*} : ConfigSpace (Sym2 V) := fun _ => true

/-- The Dirac mass on the all-open configuration is translation invariant. -/
theorem allOpen_translationInvariant {V : Type*} [DecidableEq V] (P : PeriodicGraph V) :
    P.IsTranslationInvariant (Measure.dirac allOpen) := fun z =>
  ⟨P.measurable_configTranslate z, by
    rw [Measure.map_dirac' (P.measurable_configTranslate z)]
    rfl⟩

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- Translating `[0, 1]²` by `(1, 2)`.
example (E : PeriodicPlaneEmbedding P) :=
  E.shift_image_rectVertices ![1, 2] 0 1 0 1

-- Side connections have translation-invariant probability.
example (E : PeriodicPlaneEmbedding P) (S side : Set V) :=
  E.rectSideConnectionEvent_translate_measureReal_eq _ (allOpen_translationInvariant P) ![1, 2]
    0 1 0 1 S side

-- Left-side connections have translation-invariant probability.
example (E : PeriodicPlaneEmbedding P) (S : Set V) :=
  E.rectLeftConnection_translate_measureReal_eq _ (allOpen_translationInvariant P) ![1, 2]
    0 1 0 1 S

end RectangleTranslation
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
