/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.RectangleMonotonicity

/-!
# Tests for `Sheffield.RectangleMonotonicity`

Module under test: `Sheffield.RectangleMonotonicity` in
`PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar`.

* `PeriodicPlaneEmbedding.rectVertices_mono` for `[1, 2]² ⊆ [0, 3]²`.
* `PeriodicPlaneEmbedding.rectLeftConnectionEvent_mono_otherBounds` enlarging `[0, 1]²` to
  `[0, 2] × [-1, 2]` with the left side fixed.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
namespace RectangleMonotonicity

open _root_.StatMech _root_.StatMech.FK.PeriodicPlanar MeasureTheory Filter

variable {V : Type*} [DecidableEq V] [Countable V] {P : PeriodicGraph V}

-- Vertices of `[1, 2]²` are vertices of `[0, 3]²`.
example (E : PeriodicPlaneEmbedding P) : E.rectVertices 1 2 1 2 ⊆ E.rectVertices 0 3 0 3 :=
  E.rectVertices_mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- Left-side connections persist when the other three sides move outward.
example (E : PeriodicPlaneEmbedding P) (S : Set V) :
    E.rectSideConnectionEvent 0 1 0 1 S (E.rectLeftBoundaryVertices 0 1 0 1) ⊆
      E.rectSideConnectionEvent 0 2 (-1) 2 S (E.rectLeftBoundaryVertices 0 2 (-1) 2) :=
  E.rectLeftConnectionEvent_mono_otherBounds S (by norm_num) (by norm_num) (by norm_num)

end RectangleMonotonicity
end PhyslibExtTest.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield
