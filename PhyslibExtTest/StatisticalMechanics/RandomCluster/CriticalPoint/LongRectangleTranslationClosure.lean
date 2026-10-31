/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTranslationClosure

/-!
# Tests for
`PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleTranslationClosure`

* `not_translationClosure_coarseCover_two_one` (with the module's local `Fact (2 < 8)` re-enabled):
  the translation-closure event at `(L, α, n) = (8, 2, 1)` is not covered by thin crossings
  (refutation);
* `bdcTorusThinCrossing_subset_translationClosure` and
  `bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded` on the `3 × 3` torus.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
namespace LongRectangleTranslationClosure

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Lattice _root_.StatMech.RSW.Box
open _root_.StatMech.Universality

instance : Fact (2 < 3) := ⟨by norm_num⟩

attribute [local instance] thinTranslationClosureCounterexample_eightFact

-- The coarse cover by the translation closure fails at `(8, 2, 1)`.
example : ¬ BdcTorusWindingToThinCover 8 2 1
    (bdcTorusThinCrossingTranslationClosureEvent 8 2 1) :=
  not_translationClosure_coarseCover_two_one

-- A thin crossing lies in its translation closure.
example (omega : TorusAmbientConfig 3) (h : bdcTorusThinCrossing 3 1 1 omega) :
    bdcTorusThinCrossingTranslationClosure 3 1 1 omega :=
  bdcTorusThinCrossing_subset_translationClosure 3 1 1 omega h

-- The closure has a finite long-rectangle description.
example (omega : TorusAmbientConfig 3) :=
  bdcTorusThinCrossingTranslationClosure_iff_pullback_mem_finiteExpanded 3 1 1 omega

end LongRectangleTranslationClosure
end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint
