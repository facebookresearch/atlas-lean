/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.BoxDownCompressionCounterexample

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.BoxDownCompressionCounterexample`

* The two disjoint-occurrence events are computed (`bdc2_box_AB`, `bdc2_box_compressed`) and the
  refutation `¬ rit_BoxDownCompMono (Fin 2)` is restated.
-/

@[expose] public section

open StatMech

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.BoxDownCompressionCounterexample

example : disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_B)
    = ({bdc2_FF, bdc2_TF} : Set (ConfigSpace (Fin 2))) := bdc2_box_AB

example : disjointOccurrence (familyEvent bdc2_A) (familyEvent bdc2_A)
    = ({bdc2_FF} : Set (ConfigSpace (Fin 2))) := bdc2_box_compressed

example : ¬ rit_BoxDownCompMono (Fin 2) := bdc2_boxDownCompMono_fin2_false

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.BoxDownCompressionCounterexample
