/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.Universality.CrossingTranslationInvariance

/-!
# Tests for `MathlibExt.Probability.Percolation.Universality.CrossingTranslationInvariance`

* `translateConfig v` preserves `ℙ_{1/2}`; crossing probabilities of `[0, 2] × [0, 1]` and of its
  translate by `(3, -1)` agree.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal ENNReal
open StatMech StatMech.Lattice StatMech.Universality
open StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.Universality.CrossingTranslationInvariance

example : MeasurePreserving (translateConfig ![3, -1]) halfMeasure halfMeasure :=
  cti_selfDual_shift_invariant _

example : halfMeasure.real (horizontalCrossingEvent (0 + (![3, -1] : Site 2) 0)
      (2 + (![3, -1] : Site 2) 0) (0 + (![3, -1] : Site 2) 1) (1 + (![3, -1] : Site 2) 1))
    = halfMeasure.real (horizontalCrossingEvent 0 2 0 1) :=
  cti_horizontalCrossing_translation_invariant 0 2 0 1 _
    (measurableSet_horizontalCrossingEvent 0 2 0 1)

end MathlibExtTest.StatMech.Probability.Percolation.Universality.CrossingTranslationInvariance
