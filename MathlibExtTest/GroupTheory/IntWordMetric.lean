/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.IntWordMetric

@[expose] public section

namespace MathlibExtTest.IntWordMetric

open Group.Generators

example : intGenerators.wordLength (Multiplicative.ofAdd (-7 : ℤ)) = 7 := by
  rw [wordLength_intGenerators]; rfl

example : intGenerators.wordLength (Multiplicative.ofAdd (0 : ℤ)) = 0 := by
  rw [wordLength_intGenerators]; rfl

end MathlibExtTest.IntWordMetric
