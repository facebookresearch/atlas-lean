/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.CycleShannonBoundsLovasz1979UpperBound
import MathlibExt.Combinatorics.Coding.CycleShannonBounds
import MathlibExt.Combinatorics.Coding.PolakSchrijver

namespace MathlibExtTest.Combinatorics.Coding.CycleShannonBoundsLovasz1979UpperBound

open MathlibExt.Combinatorics.Coding.CycleGraphCode
open MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

example : ENNReal.rpow 343 ((5 : ℝ)⁻¹) ≤ lovaszThetaCycleSeven :=
  le_trans bmrrst1971LowerBound lovasz1979UpperBound

example : ENNReal.rpow 367 ((5 : ℝ)⁻¹) ≤ lovaszThetaCycleSeven :=
  le_trans polakSchrijverRateLowerBound lovasz1979UpperBound

example (n : PositiveNat) (A : CycleCode 7 n.1) :
    cycleCodeRate 7 n A ≤ lovaszThetaCycleSeven :=
  le_trans (cycleCodeRate_le_shannonCapacity 7 n A) lovasz1979UpperBound

end MathlibExtTest.Combinatorics.Coding.CycleShannonBoundsLovasz1979UpperBound
