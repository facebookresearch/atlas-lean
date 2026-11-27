/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.CycleShannonBoundsMathewOstergard2017LowerBound

/-!
# Signature of the Mathew–Östergård rate bound
-/

open MathlibExt.Combinatorics.Coding.CycleGraphCode
open MathlibExt.Combinatorics.Coding.CycleShannonBoundsWanted

example : ENNReal.rpow 350 ((5 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 :=
  @mathewOstergard2017LowerBound
