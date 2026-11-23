/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The class `S` of normalized univalent functions (Hayman–Lingham Problems 6.9, 6.42, 6.78)

Shared definition for the univalent-function problems of Hayman and Lingham's list: `f` is
holomorphic and injective on the open unit disc with `f 0 = 0` and `f' 0 = 1`. Problem 6.78 uses it
for spherical areas, Problem 6.42 for logarithmic coefficients, Problem 6.9 for Hadamard products.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace MathlibExt.Analysis.UnivalentClassSShared

/-- The class `S`: holomorphic injective functions on the unit disc with `f 0 = 0` and
`f' 0 = 1`. -/
def IsNormalizedUnivalent (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball 0 1) ∧ Set.InjOn f (Metric.ball 0 1) ∧ f 0 = 0 ∧ deriv f 0 = 1

end MathlibExt.Analysis.UnivalentClassSShared
