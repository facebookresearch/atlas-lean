/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.HyperbolicGroupExamples
public import MathlibExt.GroupTheory.GroupGrowthGenerators
public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Defs

@[expose] public section

namespace MathlibExtTest.HyperbolicGroupExamples

open Group Group.Generators

/-- Non-degenerate instances of the hypotheses of the wanted theorems on hyperbolic groups and
groups of polynomial growth: an infinite cyclic group and a nontrivial finite group. -/
example : IsHyperbolic (Multiplicative ℤ) := isHyperbolic_multiplicative_int

example : IsHyperbolic (Multiplicative (ZMod 3)) := IsHyperbolic.of_finite _

example : intGenerators.HasPolynomialGrowth := hasPolynomialGrowth_intGenerators

example : (Multiplicative.ofAdd (5 : ℤ)) ≠ 1 := by decide

end MathlibExtTest.HyperbolicGroupExamples
