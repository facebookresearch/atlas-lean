/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Dynamics.PolynomialNetworks.Deficiency

/-! # Polynomial networks: an edge from an exponent vector to itself -/

open MathlibExt.Biology.Dynamics.ComplexBalanced

private def loop : ReactionNetwork Unit Unit where
  src := fun _ _ => 2
  prod := fun _ _ => 2

example (k : Unit → ℝ) (x : Unit → ℝ) : loop.massActionField k x = 0 := by
  funext s
  simp [ReactionNetwork.massActionField, loop]

example : loop.IsWeaklyReversible := fun _ => .refl

example : Finite loop.complexes := inferInstance
