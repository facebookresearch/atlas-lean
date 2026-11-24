/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

/-!
# Finite probability vectors

The lightweight predicate for a probability vector on a finite type,
shared by modules that need only the predicate (such as
expectation-maximization) without the coupling and transport API of
`MathlibExt.Probability.FiniteTransport`, which re-exports it.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace MathlibExt.Probability.FiniteDist

/-- A probability vector on a finite type: nonnegative entries summing to 1. -/
def IsDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

end MathlibExt.Probability.FiniteDist
