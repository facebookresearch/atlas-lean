/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card

/-!
# Sum-free finite sets of natural numbers

This module defines the sum-free predicate for finite subsets of the natural numbers.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted

/-- **Sum-free sets of natural numbers.** A finite set $S$ of natural numbers is sum-free if
$x + y \notin S$ for all $x, y \in S$, where $x = y$ is allowed.

Source: [GREEN-001]. -/
def IsSumFree (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x + y ∉ s

end MathlibExt.Combinatorics.GreenProblem1LargeSumFreeWanted
