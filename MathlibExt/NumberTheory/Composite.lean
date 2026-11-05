/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# Composite natural numbers

A shared predicate for natural numbers greater than one that are not prime.
-/

@[expose] public section

namespace Nat

/-- **Composite numbers.** A natural number $n$ is composite if $n > 1$ and $n$ is not prime. -/
def IsComposite (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime

/-- **Composite numbers exceed one.** Every composite natural number $n$ satisfies $1 < n$. -/
theorem IsComposite.one_lt {n : ℕ} (h : n.IsComposite) : 1 < n :=
  h.1

/-- A composite natural number is not prime. -/
theorem IsComposite.not_prime {n : ℕ} (h : n.IsComposite) : ¬ n.Prime :=
  h.2

end Nat
