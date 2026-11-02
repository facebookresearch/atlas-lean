/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Monotone.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

open scoped BigOperators

/-!
# Erdős Problem #884

The full reciprocal divisor-gap sum is bounded by an absolute constant
times `1` plus the consecutive reciprocal divisor-gap sum.
-/

namespace MathlibExt.NumberTheory.ErdosProblem884Wanted

/-- **Divisor-gap sums (Erdős Problem 884).** The statement that there is a real constant $C > 0$
such that for every positive integer $n$, if $d_1 < d_2 < \dots < d_t$ are all the divisors of $n$
in increasing order, then
$\sum_{1 \le i < j \le t} \frac{1}{d_j - d_i} \le
C \left(1 + \sum_{1 \le i < t} \frac{1}{d_{i+1} - d_i}\right)$. -/
def Statement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ t : ℕ, ∀ d : Fin t → ℕ,
    (StrictMono d ∧ (∀ k, d k ∣ n) ∧ ∀ m : ℕ, m ∣ n → ∃ k, d k = m) →
    (∑ i : Fin t, ∑ j : Fin t, if i < j then (1 : ℝ) / (((d j - d i : ℕ) : ℝ)) else 0) ≤
      C * (1 +
        (∑ i : Fin t, ∑ j : Fin t,
          if j.val = i.val + 1 then (1 : ℝ) / (((d j - d i : ℕ) : ℝ)) else 0))

/-- **Erdős Problem 884 is false (Larsen).** For every real constant $C > 0$ there is a positive
integer $n$ whose divisors $d_1 < d_2 < \dots < d_t$, listed in increasing order, satisfy
$\sum_{1 \le i < j \le t} \frac{1}{d_j - d_i} >
C \left(1 + \sum_{1 \le i < t} \frac{1}{d_{i+1} - d_i}\right)$.

Source: Lean proof of the negative answer to Erdős Problem 884,
pinned revision f8a51976fd2e66a52b4928c109fb9ae877a1a507,
https://github.com/Jayyhk/erdos-lean/blob/f8a51976fd2e66a52b4928c109fb9ae877a1a507/problems/884/Erdos884.lean.
Moved from `OpenConjectures/NumberTheory/ErdosProblem884`.
-/
public theorem_wanted Statement_refuted : ¬ Statement

end MathlibExt.NumberTheory.ErdosProblem884Wanted
