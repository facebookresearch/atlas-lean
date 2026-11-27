/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import MathlibExt.Combinatorics.Enumerative.Hypersequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import MathlibExt.Combinatorics.Enumerative.HypersequenceRecurrence

/-! # Abel summation by parts for hypersequences -/

namespace MetaMathlibExt

open Finset

/-- **Abel summation by parts.** Let $a$ and $b$ be sequences of complex numbers and let
$a^{(1)}_k = \sum_{i=0}^{k} a_i$ be the first hypersequence (the partial sums) of $a$. Then for
every natural number $n$,
$$\sum_{k=0}^{n} a_k b_k = a^{(1)}_n b_{n+1} + \sum_{k=0}^{n} a^{(1)}_k (b_k - b_{k+1}).$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Theorem 7 (`integers-2024-A70-thm-7`). -/
public theorem sum_mul_eq_hypersequence_one_mul_add_sum (a b : ℕ → ℂ) (n : ℕ) :
    ∑ k ∈ range (n + 1), a k * b k =
      hypersequence a 1 n * b (n + 1) +
        ∑ k ∈ range (n + 1), hypersequence a 1 k * (b k - b (k + 1)) := by
  induction n with
  | zero =>
    simp only [Nat.zero_add, sum_range_one, hypersequence_one_zero]
    ring
  | succ n ih =>
    have hnext : hypersequence a 1 (n + 1) = hypersequence a 1 n + a (n + 1) :=
      hypersequence_succ_succ a 0 n
    simp only [sum_range_succ _ (n + 1)]
    rw [ih, hnext]
    ring

end MetaMathlibExt
