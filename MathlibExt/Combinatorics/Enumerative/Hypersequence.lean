/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Hypersequences

The hypersequence of generation `r` of a sequence `a` iterates partial sums: `a^{(0)}_n = a_n`
and `a^{(r+1)}_n = ∑_{k=0}^{n} a^{(r)}_k`. This module defines `hypersequence` and proves its
defining recursion `hypersequence_succ` and the first value `hypersequence_one_zero`.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Hypersequence.** Let $(a_n)_{n \ge 0}$ be a sequence in an additive commutative monoid.
Its hypersequence of generation $r$, written $a^{(r)}_n$, is defined by recursion on $r$:
$a^{(0)}_n = a_n$ and $a^{(r+1)}_n = \sum_{k=0}^{n} a^{(r)}_k$ for all natural numbers $r$ and
$n$. Thus each generation is the sequence of partial sums of the previous one.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public def hypersequence {R : Type*} [AddCommMonoid R] (a : ℕ → R) : ℕ → ℕ → R
  | 0, n => a n
  | r + 1, n => ∑ k ∈ range (n + 1), hypersequence a r k

/-- **Each hypersequence generation sums the previous one.** Let $(a_n)$ be a sequence in an
additive commutative monoid and let $a^{(r)}_n$ denote its hypersequence of generation $r$. For
all natural numbers $r$ and $n$, $a^{(r+1)}_n = \sum_{k=0}^{n} a^{(r)}_k$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public theorem hypersequence_succ {R : Type*} [AddCommMonoid R] (a : ℕ → R) (r n : ℕ) :
    hypersequence a (r + 1) n = ∑ k ∈ range (n + 1), hypersequence a r k :=
  rfl

/-- **First hypersequence at index zero.** Let $(a_n)$ be a sequence in an additive commutative
monoid and let $a^{(1)}_n$ denote its hypersequence of generation $1$. Then $a^{(1)}_0 = a_0$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums*,
INTEGERS 24 (2024), Article A70, Section 1, Equation (1.1). -/
public theorem hypersequence_one_zero {R : Type*} [AddCommMonoid R] (a : ℕ → R) :
    hypersequence a 1 0 = a 0 := by
  simp [hypersequence]

end

end MetaMathlibExt
