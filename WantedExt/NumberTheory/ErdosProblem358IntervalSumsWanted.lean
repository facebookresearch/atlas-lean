/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Erdos Problem 358: for an infinite strictly increasing sequence of positive
integers `A = {a_1 < a_2 < ...}`, let `f(n)` be the number of pairs `(u, v)`
with `u ≤ v` such that `Σ_{i=u}^v a_i = n`. Is there a sequence `A` with
`f(n) → ∞` as `n → ∞`?

Note: the source also asks a weaker variant (whether `f(n) ≥ 2` for all
large `n` is attainable); this entry formalizes the lead question only,
`f(n) → ∞`.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Monotone.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem358IntervalSumsWanted

open scoped BigOperators

/-! Source record `EP-358`. -/

/-- **Interval-sum representation count.** For a sequence $a_0, a_1, a_2, \ldots$ of natural
numbers and a natural number $n$, $f_a(n)$ is the number of pairs $(u, v)$ of natural numbers
with $u \le v$ and $a_u + a_{u+1} + \cdots + a_v = n$, and $f_a(n) = 0$ if there are infinitely
many such pairs.

The sequence is indexed from $0$ rather than from $1$ as in the source; this does not change the
count. When the sequence is strictly increasing with positive terms there are only finitely many
such pairs, so $f_a(n)$ is then the true number of representations. -/
noncomputable def RepCount (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card {(p : ℕ × ℕ) | p.1 ≤ p.2 ∧ (∑ i ∈ Finset.Icc p.1 p.2, A i) = n}
/-- **The interval-sum conjecture of Erdős Problem 358.** This is the proposition that there is a
strictly increasing sequence $a_0 < a_1 < a_2 < \cdots$ of positive integers whose interval-sum
representation count $f(n)$, the number of pairs $(u, v)$ of natural numbers with $u \le v$ and
$a_u + a_{u+1} + \cdots + a_v = n$, tends to infinity as $n \to \infty$. -/
def conjecture : Prop :=
  ∃ A : ℕ → ℕ, StrictMono A ∧ 0 < A 0 ∧
    Filter.Tendsto (fun n : ℕ => RepCount A (n : ℕ)) Filter.atTop Filter.atTop

/-- **Interval sums with unbounded representation counts (Erdős Problem 358).** There is a
strictly increasing sequence $a_0 < a_1 < a_2 < \cdots$ of positive integers such that the
number $f(n)$ of pairs $(u, v)$ of natural numbers with $u \le v$ and
$a_u + a_{u+1} + \cdots + a_v = n$ tends to infinity as $n \to \infty$.

Resolved true: Resolved by Tao's February 2026 construction of a set A of positive integers with
f(n) >> log n for all large n, hence f(n) -> infinity (Erdos Problems record 358, [Ta26]).
Source: Terence Tao, construction of a set A of positive integers with f(n) >> log n for Erdos
Problem 358, February 2026,
https://terrytao.wordpress.com/wp-content/uploads/2026/02/erdos-358-2.pdf. Moved from
`OpenConjectures/NumberTheory/ErdosProblem358IntervalSums`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem358IntervalSumsWanted
