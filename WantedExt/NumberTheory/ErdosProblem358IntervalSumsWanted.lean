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

/-- Number of interval representations of `n` as a consecutive sum of `A`.

The sequence is indexed from `0` rather than the source's `1`-based
`a_1 < a_2 < ...`; this shift is harmless since only the ordered values
and interval sums matter.

`Nat.card` of a set is junk-but-total: it returns `0` when the solution
set is infinite. Finiteness gap (not formalized): for a strictly
increasing sequence of positive integers the solution set is in fact
finite, so `RepCount` agrees with the true count on all admissible
inputs. -/
noncomputable def RepCount (A : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.card {(p : ℕ × ℕ) | p.1 ≤ p.2 ∧ (∑ i ∈ Finset.Icc p.1 p.2, A i) = n}
/-- [EP-358] There exists an infinite strictly increasing sequence of positive
integers whose interval-sum representation count tends to infinity. -/
def conjecture : Prop :=
  ∃ A : ℕ → ℕ, StrictMono A ∧ 0 < A 0 ∧
    Filter.Tendsto (fun n : ℕ => RepCount A (n : ℕ)) Filter.atTop Filter.atTop

/--
Resolved true: Resolved by Tao's February 2026 construction of a set A of positive integers with
f(n) >> log n for all large n, hence f(n) -> infinity (Erdos Problems record 358, [Ta26]).
Source: Terence Tao, construction of a set A of positive integers with f(n) >> log n for Erdos
Problem 358, February 2026,
https://terrytao.wordpress.com/wp-content/uploads/2026/02/erdos-358-2.pdf. Moved from
`OpenConjectures/NumberTheory/ErdosProblem358IntervalSums`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem358IntervalSumsWanted
