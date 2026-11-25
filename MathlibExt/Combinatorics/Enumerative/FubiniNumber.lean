/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MetaMathlibExt

@[expose] public section

open scoped BigOperators

/-- **Fubini numbers.** The Fubini number (ordered Bell number) of a natural number $n$ is
$F(n) = \sum_{k=0}^{n} S(n,k)\, k!$, where $S(n,k)$ is the Stirling number of the second kind.

$F(n)$ counts the weak orderings, equivalently the ordered set partitions, of an $n$-element set.

Source: concept `jis_sem_e1177ff556038d65c81b8a4b`; source statements
`jis_b26251532a8ea8d30aa79dc5` (Fubini numbers count weak orderings of `n`
elements with `n ∈ ℕ₀`), `jis_0874746b31275e17727c6370` (ordered Bell /
Fubini number as the cardinality of set compositions, i.e. ordered set
partitions), `jis_3e6dba4b03dc26402e017ca1`, `jis_5f1e2c9fcad751f6300d9e68`
(Stirling-transform relations between factorials and Fubini numbers). -/
def fubiniNumber : Nat → Nat :=
  fun n => ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * Nat.factorial k

/-- **Fubini numbers as sums of Stirling numbers.** For every natural number $n$, the Fubini
number $F(n)$ equals $\sum_{k=0}^{n} S(n,k)\, k!$, where $S(n,k)$ is the Stirling number of the
second kind.

Source: concept `jis_sem_e1177ff556038d65c81b8a4b`; source statements
`jis_3e6dba4b03dc26402e017ca1`, `jis_5f1e2c9fcad751f6300d9e68`. -/
theorem fubiniNumber_eq_sum (n : Nat) :
    fubiniNumber n =
      ∑ k ∈ Finset.range (n + 1), Nat.stirlingSecond n k * Nat.factorial k :=
  rfl

/-- **Fubini number of zero.** The Fubini number $F(0)$ equals $1$: the empty set has exactly
one weak ordering. -/
@[simp]
theorem fubiniNumber_zero : fubiniNumber 0 = 1 := by decide

/-- **Fubini number of one.** The Fubini number $F(1)$ equals $1$. -/
@[simp]
theorem fubiniNumber_one : fubiniNumber 1 = 1 := by decide

/-- **Fubini number of two.** The Fubini number $F(2)$ equals $3$. -/
theorem fubiniNumber_two : fubiniNumber 2 = 3 := by decide

/-- **Fubini number of three.** The Fubini number $F(3)$ equals $13$.

Source: concept `jis_sem_e1177ff556038d65c81b8a4b`; source statement
`jis_0874746b31275e17727c6370` (the 13 set compositions of a 3-element set). -/
theorem fubiniNumber_three : fubiniNumber 3 = 13 := by decide

end

end MetaMathlibExt
