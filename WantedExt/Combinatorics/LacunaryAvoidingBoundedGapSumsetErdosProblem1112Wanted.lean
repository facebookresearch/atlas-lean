/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bounded-gap sequences whose triple sums avoid a lacunary sequence (Erdős Problem 1112)

Erdős Problem 1112: let `1 ≤ d₁ < d₂` and `k ≥ 3`. Does there exist an integer `r` such that if `B
= {b₁ < ⋯}` is a lacunary sequence of positive integers with `b_{i+1} ≥ r b_i` then there exists a
sequence of positive integers `A = {a₁ < ⋯}` such that `d₁ ≤ a_{i+1} - a_i ≤ d₂` for all `i ≥ 1`
and `(kA) ∩ B = ∅`, where `kA` is the `k`-fold sumset?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace MathlibExt.Combinatorics.LacunaryAvoidingBoundedGapSumsetErdosProblem1112Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1112, https://www.erdosproblems.com/1112 (status
OPEN (LEAN)). UnsolvedMath record UM-00002499 (`EP-1112`), dataset ulamai/UnsolvedMath v1.8.0.

The statement is the page's interpretation of a remark of Erdős and Graham, who asked whether
their `A + A` result can hold for `A + A + A`. The page writes `r_k(d₁, d₂)` for the least `r`
that works (if any), records that `r₃(2, 3)` does not exist (Bollobás, Hegyvári and Jin, 'a
negative answer'), and keeps the problem open because the existence of `r_k(a, b)` for other
parameters with `k ≥ 3` is unknown, with no conjectured answer. This module states the settled
case `d₁ = 2`, `d₂ = 3`, `k = 3`. Sequences are indexed from `0`; `b` is strictly increasing and
positive with `r b_i ≤ b_{i+1}`, `a` is positive with gaps in `[d₁, d₂]` (written without
truncated subtraction), and `kA` is the `k`-fold sumset `k • Set.range a` (Mathlib's pointwise
`ℕ`-action on sets is repeated addition). formal-conjectures has no statement of this problem.
-/

open scoped Pointwise

/-- **Lacunary threshold for bounded-gap sumsets.** For natural numbers $d_1$, $d_2$ and $k$,
the threshold $r_k(d_1, d_2)$ of Erdős Problem 1112 exists when there is a natural number $r$
such that for every strictly increasing sequence $b_0 < b_1 < \cdots$ of positive integers with
$b_{i+1} \ge r b_i$ for all $i$, there is a sequence $a_0, a_1, \dots$ of positive integers with
$a_i + d_1 \le a_{i+1} \le a_i + d_2$ for all $i$ such that no $b_i$ lies in the $k$-fold sumset
of $A = \{a_0, a_1, \dots\}$, the set of all sums of $k$ elements of $A$ with repetition allowed
(for $k = 0$ this set is $\{0\}$). -/
def HasLacunaryThreshold (d₁ d₂ k : ℕ) : Prop :=
  ∃ r : ℕ, ∀ b : ℕ → ℕ, 0 < b 0 → StrictMono b → (∀ i, r * b i ≤ b (i + 1)) →
    ∃ a : ℕ → ℕ, 0 < a 0 ∧ (∀ i, a i + d₁ ≤ a (i + 1) ∧ a (i + 1) ≤ a i + d₂) ∧
      Disjoint (k • Set.range a) (Set.range b)

/-- **Statement of Erdős Problem 1112 for gaps in $[2, 3]$ and triple sums.** The threshold
$r_3(2, 3)$ exists: there is a natural number $r$ such that for every strictly increasing
sequence $b_0 < b_1 < \cdots$ of positive integers with $b_{i+1} \ge r b_i$ for all $i$, there is
a sequence $a_0, a_1, \dots$ of positive integers with $a_i + 2 \le a_{i+1} \le a_i + 3$ for all
$i$ such that no $b_i$ is a sum $x + y + z$ of three, not necessarily distinct, terms $x, y, z$
of the sequence $a$. -/
def lacunaryThresholdGapsTwoThreeThreeFold : Prop :=
  HasLacunaryThreshold 2 3 3

/--
**Bollobás–Hegyvári–Jin theorem on Erdős Problem 1112.** There is no natural number $r$ such
that for every strictly increasing sequence $b_0 < b_1 < \cdots$ of positive integers with
$b_{i+1} \ge r b_i$ for all $i$, there is a sequence $a_0, a_1, \dots$ of positive integers with
$a_i + 2 \le a_{i+1} \le a_i + 3$ for all $i$ such that no $b_i$ is a sum of three, not
necessarily distinct, terms of the sequence $a$. In other words, the threshold $r_3(2, 3)$ of
Erdős Problem 1112 (gaps between $2$ and $3$, triple sums) does not exist.

Source: T. F.
Bloom, Erdős Problems, Problem #1112, https://www.erdosproblems.com/1112 (status OPEN (LEAN));
resolution: B. Bollobás, N. Hegyvári and G. Jin, On a problem of Erdős and Graham, Discrete Math.
175 (1997), 253-257, main result (Theorem 3 of the paper), as recorded on erdosproblems.com/1112:
for any integers 1 ≤ r₁ < r₂ < ⋯ there is a B with b_{i+1} ≥ r_i b_i such that (A + A + A) ∩ B ≠ ∅
for every A with 2 ≤ a_{i+1} - a_i ≤ 3; erdosproblems.com/1112: 'It follows from the above results
that r₂(2, 3) = 2 and that r₃(2, 3) does not exist',
https://doi.org/10.1016/S0012-365X(96)00122-7.
-/
public theorem_wanted lacunaryThresholdGapsTwoThreeThreeFold_refuted :
    ¬ lacunaryThresholdGapsTwoThreeThreeFold

end MathlibExt.Combinatorics.LacunaryAvoidingBoundedGapSumsetErdosProblem1112Wanted
