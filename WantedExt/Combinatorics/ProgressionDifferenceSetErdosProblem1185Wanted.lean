/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Progressions with common difference in a difference set (Erdős Problem 1185)

Erdős Problem 1185: let `δ > 0` and `k ≥ 3`. Is there `m ≥ 1` (depending only on `δ` and `k`) such
that, for all large `N`, if `A, B ⊆ {1, …, N}` with `|A| ≥ δ N` and `|B| ≥ m`, then `A` contains a
non-trivial `k`-term arithmetic progression whose common difference is in `B - B`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.ProgressionDifferenceSetErdosProblem1185Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1185, https://www.erdosproblems.com/1185 (status
SOLVED). UnsolvedMath record UM-30007226 (`EP-1185`), dataset ulamai/UnsolvedMath v1.8.0.

The question is read for all `δ > 0` and `k ≥ 3`. The common difference is taken positive, which
loses nothing since `B - B` is symmetric and a progression can be reversed. formal-conjectures has
no statement.
-/

open Filter

/-- **Erdős Problem 1185: progressions with difference in a difference set.** This is the
statement that for every real $\delta > 0$ and every natural number $k \ge 3$ there is a natural
number $m \ge 1$ such that for all sufficiently large natural numbers $N$, whenever $A$ and $B$
are subsets of $\{1, \dots, N\}$ with $|A| \ge \delta N$ and $|B| \ge m$, there are natural
numbers $a$ and $d > 0$ such that $b_1 = b_2 + d$ for some $b_1, b_2 \in B$ and $a + i d \in A$
for every natural number $i < k$; that is, $A$ contains the $k$-term arithmetic progression
$a, a + d, \dots, a + (k - 1) d$, whose common difference $d$ is positive and lies in $B - B$. -/
def progressionWithDifferenceInDifferenceSet : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k → ∃ m : ℕ, 1 ≤ m ∧ ∀ᶠ N : ℕ in atTop,
    ∀ A B : Finset ℕ, A ⊆ Finset.Icc 1 N → B ⊆ Finset.Icc 1 N → δ * N ≤ A.card → m ≤ B.card →
      ∃ a d : ℕ, 0 < d ∧ (∃ b₁ ∈ B, ∃ b₂ ∈ B, b₂ + d = b₁) ∧ ∀ i < k, a + i * d ∈ A

/--
**Erdős Problem 1185 is false.** The following statement is false: for every real $\delta > 0$
and every natural number $k \ge 3$ there is a natural number $m \ge 1$ such that for all
sufficiently large natural numbers $N$, whenever $A$ and $B$ are subsets of $\{1, \dots, N\}$
with $|A| \ge \delta N$ and $|B| \ge m$, there are natural numbers $a$ and $d > 0$ such that
$b_1 = b_2 + d$ for some $b_1, b_2 \in B$ and $a + i d \in A$ for every natural number $i < k$.

The answer is negative already for $k = 3$: Furstenberg gave an infinite set $B$ such that
$B - B$ is not $2$-intersective, that is, some set of positive density contains no $3$-term
progression with common difference in $B - B$; truncating both sets at $N$ gives
counterexamples with $|B \cap [1, N]|$ unbounded.

Source: T. F. Bloom, Erdős Problems,
Problem #1185, https://www.erdosproblems.com/1185 (status SOLVED); resolution: H. Furstenberg,
Recurrence in Ergodic Theory and Combinatorial Number Theory, Princeton University Press (1981),
erdosproblems.com/1185: false already at k = 3, since Furstenberg gave an infinite set B such that B
- B is not 2-intersective.
-/
public theorem_wanted progressionWithDifferenceInDifferenceSet_refuted :
    ¬ progressionWithDifferenceInDifferenceSet

end MathlibExt.Combinatorics.ProgressionDifferenceSetErdosProblem1185Wanted
