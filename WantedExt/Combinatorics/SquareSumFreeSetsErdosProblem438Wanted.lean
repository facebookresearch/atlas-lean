/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sets whose sumset avoids the squares (Erdős Problem 438)

Erdős Problem 438: how large can `A ⊆ {1, …, N}` be if `A + A` contains no square numbers?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.SquareSumFreeSetsErdosProblem438Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #438, https://www.erdosproblems.com/438 (status
SOLVED). UnsolvedMath record UM-30006869 (`EP-438`), dataset ulamai/UnsolvedMath v1.8.0.

`A + A` includes the sums `a + a`; excluding them changes the maximum by `O(√N)` only (the `a` with
`2a` a square). The answer is stated as `max |A| / N → 11/32`, the maximum being an `sSup` over a
bounded nonempty set. Compared with the formal-conjectures statement `ErdosProblems/438.lean`
(equivalent; no code imported).
-/

/-- **Square-sum-free sets.** A finite set $A$ of natural numbers is square-sum-free if for all
$a, b \in A$, not necessarily distinct, the sum $a + b$ is not a perfect square. -/
def IsSquareSumFree (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ¬ IsSquare (a + b)

/-- **Maximum size of a square-sum-free set.** For a natural number $N$, the largest size of a set
$A \subseteq \{1, \dots, N\}$ such that no sum $a + b$ with $a, b \in A$, not necessarily distinct,
is a perfect square. -/
noncomputable def maxSquareSumFreeSize (N : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ IsSquareSumFree A ∧ A.card = k}

/-- **Erdős Problem 438 (statement).** For a natural number $N$, let $M(N)$ be the largest size of
a set $A \subseteq \{1, \dots, N\}$ such that no sum $a + b$ with $a, b \in A$, not necessarily
distinct, is a perfect square. This is the statement that $M(N) / N \to 11/32$ as
$N \to \infty$. -/
def maxSquareSumFreeDensity : Prop :=
  Filter.Tendsto (fun N : ℕ => (maxSquareSumFreeSize N : ℝ) / N) Filter.atTop (nhds (11 / 32))

/--
**Maximal density of square-sum-free sets (Erdős Problem 438).** For a natural number $N$, let
$M(N)$ be the largest size of a set $A \subseteq \{1, \dots, N\}$ such that no sum $a + b$ with
$a, b \in A$, not necessarily distinct, is a perfect square. Then $M(N) / N \to 11/32$ as
$N \to \infty$.

Khalfalah, Lodha and Szemerédi proved $M(N) \le (11/32 + o(1)) N$, and Massias's example (the
integers congruent to one of $1, 5, 9, 13, 14, 17, 21, 25, 26, 29, 30$ modulo $32$) gives
$M(N) \ge 11N/32 + O(1)$.

Source: T. F. Bloom, Erdős
Problems, Problem #438, https://www.erdosproblems.com/438 (status SOLVED); resolution: A. Khalfalah,
S. Lodha and E. Szemerédi, Tight bound for the density of sequence of integers the sum of no two of
which is a perfect square, Discrete Math. (2002), 243-255, max |A| ≤ (11/32 + o(1)) N; Massias's
residues mod 32 give the lower bound (erdosproblems.com/438).
-/
public theorem_wanted maxSquareSumFreeDensity_holds : maxSquareSumFreeDensity

end MathlibExt.Combinatorics.SquareSumFreeSetsErdosProblem438Wanted
