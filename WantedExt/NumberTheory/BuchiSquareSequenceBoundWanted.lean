/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.BuchiSquareSequenceBoundWanted

/-- **Büchi sequences.** Let $M$ be a natural number. A sequence of integers
$u_0, u_1, u_2, \dots$ is a Büchi sequence of length $M$ when the second differences of its
squares equal $2$ along its first $M$ terms, that is,
$u_{j+2}^2 - 2u_{j+1}^2 + u_j^2 = 2$ for every $j$ with $j + 2 < M$.

Only the terms $u_j$ with $j < M$ are constrained. -/
def IsBuchiSequence (M : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j : ℕ, j + 2 < M →
    u (j + 2) ^ 2 - 2 * u (j + 1) ^ 2 + u j ^ 2 = 2

/-- **Trivial sequences in Büchi's problem.** Let $M$ be a natural number. A sequence of
integers $u_0, u_1, u_2, \dots$ is trivial at length $M$ when there is an integer $x$ with
$u_j^2 = (x + j)^2$ for every $j < M$; equivalently, after changing the signs of some of its
terms, its first $M$ terms are the consecutive integers $x, x + 1, \dots, x + M - 1$. -/
def IsTrivial (M : ℕ) (u : ℕ → ℤ) : Prop :=
  ∃ x : ℤ, ∀ j : ℕ, j < M →
    u j ^ 2 = (x + (j : ℤ)) ^ 2

/-- **Büchi's square-sequence conjecture.** There is a natural number $M \ge 5$ such that
every integer Büchi sequence of length $M$ is trivial: for every sequence of integers
$u_0, u_1, u_2, \dots$ with $u_{j+2}^2 - 2u_{j+1}^2 + u_j^2 = 2$ for all $j$ with
$j + 2 < M$, there is an integer $x$ with $u_j^2 = (x + j)^2$ for all $j < M$. -/
def conjecture : Prop :=
  ∃ M : ℕ, 5 ≤ M ∧
    ∀ u : ℕ → ℤ, IsBuchiSequence M u → IsTrivial M u

/--
**Resolution of Büchi's square-sequence conjecture.** There is a natural number $M \ge 5$
such that every integer Büchi sequence of length $M$ is trivial: for every sequence of
integers $u_0, u_1, u_2, \dots$ with $u_{j+2}^2 - 2u_{j+1}^2 + u_j^2 = 2$ for all $j$ with
$j + 2 < M$, there is an integer $x$ with $u_j^2 = (x + j)^2$ for all $j < M$.

Stanley Yao Xiao (arXiv:2412.16740v3, Jun 2025) proves unconditionally that five integer
squares with constant second difference $2$ are consecutive (Theorem 1.3), so the statement
holds with $M = 5$; the earlier length-8 bound was Vojta's conditional result under
Bombieri–Lang.

Source: Stanley Yao Xiao, Hilbert's tenth problem for
systems of diagonal quadratic forms, and Büchi's problem, arXiv:2412.16740v3 (2025),
https://arxiv.org/abs/2412.16740v3. Moved from
`OpenConjectures/NumberTheory/BuchiSquareSequenceBound`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.BuchiSquareSequenceBoundWanted
