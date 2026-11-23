/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Right-down diagonal sequences

This file formalizes the recurrence in László Németh and László Szalay,
*Sequences Involving Square Zig-Zag Shapes*, Journal of Integer Sequences 24
(2021), Article 21.5.2.
-/

open scoped BigOperators

namespace MetaMathlibExt

@[expose]
public section

/-- **Right-down diagonal coefficient.** For natural numbers $k$ and $i$, the coefficient
$c_k(i)$ of the right-down diagonal recurrence is the integer $(-1)^i \binom{k+1-i}{i+1}$ when
$i \le k+1$, and $0$ when $i > k+1$. -/
def rightDownDiagonalCoefficient (k i : ℕ) : ℤ :=
  (-1) ^ i * Nat.choose (k + 1 - i) (i + 1)

/-- **Right-down diagonal families of order $k$.** For a natural number $k$, a family
$(A_j)_{0 \le j \le k+1}$ of integer sequences $A_j : \mathbb{N} \to \mathbb{Z}$ is a family of
right-down diagonal sequences of order $k$ when $k \ge 1$ and, for every $j$ and every natural
number $n \ge \lfloor k/2 \rfloor + 1$,
$$A_j(n) = \sum_{i=0}^{\lfloor k/2 \rfloor} c_k(i)\, A_j(n-1-i),$$
where $c_k(i) = (-1)^i \binom{k+1-i}{i+1}$ is the right-down diagonal coefficient.

Source: László Németh and László Szalay, *Sequences Involving Square Zig-Zag Shapes*, Journal
of Integer Sequences 24 (2021), Article 21.5.2. Stable source identifiers: concept
`jis_sem_81073f165e7dac1ef20a1a7a`, statement `jis_0034612dbd4f4faf5fca455c`.
-/
def IsRightDownDiagonalFamily (k : ℕ) (A : Fin (k + 2) → ℕ → ℤ) : Prop :=
  1 ≤ k ∧ ∀ j n, k / 2 + 1 ≤ n →
    A j n = ∑ i ∈ Finset.range (k / 2 + 1),
      rightDownDiagonalCoefficient k i * A j (n - 1 - i)

end

end MetaMathlibExt
