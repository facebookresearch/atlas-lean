/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Basic

/-!
# Generalized Sylvester sequence

This file defines the generalized Sylvester sequence from
[Y. Kamio, *Asymptotic Analysis of Infinite Decompositions of a Unit Fraction into Unit
Fractions*](https://arxiv.org/abs/2503.02317v1), Definition 2.1.

The paper indexes the sequence from one. Thus `generalizedSylvester n k` is its
`s_{k + 1}(n)`. The definition is extended to every `n : ℕ`; the paper assumes `0 < n`
when proving later properties of the sequence.
-/

@[expose] public section

namespace Nat

/-- **Generalized Sylvester sequence.** For a natural number $n$, the generalized Sylvester sequence
$(s_k(n))_{k \ge 0}$ is the sequence of natural numbers defined by $s_0(n) = n + 1$ and
$s_{k+1}(n) = s_k(n)^2 - s_k(n) + 1$ for $k \ge 0$.

The source indexes the sequence from one: its $s_1(n)$ is $s_0(n)$ here. -/
def generalizedSylvester (n : ℕ) : ℕ → ℕ
  | 0 => n + 1
  | k + 1 => generalizedSylvester n k ^ 2 - generalizedSylvester n k + 1

/-- **Initial term of the generalized Sylvester sequence.** For every natural number $n$, the
generalized Sylvester sequence $(s_k(n))_{k \ge 0}$ satisfies $s_0(n) = n + 1$. -/
@[simp]
theorem generalizedSylvester_zero (n : ℕ) :
    generalizedSylvester n 0 = n + 1 := rfl

/-- **Recurrence for the generalized Sylvester sequence.** For all natural numbers $n$ and $k$, the
generalized Sylvester sequence $(s_k(n))_{k \ge 0}$ satisfies
$s_{k+1}(n) = s_k(n)^2 - s_k(n) + 1$. -/
@[simp]
theorem generalizedSylvester_succ (n k : ℕ) :
    generalizedSylvester n (k + 1) =
      generalizedSylvester n k ^ 2 - generalizedSylvester n k + 1 := rfl

/-- **Positivity of the generalized Sylvester sequence.** For all natural numbers $n$ and $k$, the
term $s_k(n)$ of the generalized Sylvester sequence is positive. -/
theorem generalizedSylvester_pos (n k : ℕ) : 0 < generalizedSylvester n k := by
  cases k <;> simp

end Nat
