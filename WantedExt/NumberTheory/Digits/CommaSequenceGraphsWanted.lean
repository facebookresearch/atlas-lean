/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.NumberTheory.Digits.CommaChildParent
public import MathlibExt.NumberTheory.Digits.CommaNonSuccessors
public import MathlibExt.NumberTheory.Digits.CommaParent
public import MathlibExt.NumberTheory.Digits.CommaTerminal

namespace MetaMathlibExt

@[expose] public section

/-- **Numbers with two comma-children.** Fix a base $b \ge 2$, and say that $n$ has at least two
comma-children if there are distinct digits $y_1 \ne y_2$ below $b$ that are both comma
candidates for $n$ in base $b$ (distinct candidates $y$ give distinct children
$n + b\,(n \bmod b) + y$). Then a positive integer $n < b^2$ has at least two comma-children if
and only if $n = (b - 1 - 2x)\, b + x$ for some $x$ with $1 \le x$ and $2x \le b - 1$; and an
integer $n \ge b^2$ has at least two comma-children if and only if its base-$b$ representation,
most significant digit first, is $d\,(b-1) \cdots (b-1)\, d\,(b-1-d)$ with some number $i \ge 0$
of middle digits $b - 1$ and $1 \le d \le b - 2$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.2 (`fq-2024-sloane05302024-thm-5.2`). -/
public theorem_wanted two_commaChildren_iff (b : ℕ) (hb : 2 ≤ b) :
    (∀ n : ℕ, 0 < n → n < b ^ 2 →
      ((∃ y₁ y₂ : Fin b, y₁ ≠ y₂ ∧ IsCommaCandidate b n y₁ ∧ IsCommaCandidate b n y₂) ↔
        ∃ x : ℕ, 1 ≤ x ∧ 2 * x ≤ b - 1 ∧ n = (b - 1 - 2 * x) * b + x)) ∧
    ∀ n : ℕ, b ^ 2 ≤ n →
      ((∃ y₁ y₂ : Fin b, y₁ ≠ y₂ ∧ IsCommaCandidate b n y₁ ∧ IsCommaCandidate b n y₂) ↔
        ∃ d i : ℕ, 1 ≤ d ∧ d ≤ b - 2 ∧
          Nat.digits b n = [b - 1 - d, d] ++ List.replicate i (b - 1) ++ [d])

/-- **The comma-child graph has an infinite path.** For every base $b \ge 2$ there is a sequence
$a_0, a_1, \dots$ of positive integers such that for every $i$ there is a comma candidate digit
$y$ of $a_i$ in base $b$ with $a_{i+1} = a_i + b\,(a_i \bmod b) + y$, that is, each $a_{i+1}$ is
a comma-child of $a_i$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.6 (`fq-2024-sloane05302024-thm-5.6`). -/
public theorem_wanted exists_infinite_commaChild_path (b : ℕ) (hb : 2 ≤ b) :
    ∃ a : ℕ → ℕ, (∀ i, 0 < a i) ∧
      ∀ i, ∃ y : Fin b, IsCommaCandidate b (a i) y ∧ a (i + 1) = a i + b * (a i % b) + y.val

/-- **There is a unique infinite comma-child path from 1 in base 3.** There is exactly one
sequence $a_0, a_1, \dots$ of natural numbers with $a_0 = 1$ such that for every $i$ there is a
comma candidate digit $y$ of $a_i$ in base $3$ with $a_{i+1} = a_i + 3\,(a_i \bmod 3) + y$,
that is, each $a_{i+1}$ is a base-3 comma-child of $a_i$.

The paper also describes this path (at branch points it alternately takes the lower and the
higher child); that description is not part of this statement.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 10.1 (`fq-2024-sloane05302024-thm-10.1`). -/
public theorem_wanted existsUnique_commaChild_path_base_three :
    ∃! a : ℕ → ℕ, a 0 = 1 ∧
      ∀ i, ∃ y : Fin 3, IsCommaCandidate 3 (a i) y ∧ a (i + 1) = a i + 3 * (a i % 3) + y.val

end

end MetaMathlibExt
