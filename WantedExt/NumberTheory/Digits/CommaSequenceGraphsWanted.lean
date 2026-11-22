/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Digits.Defs
public import MathlibExt.NumberTheory.CommaSequence

namespace MetaMathlibExt

@[expose] public section

/-- **Landmines of the comma sequence.** Let $b \ge 2$ and let $n$ be a positive integer. Then no
digit $y < b$ is a comma candidate for $n$ in base $b$ (so $n$ has no comma successor) if and
only if the base-$b$ representation of $n$, most significant digit first, is
$(b-1) \cdots (b-1)\, x\, (b-1-x)$ with some number $i \ge 0$ of leading digits $b - 1$ and
$1 \le x \le b - 2$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.1 (`fq-2024-sloane05302024-thm-5.1`). -/
public theorem_wanted isCommaTerminal_iff_digits (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) :
    IsCommaTerminal b n ↔ ∃ i x : ℕ, 1 ≤ x ∧ x ≤ b - 2 ∧
      Nat.digits b n = [b - 1 - x, x] ++ List.replicate i (b - 1)

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

/-- **Recovering the parent of a comma-child.** Fix a base $b \ge 2$ and a natural number $n$.
Call $n$ a comma-child of $k$ if $n = k + b\,(k \bmod b) + y$ for some comma candidate digit $y$
of $k$ in base $b$. Let $f$ be the most significant base-$b$ digit of $n$ and let
$x = (n - f) \bmod b$. If $n$ is a comma-child of a positive integer $k$, then
$k = n - x b - f$; and if the integer $n - x b - f$ is negative, then $n$ is not a comma-child
of any positive integer.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Lemma 5.3 (`fq-2024-sloane05302024-lem-5.3`). -/
public theorem_wanted commaChild_parent_eq (b n : ℕ) (hb : 2 ≤ b) :
    (∀ k : ℕ, 0 < k → (∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val) →
      (k : ℤ) = n - ((n - commaMsd b n) % b : ℕ) * b - commaMsd b n) ∧
    ((n : ℤ) - ((n - commaMsd b n) % b : ℕ) * b - commaMsd b n < 0 →
      ¬ ∃ k : ℕ, 0 < k ∧ ∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val)

/-- **Numbers that are not comma successors.** Let $b \ge 3$ and $n \ge b^2 - 1$. Then $n$ is not
the comma successor in base $b$ of any positive integer if and only if $n = c\, b^i$ for some
$i \ge 2$ and some $c$ with $2 \le c \le b - 1$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.4 (`fq-2024-sloane05302024-thm-5.4`). -/
public theorem_wanted not_commaSucc_iff (b n : ℕ) (hb : 3 ≤ b) (hn : b ^ 2 - 1 ≤ n) :
    (¬ ∃ k : ℕ, 0 < k ∧ IsCommaSucc b k n) ↔
      ∃ c i : ℕ, 2 ≤ i ∧ 2 ≤ c ∧ c ≤ b - 1 ∧ n = c * b ^ i

/-- **Every number at least the square of the base is a comma-child.** Let $b \ge 2$ and
$n \ge b^2$. Then there are a positive integer $k$ and a comma candidate digit $y$ of $k$ in
base $b$ with $n = k + b\,(k \bmod b) + y$, that is, $n$ is a comma-child of $k$.

Source: Éric Angelini, Michael S. Branicky, Giovanni Resta, N. J. A. Sloane, and
David W. Wilson, *The Comma Sequence: A Simple Sequence with Bizarre Properties*, The Fibonacci
Quarterly 62 (2024), no. 3, Theorem 5.5 (`fq-2024-sloane05302024-thm-5.5`). -/
public theorem_wanted exists_commaParent_of_sq_le (b n : ℕ) (hb : 2 ≤ b) (hn : b ^ 2 ≤ n) :
    ∃ k : ℕ, 0 < k ∧ ∃ y : Fin b, IsCommaCandidate b k y ∧ n = k + b * (k % b) + y.val

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
