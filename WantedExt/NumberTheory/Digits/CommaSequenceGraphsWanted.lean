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
public import MathlibExt.NumberTheory.Digits.TwoCommaChildren

namespace MetaMathlibExt

@[expose] public section

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
