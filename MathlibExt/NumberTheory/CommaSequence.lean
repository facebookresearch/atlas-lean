/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Data.Nat.Log

namespace MetaMathlibExt

@[expose] public section

/-- **Most significant digit.** For natural numbers $b$ and $m$, let $k$ be the base-$b$
logarithm of $m$ rounded down, that is, the largest $k$ with $b^k \le m$ when $b \ge 2$ and
$m \ge 1$, and $k = 0$ otherwise. The most significant digit of $m$ in base $b$ is
$\lfloor m / b^k \rfloor$. When $b \ge 2$ and $m \ge 1$ this is the leading digit of the
base-$b$ expansion of $m$.

Source: source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`. -/
public def commaMsd (b m : Nat) : Nat :=
  m / b ^ Nat.log b m

/-- **Comma candidate digits.** Let $b$ and $n$ be natural numbers and let $y$ be a digit with
$0 \le y < b$. Put $m = n + b\,(n \bmod b) + y$, where $n \bmod b$ is the remainder of $n$ on
division by $b$. Then $y$ is a comma candidate for $n$ in base $b$ if $m > 0$ and the most
significant base-$b$ digit of $m$ equals $y$.

For such a candidate $y$ in base $b \ge 2$, the difference $m - n = b\,(n \bmod b) + y$ is
written with the base-$b$ digits $n \bmod b$ and $y$: the last digit of $n$ followed by the
leading digit of $m$.

Source: source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`. -/
public def IsCommaCandidate (b n : Nat) (y : Fin b) : Prop :=
  let m := n + b * (n % b) + y.val
  0 < m ∧ commaMsd b m = y.val

/-- **Comma successor.** Let $b$, $n$ and $m$ be natural numbers. Then $m$ is the comma successor
of $n$ in base $b$ if there is a comma candidate digit $y < b$ for $n$ in base $b$ such that
$m = n + b\,(n \bmod b) + y$ and no digit $y' < y$ is a comma candidate for $n$ in base $b$.

Taking the least candidate $y$ makes $m$ the smallest possible next term.

Source: source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`. -/
public def IsCommaSucc (b n m : Nat) : Prop :=
  ∃ y : Fin b, IsCommaCandidate b n y ∧ m = n + b * (n % b) + y.val ∧
    ∀ y' : Fin b, y'.val < y.val → ¬ IsCommaCandidate b n y'

/-- **Comma-terminal numbers.** Let $b$ and $n$ be natural numbers. Then $n$ is comma-terminal in
base $b$ if no digit $y$ with $0 \le y < b$ is a comma candidate for $n$ in base $b$, so $n$ has
no comma successor in base $b$.

Source: source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`. -/
public def IsCommaTerminal (b n : Nat) : Prop :=
  ∀ y : Fin b, ¬ IsCommaCandidate b n y

/-- **Infinite comma sequences.** Let $b$ and $v$ be natural numbers and let
$a : \mathbb{N} \to \mathbb{N}$ be a sequence. Then $a$ is an infinite comma sequence in base $b$
starting at $v$ if $b \ge 2$, $v > 0$, $a_1 = v$, and for every $n \ge 1$ the term $a_{n+1}$ is
the comma successor of $a_n$ in base $b$.

Indexing starts at $1$; the value $a_0$ is unconstrained.

Source: source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`. -/
public def IsInfiniteCommaSeq (b v : Nat) (a : Nat → Nat) : Prop :=
  2 ≤ b ∧ 0 < v ∧ a 1 = v ∧ ∀ n, 1 ≤ n → IsCommaSucc b (a n) (a (n + 1))

/-- **Terminating comma sequences.** Let $b$ and $v$ be natural numbers. The comma sequence in
base $b$ starting at $v$ terminates if $b \ge 2$, $v > 0$, and there is no infinite comma
sequence in base $b$ starting at $v$.

Source: source lines 183-193, concept `jis_term_0c062437479f9d4e43de4e3f`. -/
public def IsCommaTerminating (b v : Nat) : Prop :=
  2 ≤ b ∧ 0 < v ∧ ¬ ∃ a : Nat → Nat, IsInfiniteCommaSeq b v a

end

end MetaMathlibExt
