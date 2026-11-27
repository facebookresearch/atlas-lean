/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Pi

/-!
# Type-3 b-nomial numbers

For a base `b ≥ 2`, Ji Young Choi defines a digit in a finite `b`-ary string to be
*indispensable* when it belongs to a constant run whose next digit to the right is smaller.
The type-3 `b`-nomial number counts length-`n` strings having exactly `k` indispensable digits.

Source: Ji Young Choi, *Digit Sums Generalizing Binomial Coefficients*,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Choi/choi15.tex>, the definitions of
indispensable digits and type-3 `b`-nomial numbers.

JIS concept: `jis_sem_c0908e8c24b869247eba442f`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Digits of a string extended by zero.** For a $b$-ary string $x = (x_0, \dots, x_{n-1})$ of
length $n$, written from left to right, and a natural number $j$, this is the digit $x_j$ if
$j < n$, and $0$ if $j \ge n$.

Positions in $x$ run from left to right, so $x_0$ represents the source's leftmost digit $a_n$.
In particular, position $n$ represents the stipulated boundary digit $a_0 = 0$. -/
def bNomialDigitAtOrZero {n b : ℕ} (x : Fin n → Fin b) (j : ℕ) : ℕ :=
  if h : j < n then (x ⟨j, h⟩).val else 0

/-- **Indispensable digits.** Let $x = (x_0, \dots, x_{n-1})$ be a $b$-ary string of length $n$,
written from left to right, and extend it by zero on the right, setting $x_j = 0$ for $j \ge n$.
A position $p < n$ is indispensable in $x$ when there is a natural number $r$ with
$1 \le r \le n + 1 - p$ such that $x_{p+t} = x_p$ for every $t$ with $1 \le t < r$, and
$x_{p+r} < x_p$. That is, some nonempty constant run of digits beginning at position $p$ is
followed on the right by a strictly smaller digit.

The paper writes the digit at position $p$ as $a_i$ with $i = n - p$ and prints the witness bound
$r \le i + 1$, although only the boundary digit $a_0$ (position $n$) is defined. With the zero
extension the final case $r = i + 1$ is unsatisfiable, so the predicate agrees with the source in
every case the source defines. -/
def IsBNomialIndispensableDigit {n b : ℕ} (x : Fin n → Fin b) (p : Fin n) : Prop :=
  ∃ r : Fin (n + 2),
    1 ≤ r.val ∧
      p.val + r.val ≤ n + 1 ∧
      (∀ t : Fin (n + 2), 1 ≤ t.val → t.val < r.val →
        bNomialDigitAtOrZero x (p.val + t.val) = (x p).val) ∧
      bNomialDigitAtOrZero x (p.val + r.val) < (x p).val

/-- The indispensable-digit predicate is decidable by bounded search. -/
instance decidablePredIsBNomialIndispensableDigit {n b : ℕ} (x : Fin n → Fin b) :
    DecidablePred (IsBNomialIndispensableDigit x) := by
  intro p
  unfold IsBNomialIndispensableDigit
  infer_instance

/-- **Number of indispensable digits.** For a $b$-ary string $x$ of finite length, $\iota(x)$ is
the number of positions of $x$ that are indispensable. -/
def bNomialIndispensableDigitCount {n b : ℕ} (x : Fin n → Fin b) : ℕ :=
  Fintype.card { p : Fin n // IsBNomialIndispensableDigit x p }

/-- **Type-3 b-nomial numbers.** For a natural number $b \ge 2$, a natural number $n$ and an
integer $k$, the type-3 $b$-nomial number is the number of $b$-ary strings $x$ of length $n$ with
exactly $k$ indispensable digits, that is, with $\iota(x) = k$. In particular it is zero for
$k < 0$.

At $n = 0$ this gives the source convention: the value is one at $k = 0$ and zero otherwise. -/
def bNomialNumberType3 (b : ℕ) (_hb : 2 ≤ b) (n : ℕ) (k : ℤ) : ℕ :=
  Fintype.card { x : Fin n → Fin b // (bNomialIndispensableDigitCount x : ℤ) = k }

end

end MetaMathlibExt
