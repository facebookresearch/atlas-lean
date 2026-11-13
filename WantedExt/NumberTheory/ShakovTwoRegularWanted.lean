/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A 2-regular sequence that counts the divisors of `n^2 + 1`

Statements from Anton Shakov, "A 2-Regular Sequence
That Counts The Divisors of `n^2 + 1`", *Journal of
Integer Sequences* 28 (2025), Article 25.6.2
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Shakov/shakov5.html>).

The sequence `s` is defined by the paper's `2`-regular
recursion (`shakovSeq` below; the value at `0` is a
dummy, the paper's domain is `n ≥ 1`). All statements
were verified numerically: the fibers of `s` match
`τ(m^2 + 1)` for `m ≤ 12`, the block-average formula
for `n ≤ 8`, the primality criterion for `n ≤ 12`,
and `s (a n) = Nat.fib (n - 1)` for `n ≤ 15` (the
paper's `F_n` is `Nat.fib (n - 1)`).

Not stated (see the source audit table): Lemmas 5
and 6 and Corollary 11, which quantify over the
paper's integer pair tree and second component tree,
neither defined in the extracted statements.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.Composite

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ShakovTwoRegularWanted

/-- **Shakov's $2$-regular sequence.** The integer sequence $s$ with $s(0) = s(1) = 0$,
$s(2) = s(3) = 1$ and, for every $k \ge 1$, $s(4k) = 2s(2k) - s(k)$,
$s(4k+1) = 2s(2k) + s(2k+1)$, $s(4k+2) = 2s(2k+1) + s(2k)$ and $s(4k+3) = 2s(2k+1) - s(k)$.

The value $s(0)$ plays no role in the recursion; the source's sequence starts at $n = 1$. -/
def shakovSeq : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | n + 4 =>
      if (n + 4) % 4 = 0 then
        2 * shakovSeq (2 * ((n + 4) / 4)) - shakovSeq ((n + 4) / 4)
      else if (n + 4) % 4 = 1 then
        2 * shakovSeq (2 * ((n + 4) / 4)) +
          shakovSeq (2 * ((n + 4) / 4) + 1)
      else if (n + 4) % 4 = 2 then
        2 * shakovSeq (2 * ((n + 4) / 4) + 1) +
          shakovSeq (2 * ((n + 4) / 4))
      else
        2 * shakovSeq (2 * ((n + 4) / 4) + 1) - shakovSeq ((n + 4) / 4)
  termination_by n => n
  decreasing_by all_goals omega

/-- **Shakov's auxiliary sequence.** The integer sequence $a$ with $a(0) = 0$, $a(1) = 1$ and,
for every $n \ge 2$, $a(n) = 2a(n-1)$ if $n \equiv 0 \pmod 4$, $a(n) = a(n-1) + 1$ if
$n \equiv 1 \pmod 4$, $a(n) = 2a(n-1) + 1$ if $n \equiv 2 \pmod 4$, and $a(n) = a(n-1) - 1$ if
$n \equiv 3 \pmod 4$.

The value $a(0)$ plays no role in the recursion; the source's sequence starts at $n = 1$. -/
def shakovA : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
      if (n + 2) % 4 = 0 then 2 * shakovA (n + 1)
      else if (n + 2) % 4 = 1 then shakovA (n + 1) + 1
      else if (n + 2) % 4 = 2 then 2 * shakovA (n + 1) + 1
      else shakovA (n + 1) - 1

/-- **Shakov's sequence counts the divisors of $m^2 + 1$.** Let $s$ be Shakov's $2$-regular
sequence and let $\tau(N)$ denote the number of positive divisors of $N$. Then $s(n) \ge 0$ for
every $n \ge 1$, and for every natural number $m$ the set $\{n \ge 1 : s(n) = m\}$ is finite
and has exactly $\tau(m^2 + 1)$ elements.

This is the coefficientwise form of the identity
$\sum_{m \ge 0} \tau(m^2 + 1) x^m = \sum_{n \ge 1} x^{s(n)}$ of formal power series.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Theorem 4. -/
theorem_wanted fiber_card (m : ℕ) :
    (∀ n : ℕ, 1 ≤ n → 0 ≤ shakovSeq n) ∧
      ∃ F : Finset ℕ,
        (∀ n : ℕ, n ∈ F ↔ 1 ≤ n ∧ shakovSeq n = (m : ℤ)) ∧
          F.card = (m ^ 2 + 1).divisors.card

/-- **Block averages of Shakov's sequence.** Let $s$ be Shakov's $2$-regular sequence.
For every natural number $n$,
$$
\frac{1}{2^n} \sum_{2^n \le t < 2^{n+1}} s(t) =
\frac{(5 + \sqrt{17})^n - (5 - \sqrt{17})^n}{2^{2n-1} \sqrt{17}},
$$
where the exponent $2n - 1$ is read as $0$ when $n = 0$ (both sides are then $0$).

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 7. -/
theorem_wanted block_average (n : ℕ) :
    (1 / (2 : ℝ) ^ n) *
        (∑ t ∈ Finset.Ico (2 ^ n) (2 ^ (n + 1)),
          (shakovSeq t : ℝ)) =
      ((5 + Real.sqrt 17) ^ n - (5 - Real.sqrt 17) ^ n) /
        ((2 : ℝ) ^ (2 * n - 1) * Real.sqrt 17)

/-- **Primality of $n^2 + 1$ from the fibers of Shakov's sequence.** Let $s$ be Shakov's
$2$-regular sequence. For every natural number $n \ge 1$, the number $n^2 + 1$ is prime if and
only if the set of natural numbers $m$ with $s(m) = n$ is exactly $\{2^n, 2^{n+1} - 1\}$.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 8. -/
theorem_wanted prime_iff_fiber (n : ℕ) (hn : 1 ≤ n) :
    Nat.Prime (n ^ 2 + 1) ↔
      {m : ℕ | shakovSeq m = (n : ℤ)} = {2 ^ n, 2 ^ (n + 1) - 1}

/-- **Shakov's sequence takes Fibonacci values along the auxiliary sequence.** Let $s$ be
Shakov's $2$-regular sequence, let $a$ be Shakov's auxiliary sequence, and let $F_k$ denote the
$k$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For every natural number $n \ge 1$,
$s(\max(a(n), 0)) = F_{n-1}$.

The source shows that $a(n)$ is a positive integer and numbers the Fibonacci numbers so that
this reads $s(a(n)) = F_n$.

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Proposition 9. -/
theorem_wanted shakovSeq_shakovA (n : ℕ) (hn : 1 ≤ n) :
    shakovSeq (shakovA n).toNat = (Nat.fib (n - 1) : ℤ)

/-- **Fibonacci squares plus one are eventually composite.** Let $F_k$ denote the $k$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For every natural number $k \ge 4$, the number
$F_k^2 + 1$ is composite.

In the source's numbering of the Fibonacci numbers, which is shifted by one, this reads
"$F_n^2 + 1$ is composite for $n > 4$".

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Corollary 10. -/
theorem_wanted fib_sq_add_one_composite (k : ℕ) (hk : 4 ≤ k) :
    Nat.IsComposite (Nat.fib k ^ 2 + 1)

end MathlibExt.NumberTheory.ShakovTwoRegularWanted
