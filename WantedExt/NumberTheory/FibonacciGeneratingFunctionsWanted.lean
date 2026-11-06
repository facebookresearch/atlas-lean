/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Int.GCD
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.NumberTheory.GibonacciNumber

namespace MetaMathlibExt

@[expose] public section

/-- **Gibonacci generating function.** For integers $a$ and $b$ and a rational number $x$, the
value of the Gibonacci generating function at $x$ is the rational number

$$G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}.$$

It is the generating function of the Gibonacci sequence $(G_n)_{n \ge 0}$ with $G_0 = a$,
$G_1 = b$ and $G_{n+2} = G_{n+1} + G_n$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public def gibonacciGeneratingValue (a b : ℤ) (x : ℚ) : ℚ :=
  (((b : ℚ) - (a : ℚ)) * x + (a : ℚ)) / (1 - x - x ^ 2)

/-- **Value of the Gibonacci generating function at zero.** For all integers $a$ and $b$, the
Gibonacci generating function $G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}$ takes the value
$G^{(a,b)}(0) = a$ at $x = 0$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem gibonacciGeneratingValue_zero (a b : ℤ) :
    gibonacciGeneratingValue a b 0 = (a : ℚ) := by
  simp [gibonacciGeneratingValue]

/-- **Value of the Gibonacci generating function at one.** For all integers $a$ and $b$, the
Gibonacci generating function $G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}$ takes the value
$G^{(a,b)}(1) = -b$ at $x = 1$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem gibonacciGeneratingValue_one (a b : ℤ) :
    gibonacciGeneratingValue a b 1 = -(b : ℚ) := by
  rw [gibonacciGeneratingValue]
  norm_num
  ring

/-- **Good rationals for a Gibonacci generating function.** Let $a$ and $b$ be integers and let
$G^{(a,b)}(x) = \frac{(b - a)x + a}{1 - x - x^2}$ be the generating function of the Gibonacci
sequence with initial terms $a$ and $b$. A rational number $x$ is good for $(a, b)$ when
$1 - x - x^2 \ne 0$ and $G^{(a,b)}(x)$ is an integer.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1 (the paper says `x = p / q` is good
for `(a, b)` when `G^{(a,b)}(x)` is an integer; Theorem 1 uses the same
integrality without the word good). -/
public def IsGibonacciGood (a b : ℤ) (x : ℚ) : Prop :=
  1 - x - x ^ 2 ≠ 0 ∧ ∃ z : ℤ, gibonacciGeneratingValue a b x = (z : ℚ)

/-- **Zero is good for every pair.** For all integers $a$ and $b$, the rational number $0$ is good
for $(a, b)$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem isGibonacciGood_zero (a b : ℤ) : IsGibonacciGood a b 0 :=
  ⟨by norm_num, a, gibonacciGeneratingValue_zero a b⟩

/-- **One is good for every pair.** For all integers $a$ and $b$, the rational number $1$ is good
for $(a, b)$.

The value of the Gibonacci generating function there is $G^{(a,b)}(1) = -b$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem isGibonacciGood_one (a b : ℤ) : IsGibonacciGood a b 1 :=
  ⟨by norm_num, -b, by rw [gibonacciGeneratingValue_one]; simp⟩

/-- **Generating series of a Gibonacci sequence.** Let $a$ and $b$ be integers and let
$(G_n)_{n \ge 0}$ be the Gibonacci sequence with $G_0 = a$ and $G_1 = b$. In the ring
$\mathbb{Q}[[X]]$ of formal power series with rational coefficients,

$$(1 - X - X^2) \sum_{n \ge 0} G_n X^n = a + (b - a) X.$$

This is the product form of the quotient $\frac{(b - a)x + a}{1 - x - x^2}$ for the generating
function of $(G_n)$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 5
(`jis-2024-24.3.1-lem-5`). -/
public theorem_wanted gibonacci_powerSeries_mul (a b : ℤ) :
    (1 - PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ)
        * PowerSeries.mk (fun n => ((gibonacciNumber a b n : ℤ) : ℚ))
      = PowerSeries.C (a : ℚ)
        + PowerSeries.C ((b : ℚ) - (a : ℚ)) * PowerSeries.X

/-- **Goodness passes to two transformed fractions.** Let $a$, $b$, $p$, $q$ be integers with
$q \ne 0$ and $\gcd(p, q) = 1$, and suppose that $p/q$ is good for $(a, b)$. If $p + q \ne 0$,
then $q/(p + q)$ is good for $(a, b)$; and if $p \ne 0$, then $(q - p)/p$ is good for $(a, b)$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 1
(`jis-2024-24.3.1-thm-1`). -/
public theorem_wanted isGibonacciGood_transform (a b p q : ℤ)
    (hcop : Int.gcd p q = 1) (hq : q ≠ 0)
    (h : IsGibonacciGood a b ((p : ℚ) / (q : ℚ))) :
    (p + q ≠ 0 → IsGibonacciGood a b ((q : ℚ) / ((p : ℚ) + (q : ℚ)))) ∧
    (p ≠ 0 → IsGibonacciGood a b (((q : ℚ) - (p : ℚ)) / (p : ℚ)))

/-- **Congruence criterion for good fractions.** Let $a, b, p, q$ be integers with
$(a, b) \ne (0, 0)$, $q \ne 0$ and $\gcd(p, q) = 1$, and put $m = |q^2 - pq - p^2|$. Then
$p / q$ is good for $(a, b)$ if and only if there are integers $u$ and $v$ with
$(q - p) u \equiv 1$, $p v \equiv 1$, $a \equiv -b p u$ and $a \equiv -b q v \pmod{m}$.

In the source's notation, with modular inverses, the condition reads
$a \equiv -bp(q - p)^{-1} \equiv -bqp^{-1} \pmod{m}$.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 6
(`jis-2024-24.3.1-lem-6`). -/
public theorem_wanted isGibonacciGood_iff (a b p q : ℤ)
    (hab : (a, b) ≠ (0, 0)) (hcop : Int.gcd p q = 1) (hq : q ≠ 0) :
    IsGibonacciGood a b ((p : ℚ) / (q : ℚ)) ↔
    ∃ u v : ℤ, (q - p) * u ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      p * v ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      a ≡ -b * p * u [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
      a ≡ -b * q * v [ZMOD |q ^ 2 - p * q - p ^ 2|]

/-- **Consecutive Fibonacci ratios are good.** For all integers $a$ and $b$ and every natural
number $n$, the ratio $F_n / F_{n+1}$ of consecutive Fibonacci numbers is good for $(a, b)$.

The source allows every integer $n \ne -1$, using the Fibonacci numbers at negative indices.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 7
(`jis-2024-24.3.1-lem-7`). -/
public theorem_wanted isGibonacciGood_fib_div (a b : ℤ) (n : ℕ) :
    IsGibonacciGood a b ((Nat.fib n : ℚ) / (Nat.fib (n + 1) : ℚ))

/-- **Two standard families of good values.** Let $a$ and $b$ be integers and let $(G_n)_{n \ge 0}$
be the Gibonacci sequence with $G_0 = a$ and $G_1 = b$. For every natural number $n$, the ratio
$F_n / F_{n+1}$ of consecutive Fibonacci numbers is good for $(a, b)$, and if $G_n \ne 0$, then
$-G_{n+1} / G_n$ is good for $(a, b)$.

The source indexes both families by all integers ($n \ne -1$ for the first).

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Corollary 2
(`jis-2024-24.3.1-cor-2`). -/
public theorem_wanted isGibonacciGood_standard_values (a b : ℤ) :
    (∀ n : ℕ, IsGibonacciGood a b ((Nat.fib n : ℚ) / (Nat.fib (n + 1) : ℚ))) ∧
    (∀ n : ℕ, gibonacciNumber a b n ≠ 0 →
      IsGibonacciGood a b
        (-(gibonacciNumber a b (n + 1) : ℚ) / (gibonacciNumber a b n : ℚ)))

/-- **Consecutive ratios of a shifted Gibonacci sequence are good.** Let $a$ and $b$ be integers
and let $(H_n)_{n \ge 0}$ be the Gibonacci sequence with $H_0 = -b$ and $H_1 = a$. For every
natural number $n$ with $H_{n+1} \ne 0$, the ratio $H_n / H_{n+1}$ is good for $(a, b)$.

The source indexes $H$ by all integers.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Lemma 8
(`jis-2024-24.3.1-lem-8`). -/
public theorem_wanted isGibonacciGood_shifted_ratio (a b : ℤ) (n : ℕ)
    (h : gibonacciNumber (-b) a (n + 1) ≠ 0) :
    IsGibonacciGood a b
      ((gibonacciNumber (-b) a n : ℚ) / (gibonacciNumber (-b) a (n + 1) : ℚ))

/-- **Good consecutive ratios of a Gibonacci sequence.** Let $p$ and $q$ be coprime integers,
let $(H_n)_{n \ge 0}$ be the Gibonacci sequence with $H_0 = p$ and $H_1 = q$, and put
$m = |q^2 - pq - p^2|$. Call a pair of integers $(a, b)$ admissible when $H_n / H_{n+1}$ is
good for $(a, b)$ for every natural number $n$ with $H_{n+1} \ne 0$. Then there are infinitely
many admissible pairs, and a pair $(a, b)$ is admissible if and only if there are integers $u$
and $v$ with $(q - p) u \equiv 1$, $p v \equiv 1$, $a \equiv -b p u$ and
$a \equiv -b q v \pmod{m}$.

In the source's notation, with modular inverses, the condition reads
$a \equiv -bp(q - p)^{-1} \equiv -bqp^{-1} \pmod{m}$. The source indexes $H$ by all integers.

Source: Knapp, *Fibonacci Generating Functions*, Journal of Integer
Sequences 27 (2024), Article 24.3.1, Theorem 3
(`jis-2024-24.3.1-thm-3`). -/
public theorem_wanted isGibonacciGood_ratios_infinite_iff (p q : ℤ)
    (hcop : Int.gcd p q = 1) :
    (Set.Infinite {ab : ℤ × ℤ | ∀ n : ℕ, gibonacciNumber p q (n + 1) ≠ 0 →
        IsGibonacciGood ab.1 ab.2
          ((gibonacciNumber p q n : ℚ) / (gibonacciNumber p q (n + 1) : ℚ))}) ∧
    ∀ a b : ℤ, (∀ n : ℕ, gibonacciNumber p q (n + 1) ≠ 0 →
        IsGibonacciGood a b
          ((gibonacciNumber p q n : ℚ) / (gibonacciNumber p q (n + 1) : ℚ))) ↔
      ∃ u v : ℤ, (q - p) * u ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
        p * v ≡ 1 [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
        a ≡ -b * p * u [ZMOD |q ^ 2 - p * q - p ^ 2|] ∧
        a ≡ -b * q * v [ZMOD |q ^ 2 - p * q - p ^ 2|]

end

end MetaMathlibExt
