/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.NumberTheory.LucasSequence
public import MathlibExt.NumberTheory.TribonacciSequenceWithInitialValues001
public import MathlibExt.NumberTheory.TrinomialCoefficient

/-!
# The 2-Pascal triangle (Otmani)

Statements from Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*,
Journal of Integer Sequences 28 (2025), Article 25.3.5.

The paper's 2-binomial coefficient `binom(n, k)_2` (the entries of the 2-Pascal triangle) is
the coefficient of `X^k` in `(1 + X + X^2)^n`, i.e. `MetaMathlibExt.trinomialCoefficient n k`;
the record of Theorem 3 identifies it through its extraction formula, formalized below as
`trinomialCoefficient_eq_coeff`. Where the paper lets an integer lower index be negative,
the coefficient is `0`; statements spell this out with an `if`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Fundamental theorem of Riordan arrays.** Write $[t^m]F$ for the coefficient of $t^m$ in a
power series $F$. Let $R$ be a commutative ring and let $d$, $h$, $f$ be power series over
$R$ with $h(0) = 0$. Then for every $n \in \mathbb{N}$,

$$\sum_{k=0}^{n} \left([t^n]\,d(t)\,h(t)^k\right) [t^k]\,f = [t^n]\,d(t)\,f(h(t)).$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 1 (`jis-2025-25.3.5-thm-1`). -/
public theorem_wanted riordan_array_sum_eq_coeff_subst {R : Type*} [CommRing R]
    (d h f : PowerSeries R) (hh : constantCoeff h = 0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), coeff n (d * h ^ k) * coeff k f = coeff n (d * f.subst h)

/-- **Trinomial coefficients as coefficients of a rational series.** Write $\binom{n}{k}_2$ for
the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$, and $[t^m]\,F$ for the
coefficient of $t^m$ in a formal power series $F$ over $\mathbb{Q}$. For all natural numbers
$n$ and $k$, $\binom{n}{k}_2 = [t^{2n}]\,(1 - t + t^2)^n (1 - t)^{-1} \left(t/(1-t)\right)^k$.

The paper also allows negative integers $k$; that case is not included here.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 3 (`jis-2025-25.3.5-thm-3`). -/
public theorem_wanted trinomialCoefficient_eq_coeff (n k : ℕ) :
    (trinomialCoefficient n k : ℚ) =
      coeff (2 * n) ((1 - X + X ^ 2) ^ n * (1 - X)⁻¹ * (X * (1 - X)⁻¹) ^ k)

/-- **Roots-of-unity filter for trinomial coefficients.** Write $\binom{n}{k}_2$ for the trinomial
coefficient, the coefficient of $t^k$ in $(1 + t + t^2)^n$. Let $n$, $x$, $b$ be natural
numbers with $x < b$, let $z \ne 0$ be a complex number, and let $w = e^{2\pi i/b}$. Then

$$\sum_{k=0}^{\lfloor (2n - x)/b \rfloor} \binom{n}{x + bk}_2 z^{x + bk} =
\frac{z^n}{b} \sum_{j=1}^{b} w^{j(n - x)} \left(1 + z w^j + \frac{1}{z w^j}\right)^n,$$

where for $x > 2n$ the left side is $0$. The hypothesis $z \ne 0$ is implicit in the
paper's $(z w^j)^{-1}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 9 (`jis-2025-25.3.5-thm-9`). -/
public theorem_wanted sum_trinomialCoefficient_arith_prog (n x b : ℕ) (hxb : x < b) (z : ℂ)
    (hz : z ≠ 0) :
    let w := Complex.exp (2 * Real.pi * Complex.I / b)
    ∑ k ∈ Finset.range ((2 * n - x) / b + 1), (trinomialCoefficient n (x + b * k) : ℂ) *
        z ^ (x + b * k) =
      z ^ n * (1 / b) * ∑ j ∈ Finset.Icc 1 b,
        w ^ ((j : ℤ) * ((n : ℤ) - x)) * (1 + z * w ^ j + (z * w ^ j)⁻¹) ^ n

/-- **Alternating trinomial sums over residue classes modulo 3 and 5.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$, and
$L_m$ for the Lucas numbers ($L_0 = 2$, $L_1 = 1$, $L_{m+2} = L_{m+1} + L_m$). Let $n$ and $x$ be
natural numbers.

If $x < 3$, then $3 \sum_{k=0}^{2n} (-1)^{k+x} \binom{n}{3k+x}_2$ equals $(-1)^n 2^{n+1} + 1$
when $n \equiv x \pmod 3$, and $(-1)^{n+1} 2^n + 1$ otherwise.

If $x < 5$, let $S = 5 \sum_{k=0}^{2n} (-1)^{k+x} \binom{n}{5k+x}_2$. Then
$S = 2 (-1)^n L_{2n} + 1$ when $n \equiv x \pmod 5$, $S = (-1)^{n+1} L_{2n+1} + 1$ when
$n \equiv x \pm 1 \pmod 5$, and $S = (-1)^n L_{2n-1} + 1$ when $n \ge 1$ and
$n \equiv x \pm 2 \pmod 5$.

The paper does not bound $x$; the last case excludes $n = 0$, where it would need $L_{-1}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 10 (`jis-2025-25.3.5-cor-10`). -/
public theorem_wanted trinomialCoefficient_alternating_sums_mod_three_five (n x : ℕ) :
    (x < 3 →
      3 * ∑ k ∈ Finset.range (2 * n + 1),
          (trinomialCoefficient n (3 * k + x) : ℤ) * (-1) ^ (k + x) =
        if n ≡ x [MOD 3] then (-1) ^ n * 2 ^ (n + 1) + 1 else (-1) ^ (n + 1) * 2 ^ n + 1) ∧
    (x < 5 →
      let S := 5 * ∑ k ∈ Finset.range (2 * n + 1),
          (trinomialCoefficient n (5 * k + x) : ℤ) * (-1) ^ (k + x)
      (n ≡ x [MOD 5] → S = 2 * (-1) ^ n * lucasNumber (2 * n) + 1) ∧
        (n ≡ x + 1 [MOD 5] ∨ x ≡ n + 1 [MOD 5] → S = (-1) ^ (n + 1) * lucasNumber (2 * n + 1) + 1) ∧
        (1 ≤ n → n ≡ x + 2 [MOD 5] ∨ x ≡ n + 2 [MOD 5] →
          S = (-1) ^ n * lucasNumber (2 * n - 1) + 1))

/-- **Alternating sums of trinomial coefficients in an arithmetic progression.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1 + t + t^2)^n$.
For natural numbers $n$, $x$, $b$ with $b$ even and $x < b$,

$$\sum_{k=0}^{2n} (-1)^k \binom{n}{x + bk}_2 = \frac{1}{b} \sum_{j=1}^{b}
\cos\frac{\pi(n - x)(1 + 2j)}{b} \left(1 + 2\cos\frac{\pi(2j + 1)}{b}\right)^n.$$

The paper sums over all $k \ge 0$ (the terms with $k > 2n$ vanish) and does not state
$x < b$; without it the identity fails: for $n = 3$ and $b = x = 2$ the left side is $1$ and
the right side is $0$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 11 (`jis-2025-25.3.5-cor-11`). -/
public theorem_wanted sum_trinomialCoefficient_arith_prog_alternating (n x b : ℕ)
    (hb : Even b) (hxb : x < b) :
    ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient n (x + b * k) : ℝ) * (-1) ^ k =
      1 / b * ∑ j ∈ Finset.Icc 1 b,
        Real.cos (Real.pi * ((n : ℝ) - x) * (1 + 2 * j) / b) *
          (1 + 2 * Real.cos (Real.pi * (2 * j + 1) / b)) ^ n

/-- **Generating polynomial of trinomial coefficients with even index.** Write $\binom{n}{k}_2$
for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For every
$n \in \mathbb{N}$ and all complex numbers $z$ and $s$ with $s^2 = z$
$$\sum_{k=0}^{n} \binom{n}{2k}_2 z^k = \frac{(1 + s + z)^n + (1 - s + z)^n}{2}.$$

The paper states this for an indeterminate $z$, with $\sqrt{z}$ in place of $s$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 13 (`jis-2025-25.3.5-cor-13`). -/
public theorem_wanted sum_trinomialCoefficient_even (n : ℕ) (z s : ℂ) (hs : s ^ 2 = z) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k) : ℂ) * z ^ k =
      ((1 + s + z) ^ n + (1 - s + z) ^ n) / 2

/-- **Generating polynomial of trinomial coefficients with odd index.** Write $\binom{n}{k}_2$
for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For every
$n \in \mathbb{N}$ and all complex numbers $z$ and $s$ with $s^2 = z$ and $s \ne 0$
$$\sum_{k=0}^{n} \binom{n}{2k+1}_2 z^k = \frac{(1 + s + z)^n - (1 - s + z)^n}{2s}.$$

The paper states this for an indeterminate $z$, with $\sqrt{z}$ in place of $s$, and calls the
left side $q_n(z)$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 15 (`jis-2025-25.3.5-cor-15`). -/
public theorem_wanted sum_trinomialCoefficient_odd (n : ℕ) (z s : ℂ) (hs : s ^ 2 = z)
    (hs0 : s ≠ 0) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k + 1) : ℂ) * z ^ k =
      ((1 + s + z) ^ n - (1 - s + z) ^ n) / (2 * s)

/-- **Alternating binomial transform of a row of trinomial coefficients.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For all
$n, m \in \mathbb{N}$
$$\sum_{k=m}^{2n} \binom{n}{k}_2 \binom{k}{m} (-1)^k = \binom{n}{m}_2.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 16 (`jis-2025-25.3.5-thm-16`). -/
public theorem_wanted sum_trinomialCoefficient_mul_choose_alternating (n m : ℕ) :
    ∑ k ∈ Finset.Icc m (2 * n), (trinomialCoefficient n k : ℤ) * k.choose m * (-1) ^ k =
      (trinomialCoefficient n m : ℤ)

/-- **Two binomial transforms of a row of trinomial coefficients agree.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For all
$n, m \in \mathbb{N}$
$$\sum_{k=0}^{m} \binom{n}{k}_2 \binom{m}{k} =
\sum_{k=0}^{2n} \binom{n}{k}_2 \binom{m+k}{k} (-1)^k.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 17 (`jis-2025-25.3.5-thm-17`). -/
public theorem_wanted sum_trinomialCoefficient_mul_choose_eq (n m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (trinomialCoefficient n k : ℤ) * m.choose k =
      ∑ k ∈ Finset.range (2 * n + 1),
        (trinomialCoefficient n k : ℤ) * (m + k).choose k * (-1) ^ k

/-- **Alternating binomial sum down a trinomial column.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For natural numbers $n \le m$,
$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{n-k}{m}_2 = \binom{n}{m-n}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 18 (`jis-2025-25.3.5-thm-18`). -/
public theorem_wanted sum_trinomialCoefficient_sub_mul_choose (n m : ℕ) (h : n ≤ m) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n - k) m : ℤ) * n.choose k * (-1) ^ k =
      (n.choose (m - n) : ℤ)

/-- **Alternating binomial sum of trinomial coefficients over even rows.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For
every natural number $n$, $\sum_{k=0}^{n} (-1)^k \binom{n}{k} \binom{2n-2k}{n}_2 = 2^n$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 19 (`jis-2025-25.3.5-thm-19`). -/
public theorem_wanted sum_trinomialCoefficient_two_mul_sub (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (trinomialCoefficient (2 * n - 2 * k) n : ℤ) * n.choose k * (-1) ^ k = 2 ^ n

/-- **Vandermonde convolution for trinomial coefficients.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $t^k$ in $(1 + t + t^2)^n$, and put $\binom{n}{k}_2 = 0$
for negative integers $k$. Then for all natural numbers $n$, $m$ and every integer $l$,

$$\sum_{k=0}^{2m} \binom{n}{l + k}_2 \binom{m}{k}_2 = \binom{n + m}{2m + l}_2.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 20 (`jis-2025-25.3.5-thm-20`). -/
public theorem_wanted sum_trinomialCoefficient_convolution (n m : ℕ) (l : ℤ) :
    ∑ k ∈ Finset.range (2 * m + 1),
        (if 0 ≤ l + k then trinomialCoefficient n (l + k).toNat else 0) *
          trinomialCoefficient m k =
      if 0 ≤ 2 * m + l then trinomialCoefficient (n + m) (2 * m + l).toNat else 0

/-- **Alternating sum of squared trinomial coefficients.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For every natural number $n$,
$\sum_{k=0}^{2n} (-1)^k \binom{n}{k}_2^2 = \binom{n}{n}_2$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 24 (`jis-2025-25.3.5-thm-24`). -/
public theorem_wanted sum_trinomialCoefficient_sq_alternating (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient n k : ℤ) ^ 2 * (-1) ^ k =
      (trinomialCoefficient n n : ℤ)

/-- **Sums of squares and products of trinomial coefficients with even index.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For
every $n \in \mathbb{N}$ let $c_n = \binom{n}{n/2}_2$ if $n$ is even and $c_n = 0$ if $n$ is odd.
Then
$$\sum_{k=0}^{n} \binom{n}{2k}_2^2 = \frac{1}{2}\binom{2n}{2n}_2 + \frac{1}{2}\binom{n}{n}_2$$
and
$$\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{n-2k}_2 \binom{n}{2k}_2 =
\frac{1}{2}\binom{2n}{n}_2 + \frac{1}{2} c_n.$$

For odd $n$ the paper's $\binom{n}{n/2}_2$ is read as $0$: the floor reading fails, e.g. at
$n = 1$ the left side is $1$ while $\frac{1}{2}\binom{2}{1}_2 + \frac{1}{2}\binom{1}{0}_2 = 3/2$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 26 (`jis-2025-25.3.5-thm-26`). -/
public theorem_wanted sum_trinomialCoefficient_even_sq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (2 * k) : ℚ) ^ 2 =
        (trinomialCoefficient (2 * n) (2 * n) : ℚ) / 2 + (trinomialCoefficient n n : ℚ) / 2 ∧
      ∑ k ∈ Finset.range (n / 2 + 1),
          (trinomialCoefficient n (n - 2 * k) : ℚ) * trinomialCoefficient n (2 * k) =
        (trinomialCoefficient (2 * n) n : ℚ) / 2 +
          (if Even n then (trinomialCoefficient n (n / 2) : ℚ) else 0) / 2

/-- **Absorption identity for trinomial coefficients.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For natural numbers $n \ge 1$
and $k$, $\frac{k}{n} \binom{n}{k}_2 = \binom{n-1}{k-1}_2 + 2 \binom{n-1}{k-2}_2$, where a term
whose lower index is negative is read as $0$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Lemma 31 (`jis-2025-25.3.5-lem-31`). -/
public theorem_wanted trinomialCoefficient_absorption (n k : ℕ) (hn : 0 < n) :
    (k : ℚ) / n * trinomialCoefficient n k =
      (if 1 ≤ k then (trinomialCoefficient (n - 1) (k - 1) : ℚ) else 0) +
        2 * (if 2 ≤ k then (trinomialCoefficient (n - 1) (k - 2) : ℚ) else 0)

/-- **Weighted diagonal sums of trinomial coefficients by coefficient extraction.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$,
$[t^m]\,g$ for the coefficient of $t^m$ in a power series $g$, and $f_k = [t^k]\,f$. For every
integer $n > 0$ and every formal power series $f \in \mathbb{Q}[[t]]$
$$\sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 \frac{n}{n-k} f_k =
[t^{2n}]\, \frac{(1-t+t^2)^{n-1}(3-4t+2t^2)}{1-t}\,
f\!\left(\frac{t^3}{(1-t+t^2)(1-t)}\right).$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 32 (`jis-2025-25.3.5-thm-32`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_weighted (n : ℕ) (hn : 0 < n)
    (f : PowerSeries ℚ) :
    ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℚ) * n / (n - k : ℕ) * coeff k f =
      coeff (2 * n) ((1 - X + X ^ 2) ^ (n - 1) * (3 - 4 * X + 2 * X ^ 2) * (1 - X)⁻¹ *
        f.subst (X ^ 3 * ((1 - X + X ^ 2) * (1 - X))⁻¹))

/-- **Alternating weighted diagonal sum of trinomial coefficients.** Write $\binom{n}{k}_2$ for
the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For every integer $n > 0$
let $S_n = \sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 \frac{n}{n-k} (-1)^k$, a rational
number. Then $S_n = 1$ if $n \equiv 1$ or $n \equiv 3 \pmod 4$, $S_n = -1$ if
$n \equiv 2 \pmod 4$, and $S_n = 3$ if $n \equiv 0 \pmod 4$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 35 (`jis-2025-25.3.5-cor-35`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_alternating (n : ℕ) (hn : 0 < n) :
    let S := ∑ k ∈ Finset.range (2 * n / 3 + 1),
      (trinomialCoefficient (n - k) k : ℚ) * n / (n - k : ℕ) * (-1) ^ k
    (n % 4 = 1 ∨ n % 4 = 3 → S = 1) ∧ (n % 4 = 2 → S = -1) ∧ (n % 4 = 0 → S = 3)

/-- **Generating sum of the upper half of a trinomial row.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. For every natural number $n$
and every complex number $w$,
$$\sum_{k=0}^{n} \binom{n}{n-k}_2 w^{n+k} = \frac{(1+w+w^2)^n}{2} + \frac{\binom{n}{n}_2 w^n}{2} +
\frac{w^2-1}{2} \sum_{k=0}^{n-1} \binom{k}{k}_2 (1+w+w^2)^{n-1-k} w^k.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 40 (`jis-2025-25.3.5-cor-40`). -/
public theorem_wanted sum_trinomialCoefficient_upper_half (n : ℕ) (w : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient n (n - k) : ℂ) * w ^ (n + k) =
      (1 + w + w ^ 2) ^ n / 2 + (trinomialCoefficient n n : ℂ) * w ^ n / 2 +
        (w ^ 2 - 1) / 2 * ∑ k ∈ Finset.range n,
          (trinomialCoefficient k k : ℂ) * (1 + w + w ^ 2) ^ (n - 1 - k) * w ^ k


/-- **Trinomial coefficients along lines from a square-root series.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$, and
$[t^m]\,F$ for the coefficient of $t^m$ in a formal power series $F$ over $\mathbb{Q}$. Let $S$
be a power series over $\mathbb{Q}$ with $S^2 = 1 - 2t - 3t^2$ and $S(0) = 1$. For natural
numbers $n, a, b, k$ with $2a \le b$,
$2^{(b-a)k} \binom{n+ak}{n+bk}_2 = [t^{n+bk}]\, S^{-1} (1 - t - S)^{(b-a)k}$.

Equivalently $\binom{n+ak}{n+bk}_2 = [t^n]\, S^{-1}
\left((1 - t - S)^{b-a} / (2^{b-a} t^b)\right)^k$, the paper's form, which allows integers
$a$ and $b$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 38 (`jis-2025-25.3.5-thm-38`). -/
public theorem_wanted trinomialCoefficient_eq_coeff_sqrt (n a b k : ℕ) (hab : 2 * a ≤ b)
    (S : PowerSeries ℚ) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2) (hS0 : constantCoeff S = 1) :
    2 ^ ((b - a) * k) * (trinomialCoefficient (n + a * k) (n + b * k) : ℚ) =
      coeff (n + b * k) (S⁻¹ * (1 - X - S) ^ ((b - a) * k))

/-- **Inversion of an implicit Riordan array sum.** Write $[t^m]F$ for the coefficient of $t^m$
in a power series $F$ and $F'$ for its formal derivative. Let $K$ be a field and let $f$,
$\psi$, $g$, $b$ be power series over $K$ with $f(0) \ne 0$, $\psi(0) \ne 0$ and $g(0) \ne 0$.
Put $h(t) = t\,g(t)$ and, for $m \in \mathbb{N}$, $a_m = [t^m]\,f(t)\,\psi(t)^m\,b(h(t))$. Then
for every $n \in \mathbb{N}$,

$$[t^n]\,b = \sum_{k=0}^{n} \left([t^{n-k}]\,
\frac{(\psi - t\psi')\,h'}{f\,\psi^{k+1}\,g^{n+1}}\right) a_k.$$

The paper writes the factor $1/g^{n+1}$ as $t^{n+1}/h(t)^{n+1}$ and does not state the
hypothesis $f(0) \ne 0$, which $1/f$ needs.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 47 (`jis-2025-25.3.5-thm-47`). -/
public theorem_wanted implicit_riordan_sum_inverse {K : Type*} [Field K]
    (f ψ g b : PowerSeries K) (hf : constantCoeff f ≠ 0) (hψ : constantCoeff ψ ≠ 0)
    (hg : constantCoeff g ≠ 0) (n : ℕ) :
    let h := X * g
    let a : ℕ → K := fun m => coeff m (f * ψ ^ m * b.subst h)
    coeff n b = ∑ k ∈ Finset.range (n + 1),
      coeff (n - k) ((ψ - X * derivative ψ) * derivative h * (f * ψ ^ (k + 1))⁻¹ *
        g⁻¹ ^ (n + 1)) * a k


/-- **Sprugnoli's binomial sum theorem.** Write $[t^j]F$ for the coefficient of $t^j$ in a power
series $F$ over $\mathbb{C}$, $\binom{u}{j}$ for the generalized binomial coefficient, and
$(1 + t)^u = \sum_{j \ge 0} \binom{u}{j} t^j$ for the binomial series of a complex number $u$.
Let $f$ be a power series over $\mathbb{C}$. For natural numbers $n$, $x$, $a$, $b$ with
$a < b$,

$$\sum_{k=0}^{n} \binom{n + ak}{x + bk} [t^k]\,f =
[t^n]\,\frac{t^x}{(1 - t)^{x+1}}\, f\!\left(\frac{t^{b-a}}{(1 - t)^b}\right),$$

and for natural numbers $m$, $c$ with $c > 0$, every complex $y$ and every integer $a'$,

$$\sum_{k=0}^{\lfloor m/c \rfloor} \binom{y + a'k}{m - ck} [t^k]\,f =
[t^m]\,(1 + t)^y f\!\left(t^c (1 + t)^{a'}\right).$$

In the first sum the terms with $k > n$ would vanish, and the second stops where the lower
index $m - ck$ would become negative. The paper allows integer $x$ and $a$ in the first
identity and writes the second with $b = -c < 0$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 2 (`jis-2025-25.3.5-thm-2`). -/
public theorem_wanted sum_choose_mul_coeff_eq_coeff_subst (n x a b m c : ℕ) (hab : a < b)
    (hc : 0 < c) (y : ℂ) (a' : ℤ) (f : PowerSeries ℂ) :
    ∑ k ∈ Finset.range (n + 1), ((n + a * k).choose (x + b * k) : ℂ) * coeff k f =
        coeff n (X ^ x * ((1 - X) ^ (x + 1))⁻¹ * f.subst (X ^ (b - a) * ((1 - X) ^ b)⁻¹)) ∧
      ∑ k ∈ Finset.range (m / c + 1), Ring.choose (y + a' * k) (m - c * k) * coeff k f =
        coeff m (PowerSeries.binomialSeries ℂ y *
          f.subst (X ^ c * PowerSeries.binomialSeries ℂ (a' : ℂ)))

/-- **Trinomial coefficients from an algebraic Riordan array.** Write $\binom{n}{k}_2$ for the
trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$, and $[t^m]\,F$ for the
coefficient of $t^m$ in a formal power series $F$ over $\mathbb{Q}$. Let $S$ and $Q$ be power
series over $\mathbb{Q}$ with $S^2 = 4 - 3t^2$, $S(0) = 2$, $2Q^2 = 2 - t^2 - tS$ and $Q(0) = 1$,
and put
$$\alpha = \frac{-2\,(2Q + t^2 S - t)}{Q\,(3t^4 + 2tS - t^2 - 4)}, \qquad
\beta = \frac{t\,(t + S)}{2\,(1 - t^2)}.$$
Then $\binom{n}{k}_2 = [t^{2n}]\,\alpha\,\beta^k$ for all natural numbers $n$ and $k$.

In the paper $S = \sqrt{4 - 3t^2}$ and $\sqrt{2}\,Q = \sqrt{2 - t^2 - t\sqrt{4 - 3t^2}}$; since
$\sqrt{8 - 6t^2} = \sqrt{2}\,S$, the factors $\sqrt{2}$ in its formula for $\alpha$ cancel.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 6 (`jis-2025-25.3.5-thm-6`). -/
public theorem_wanted trinomialCoefficient_eq_coeff_alpha_mul_beta_pow (S Q : PowerSeries ℚ)
    (hS : S ^ 2 = 4 - 3 * X ^ 2) (hS0 : constantCoeff S = 2)
    (hQ : 2 * Q ^ 2 = 2 - X ^ 2 - X * S) (hQ0 : constantCoeff Q = 1) (n k : ℕ) :
    let α := -2 * (2 * Q + X ^ 2 * S - X) * (Q * (3 * X ^ 4 + 2 * X * S - X ^ 2 - 4))⁻¹
    let β := X * (X + S) * (2 * (1 - X ^ 2))⁻¹
    (trinomialCoefficient n k : ℚ) = coeff (2 * n) (α * β ^ k)

/-- **Sums of trinomial coefficients along lines by coefficient extraction.** Write $[t^j]\,g$
for the coefficient of $t^j$ in a power series $g$, and $f_k = [t^k]\,f$. For $n \in \mathbb{N}$
let $\binom{n}{j}_2 = [t^j]\,(1+t+t^2)^n$ be the trinomial coefficient. For complex $u$ and $z$
let $(1 + zt + z^2t^2)^u$ be the binomial series $\sum_{i \ge 0} \binom{u}{i} (zt + z^2t^2)^i$,
and for complex $u$ let $\binom{u}{j}_2 = [t^j]\,(1+t+t^2)^u$. Let $n, x, a, b, m, c$ be natural
numbers with $2a < b$ and $c > 0$, let $y, z \in \mathbb{C}$, let $a'$ be an integer and let
$f \in \mathbb{C}[[t]]$. Then
$$\sum_{k=0}^{2n} \binom{n+ak}{x+bk}_2 z^{2(n+ak)-(x+bk)} f_k =
[t^{2n}]\, (1-zt+z^2t^2)^n \frac{t^x}{(1-zt)^{x+1}}\,
f\!\left(\frac{t^{b-2a} (1-zt+z^2t^2)^a}{(1-zt)^b}\right),$$
where a term with $x + bk > 2(n+ak)$ is $0$ because its trinomial coefficient is, and
$$\sum_{k=0}^{\lfloor m/c \rfloor} \binom{y+a'k}{m-ck}_2 z^{m-ck} f_k =
[t^m]\, (1+zt+z^2t^2)^y\, f\big(t^c (1+zt+z^2t^2)^{a'}\big).$$

The paper allows integers $x$ and $a$ in the first identity and obtains the second as the case
$b = -c < 0$; $\binom{u}{j}_2$ for complex $u$ is Comtet's extension (the paper's Eq. (8)).

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 7 (`jis-2025-25.3.5-thm-7`). -/
public theorem_wanted sum_trinomialCoefficient_mul_coeff_eq_coeff_subst (n x a b m c : ℕ)
    (hab : 2 * a < b) (hc : 0 < c) (y z : ℂ) (a' : ℤ) (f : PowerSeries ℂ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    let P : ℂ → PowerSeries ℂ := fun u =>
      (PowerSeries.binomialSeries ℂ u).subst (C z * X + C z ^ 2 * X ^ 2)
    ∑ k ∈ Finset.range (2 * n + 1), (trinomialCoefficient (n + a * k) (x + b * k) : ℂ) *
          z ^ (2 * (n + a * k) - (x + b * k)) * coeff k f =
        coeff (2 * n) ((1 - C z * X + C z ^ 2 * X ^ 2) ^ n * X ^ x *
          ((1 - C z * X) ^ (x + 1))⁻¹ * f.subst (X ^ (b - 2 * a) *
            (1 - C z * X + C z ^ 2 * X ^ 2) ^ a * ((1 - C z * X) ^ b)⁻¹)) ∧
      ∑ k ∈ Finset.range (m / c + 1), E (y + a' * k) (m - c * k) * z ^ (m - c * k) * coeff k f =
        coeff m (P y * f.subst (X ^ c * P a'))

/-- **Gould-type identities for binomial and extended trinomial coefficients.** For complex $u$
and $j \in \mathbb{N}$ write $\binom{u}{j}$ for the generalized binomial coefficient and
$\binom{u}{j}_2$ for the coefficient of $t^j$ in
$(1 + t + t^2)^u = \sum_{i \ge 0} \binom{u}{i}(t + t^2)^i$ (Comtet's extension). Then for all
complex $x$, $y$ and every $n \in \mathbb{N}$,

$$\sum_{k=0}^{\lfloor n/3 \rfloor} \binom{x}{k}\binom{y - 3x}{n - 3k} =
\sum_{k=0}^{n} \binom{x}{k}\binom{y - 2k}{n - k}(-3)^k$$

and

$$\sum_{k=0}^{\lfloor n/3 \rfloor} \binom{-x}{n - 3k}_2 \binom{x}{k}(-1)^k = (-1)^n \binom{x}{n}.$$

The paper's Eq. (25) also equates the first two sums with
$\sum_k \binom{2x}{n-k}_2 \binom{y-2x}{k}(-1)^{n-k}$; that expression is left out because it is
false as printed: at $x = 2$, $y = 1/3$, $n = 1$ it equals $-23/3$, while both sides of the
first identity equal $-17/3$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 21 (`jis-2025-25.3.5-thm-21`). -/
public theorem_wanted sum_choose_gould_and_extended_trinomial (x y : ℂ) (n : ℕ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    ∑ k ∈ Finset.range (n / 3 + 1), Ring.choose x k * Ring.choose (y - 3 * x) (n - 3 * k) =
        ∑ k ∈ Finset.range (n + 1),
          Ring.choose x k * Ring.choose (y - 2 * k) (n - k) * (-3) ^ k ∧
      ∑ k ∈ Finset.range (n / 3 + 1), E (-x) (n - 3 * k) * Ring.choose x k * (-1) ^ k =
        (-1) ^ n * Ring.choose x n

/-- **An alternating convolution of extended trinomial coefficients.** For complex $u$ and
$j \in \mathbb{N}$ write $\binom{u}{j}_2$ for the coefficient of $t^j$ in
$(1 + t + t^2)^u = \sum_{i \ge 0} \binom{u}{i}(t + t^2)^i$ (Comtet's extension), where
$\binom{u}{i}$ is the generalized binomial coefficient. Then for every complex $x$ and every
$n \in \mathbb{N}$,

$$\sum_{k=0}^{n} \binom{2n - x}{n - k}_2 \binom{x}{k}_2 (-1)^k =
\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{2n - 2x}{n - 2k}_2 \binom{x}{k}_2.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 23 (`jis-2025-25.3.5-thm-23`). -/
public theorem_wanted sum_extended_trinomial_alternating_eq (x : ℂ) (n : ℕ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    ∑ k ∈ Finset.range (n + 1), E (2 * n - x) (n - k) * E x k * (-1) ^ k =
      ∑ k ∈ Finset.range (n / 2 + 1), E (2 * n - 2 * x) (n - 2 * k) * E x k

/-- **Tribonacci numbers from every third term of A077943.** Let $T_n$ be the Tribonacci
numbers, $T_0 = T_1 = 0$, $T_2 = 1$ and $T_{n+3} = T_{n+2} + T_{n+1} + T_n$. Let
$(y_n)_{n \ge 0}$ be a sequence of integers with $y_0 = y_1 = 0$, $y_2 = 1$ and
$y_{n+3} = 2y_{n+2} - 2y_{n+1} + 2y_n$ for all $n \ge 0$ (the sequence A077943). Then for
every $n \ge 0$, $2^{n+1} T_{n+2} = y_{3(n+1)}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 27 (`jis-2025-25.3.5-thm-27`). -/
public theorem_wanted two_pow_mul_tribonacci_eq (y : ℕ → ℤ) (hy0 : y 0 = 0) (hy1 : y 1 = 0)
    (hy2 : y 2 = 1) (hy : ∀ n, y (n + 3) = 2 * y (n + 2) - 2 * y (n + 1) + 2 * y n) (n : ℕ) :
    2 ^ (n + 1) * (tribonacci (n + 2) : ℤ) = y (3 * (n + 1))

/-- **Binet-type formula for diagonal sums of trinomial coefficients.** Write $\binom{n}{k}_2$
for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. Let $z, w \in \mathbb{C}$
and let $r_1, r_2, r_3 \in \mathbb{C}$ be pairwise distinct with $r_1 + r_2 + r_3 = 2w$,
$r_1 r_2 + r_1 r_3 + r_2 r_3 = 2w^2$ and $r_1 r_2 r_3 = z + w^3$, that is, let $r_1, r_2, r_3$
be the three distinct zeros of $t^3 - 2wt^2 + 2w^2 t - (z + w^3)$. Then for every
$n \in \mathbb{N}$
$$\sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 w^{2n-3k} z^k =
\sum_{i=1}^{3} \frac{(w^2 - w r_i + r_i^2)^{n+1}}{\prod_{j \ne i} (r_i - r_j)}.$$

The paper names the zeros $\alpha_{z,w}, \beta_{z,w}, \bar\beta_{z,w}$ by Cardano's formulas; the
right side is symmetric, so they are given here by Vieta's relations.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 28 (`jis-2025-25.3.5-thm-28`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_binet (z w r₁ r₂ r₃ : ℂ)
    (h₁ : r₁ + r₂ + r₃ = 2 * w) (h₂ : r₁ * r₂ + r₁ * r₃ + r₂ * r₃ = 2 * w ^ 2)
    (h₃ : r₁ * r₂ * r₃ = z + w ^ 3) (h₁₂ : r₁ ≠ r₂) (h₁₃ : r₁ ≠ r₃) (h₂₃ : r₂ ≠ r₃) (n : ℕ) :
    ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℂ) * w ^ (2 * n - 3 * k) * z ^ k =
      (w ^ 2 - w * r₁ + r₁ ^ 2) ^ (n + 1) / ((r₁ - r₂) * (r₁ - r₃)) +
        (w ^ 2 - w * r₂ + r₂ ^ 2) ^ (n + 1) / ((r₂ - r₁) * (r₂ - r₃)) +
        (w ^ 2 - w * r₃ + r₃ ^ 2) ^ (n + 1) / ((r₃ - r₁) * (r₃ - r₂))

/-- **Weighted diagonal sums of trinomial coefficients and the sequence A075115.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $x^k$ in $(1+x+x^2)^n$. Let
$(\lambda_m)$ be the integer sequence with $\lambda_0 = 3$, $\lambda_1 = 2$, $\lambda_2 = 0$ and
$\lambda_{m+3} = 2\lambda_{m+2} - 2\lambda_{m+1} + 2\lambda_m$ (OEIS A075115). For every natural
number $n \ge 1$,
$2^n \sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 \frac{n}{n-k} = \lambda_{3n}$.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 33 (`jis-2025-25.3.5-cor-33`). -/
public theorem_wanted two_pow_mul_sum_trinomialCoefficient_diagonal_weighted (l : ℕ → ℤ)
    (hl0 : l 0 = 3) (hl1 : l 1 = 2) (hl2 : l 2 = 0)
    (hl : ∀ n, l (n + 3) = 2 * l (n + 2) - 2 * l (n + 1) + 2 * l n) (n : ℕ) (hn : 0 < n) :
    2 ^ n * ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℚ) * n / (n - k : ℕ) = l (3 * n)

/-- **Power-sum formula for weighted diagonal sums of trinomial coefficients.** Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. Let
$z, w \in \mathbb{C}$ and let $r_1, r_2, r_3 \in \mathbb{C}$ satisfy $r_1 + r_2 + r_3 = 2w$,
$r_1 r_2 + r_1 r_3 + r_2 r_3 = 2w^2$ and $r_1 r_2 r_3 = z + w^3$, that is, let $r_1, r_2, r_3$
be the zeros, with multiplicity, of $t^3 - 2wt^2 + 2w^2 t - (z + w^3)$. Then for every integer
$n > 0$
$$\sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 \frac{n}{n-k} w^{2n-3k} z^k =
(w^2 - w r_1 + r_1^2)^n + (w^2 - w r_2 + r_2^2)^n + (w^2 - w r_3 + r_3^2)^n.$$

The zeros (Cardano's $\alpha_{z,w}, \beta_{z,w}, \bar\beta_{z,w}$ in the paper) are given by
Vieta's relations.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 36 (`jis-2025-25.3.5-cor-36`). -/
public theorem_wanted sum_trinomialCoefficient_diagonal_weighted_power_sum (z w r₁ r₂ r₃ : ℂ)
    (h₁ : r₁ + r₂ + r₃ = 2 * w) (h₂ : r₁ * r₂ + r₁ * r₃ + r₂ * r₃ = 2 * w ^ 2)
    (h₃ : r₁ * r₂ * r₃ = z + w ^ 3) (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.range (2 * n / 3 + 1),
        (trinomialCoefficient (n - k) k : ℂ) * n / (n - k : ℕ) * w ^ (2 * n - 3 * k) * z ^ k =
      (w ^ 2 - w * r₁ + r₁ ^ 2) ^ n + (w ^ 2 - w * r₂ + r₂ ^ 2) ^ n +
        (w ^ 2 - w * r₃ + r₃ ^ 2) ^ n

/-- **Tribonacci formula for a diagonal sum of trinomial coefficients.**
Write $\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in
$(1 + t + t^2)^n$, and $T_n$ for the Tribonacci numbers, $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{n+3} = T_{n+2} + T_{n+1} + T_n$. Then for every $n \in \mathbb{N}$,

$$\sum_{k=0}^{n} \binom{n + k}{n - k}_2 = \frac{T_{2(n+1)}}{2} + \frac{1}{2}\binom{n}{n}_2 +
\frac{1}{2} \sum_{k=0}^{n-1} \binom{k}{k}_2 \left(T_{2(n-k)} + T_{2(n-1-k)}\right).$$

The sequence $(T_{2n})$ is the bisection A099463.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 42 (`jis-2025-25.3.5-cor-42`). -/
public theorem_wanted sum_trinomialCoefficient_add_sub_eq_tribonacci (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (trinomialCoefficient (n + k) (n - k) : ℚ) =
      (tribonacci (2 * (n + 1)) : ℚ) / 2 + (trinomialCoefficient n n : ℚ) / 2 +
        (∑ k ∈ Finset.range n, (trinomialCoefficient k k : ℚ) *
          ((tribonacci (2 * (n - k)) : ℚ) + tribonacci (2 * (n - 1 - k)))) / 2

/-- **Recovering even coefficients from the 2-Pascal transform.** Write $[t^m]F$ for the
coefficient of $t^m$ in a power series $F$. Let $S$, $Q$, $R$ be power series over $\mathbb{Q}$
with $S^2 = 4 - 3t^2$, $S(0) = 2$, $2Q^2 = 2 - t^2 - tS$, $Q(0) = 1$, $R^2 = 1 - t + t^2$ and
$R(0) = 1$, and put

$$\alpha = \frac{-2(2Q + t^2 S - t)}{Q(3t^4 + 2tS - t^2 - 4)}, \qquad
\beta = \frac{t(t + S)}{2(1 - t^2)}.$$

For a power series $f$ over $\mathbb{Q}$ let $g(t) = \alpha(t)\,f(\beta(t))$. Then for every
$n \in \mathbb{N}$,

$$[t^{2n}]\,f = [t^{2n}]\,\frac{(2 - t)(1 - t)^{2n}}{2(1 - t + t^2)}\,g\!\left(\frac{t}{R}\right).$$

Here $S$, $Q$, $R$ are the square roots $\sqrt{4 - 3t^2}$, $\sqrt{(2 - t^2 - tS)/2}$ and
$\sqrt{1 - t + t^2}$, and $\alpha$, $\beta$ are the series of the paper's Theorem 6.

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Corollary 49 (`jis-2025-25.3.5-cor-49`). -/
public theorem_wanted coeff_two_mul_eq_inverse_trinomial_transform (S Q R : PowerSeries ℚ)
    (hS : S ^ 2 = 4 - 3 * X ^ 2) (hS0 : constantCoeff S = 2)
    (hQ : 2 * Q ^ 2 = 2 - X ^ 2 - X * S) (hQ0 : constantCoeff Q = 1)
    (hR : R ^ 2 = 1 - X + X ^ 2) (hR0 : constantCoeff R = 1) (f : PowerSeries ℚ) (n : ℕ) :
    let α := -2 * (2 * Q + X ^ 2 * S - X) * (Q * (3 * X ^ 4 + 2 * X * S - X ^ 2 - 4))⁻¹
    let β := X * (X + S) * (2 * (1 - X ^ 2))⁻¹
    let g := α * f.subst β
    coeff (2 * n) f = coeff (2 * n) ((2 - X) * (1 - X) ^ (2 * n) * (2 * (1 - X + X ^ 2))⁻¹ *
      g.subst (X * R⁻¹))

end

end MetaMathlibExt
