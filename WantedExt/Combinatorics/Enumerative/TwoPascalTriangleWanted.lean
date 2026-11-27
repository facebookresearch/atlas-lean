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
public import MathlibExt.Combinatorics.Enumerative.ExtendedTrinomialAlternating
public import MathlibExt.Combinatorics.Enumerative.GouldTrinomialIdentities
public import MathlibExt.Combinatorics.Enumerative.RiordanArraySum
public import MathlibExt.Combinatorics.Enumerative.SprugnoliBinomialSum
public import MathlibExt.Combinatorics.Enumerative.TrinomialAlternatingColumn
public import MathlibExt.Combinatorics.Enumerative.TrinomialBinomialTransform
public import MathlibExt.Combinatorics.Enumerative.TrinomialConvolution
public import MathlibExt.Combinatorics.Enumerative.TrinomialEvenAlternating
public import MathlibExt.Combinatorics.Enumerative.TrinomialEvenGenerating
public import MathlibExt.Combinatorics.Enumerative.TrinomialInverseTransform
public import MathlibExt.Combinatorics.Enumerative.TrinomialOddGenerating
public import MathlibExt.Combinatorics.Enumerative.TrinomialUpperHalf
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

end

end MetaMathlibExt
