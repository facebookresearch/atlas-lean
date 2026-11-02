/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.Binomial
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Combinatorics.Enumerative.FubiniNumber
public import MathlibExt.Combinatorics.Enumerative.SignedStirlingFirst

/-!
# Extensions of some combinatorial identities

Statements from Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial
Identities and Various Related Results*, INTEGERS 25 (2025), Article A61.

`S(n, k)` is `Nat.stirlingSecond`, `s(n, k)` is `signedStirlingFirst`, `B_n` is `bernoulli`
(`B_1 = -1/2`), and the ordered Bell numbers `a(n)` are `fubiniNumber`. Binomial coefficients
with a complex upper argument are `Ring.choose`, rising factorials `x^{\overline{n}}` are
`(ascPochhammer ℂ n).eval x` and falling factorials `z^{\underline{n}}` are
`(descPochhammer ℂ n).eval z`. Theorems 2, 8 and 9, Corollaries 1 and 2 and Lemmas 1-3 are read
from the primary paper; the other statements follow the extracted records.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset Polynomial
open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry (chapter5EulerEven)

/-- **Alzer–Richards derivative identity for powers of $1 - f$.** Let $r, j, n \ge 0$ be
integers and let $f \colon \mathbb{R} \to \mathbb{R}$ be $r$ times continuously differentiable.
Writing $g^{(i)}$ for the $i$-th derivative of a function $g$ and taking powers of $f$ pointwise,
for every real $x$
$$
\sum_{k=0}^{n} (-1)^{k+1} \binom{n+1}{k+1} \bigl(f^{k+1+j}\bigr)^{(r)}(x) =
\sum_{k=0}^{r} \binom{r}{k} \bigl(f^j\bigr)^{(k)}(x) \,
\bigl((1-f)^{n+1} - 1\bigr)^{(r-k)}(x).
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 1, Equation (2). -/
theorem_wanted sum_iteratedDeriv_pow_one_sub {f : ℝ → ℝ} {r : ℕ} (hf : ContDiff ℝ r f)
    (j n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv r (fun y => f y ^ (k + 1 + j)) x =
      ∑ k ∈ range (r + 1), (r.choose k : ℝ) * iteratedDeriv k (fun y => f y ^ j) x *
        iteratedDeriv (r - k) (fun y => (1 - f y) ^ (n + 1) - 1) x

/-- **Alzer–Richards derivative identity for powers of $1 + f$.** Let $r, j, n \ge 0$ be
integers and let $f \colon \mathbb{R} \to \mathbb{R}$ be $r$ times continuously differentiable
with $f(y) \ne 0$ for every real $y$. Writing $g^{(i)}$ for the $i$-th derivative of a function
$g$ and taking integer powers of $f$ pointwise, for every real $x$
$$
\sum_{k=0}^{n} \binom{n+1}{k+1} \bigl(f^{k+1-j}\bigr)^{(r)}(x) =
\sum_{k=0}^{r} \binom{r}{k} \bigl(1/f^j\bigr)^{(k)}(x) \,
\bigl((1+f)^{n+1} - 1\bigr)^{(r-k)}(x).
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 1, Equation (3). -/
theorem_wanted sum_iteratedDeriv_zpow_one_add {f : ℝ → ℝ} {r : ℕ} (hf : ContDiff ℝ r f)
    (hf0 : ∀ y, f y ≠ 0) (j n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv r (fun y => f y ^ ((k : ℤ) + 1 - j)) x =
      ∑ k ∈ range (r + 1), (r.choose k : ℝ) * iteratedDeriv k (fun y => 1 / f y ^ j) x *
        iteratedDeriv (r - k) (fun y => (1 + f y) ^ (n + 1) - 1) x

/-- **Alternating Stirling sums with $\binom{n+1}{k+1}$ give Bernoulli numbers.** Write $S(n, k)$
for the Stirling numbers of the second kind and $B_n$ for the Bernoulli numbers, with
$B_1 = -1/2$. Let $n$ be a natural number. Then for every natural number $r \le n$,
$$
\sum_{k=0}^{n} (-1)^k \frac{\binom{n+1}{k+1}}{\binom{r+k}{k}} S(r+k, k) = B_r,
$$
and
$$
\sum_{k=0}^{n} (-1)^k \frac{\binom{n+1}{k+1}}{\binom{n+1+k}{k}} S(n+1+k, k) =
B_{n+1} - (-1/2)^{n+1} (n+1)!.
$$

The case $r = n$ is Muthumalai's formula.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 2, Equation (4). -/
theorem_wanted sum_choose_div_choose_mul_stirlingSecond_eq_bernoulli (n : ℕ) :
    (∀ r ≤ n, ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
        (((n + 1).choose (k + 1) : ℚ) / ((r + k).choose k : ℚ)) *
          (Nat.stirlingSecond (r + k) k : ℚ) = bernoulli r) ∧
      ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k *
          (((n + 1).choose (k + 1) : ℚ) / ((n + 1 + k).choose k : ℚ)) *
            (Nat.stirlingSecond (n + 1 + k) k : ℚ) =
        bernoulli (n + 1) - (-1 / 2 : ℚ) ^ (n + 1) * ((n + 1).factorial : ℚ)

/-- **Vanishing alternating Stirling sums with $\binom{r+m}{k}$.** Write $S(n, k)$ for the
Stirling numbers of the second kind. For every natural number $m \ge 1$ and every natural number
$r$,
$$
\sum_{k=0}^{r+m} (-1)^k \frac{\binom{r+m}{k}}{\binom{r+k}{k}} S(r+k, k) = 0.
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 3, Equation (5). -/
theorem_wanted sum_choose_div_choose_mul_stirlingSecond_eq_zero {m : ℕ} (hm : 1 ≤ m)
    (r : ℕ) :
    ∑ k ∈ range (r + m + 1), (-1 : ℚ) ^ k *
        (((r + m).choose k : ℚ) / ((r + k).choose k : ℚ)) *
          (Nat.stirlingSecond (r + k) k : ℚ) = 0

/-- **Alternating Stirling sums with $\binom{n+1}{k+2}$.** Write $S(n, k)$ for the Stirling
numbers of the second kind and $B_n$ for the Bernoulli numbers, with $B_1 = -1/2$. Let
$n \ge 1$ be a natural number. Then for every natural number $r$ with $1 \le r \le n$,
$$
\sum_{k=0}^{n-1} (-1)^k \frac{\binom{n+1}{k+2}}{\binom{r+k}{k}} S(r+k, k) =
r B_{r-1} + (n + r) B_r,
$$
and
$$
\sum_{k=0}^{n-1} (-1)^k \frac{\binom{n+1}{k+2}}{\binom{n+1+k}{k}} S(n+1+k, k) =
(-1/2)^{n+1} (n+1)! + (n+1) B_n + (2n+1) B_{n+1}.
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 4, Equation (6). -/
theorem_wanted sum_choose_add_two_div_choose_mul_stirlingSecond {n : ℕ} (hn : 1 ≤ n) :
    (∀ r, 1 ≤ r → r ≤ n → ∑ k ∈ range n, (-1 : ℚ) ^ k *
        (((n + 1).choose (k + 2) : ℚ) / ((r + k).choose k : ℚ)) *
          (Nat.stirlingSecond (r + k) k : ℚ) = r * bernoulli (r - 1) + (n + r) * bernoulli r) ∧
      ∑ k ∈ range n, (-1 : ℚ) ^ k *
          (((n + 1).choose (k + 2) : ℚ) / ((n + 1 + k).choose k : ℚ)) *
            (Nat.stirlingSecond (n + 1 + k) k : ℚ) =
        (-1 / 2 : ℚ) ^ (n + 1) * ((n + 1).factorial : ℚ) + (n + 1) * bernoulli n +
          (2 * n + 1) * bernoulli (n + 1)

/-- **Alternating sums of signed Stirling numbers of the first kind.** Write $s(n, k)$ for the
signed Stirling numbers of the first kind. For all natural numbers $j$ and $n$ and every natural
number $r \le n$,
$$
\sum_{k=0}^{n+1} (-1)^k \frac{\binom{n+1}{k}}{\binom{k+j+r}{r}} s(k+j+r, k+j) = 0,
$$
and
$$
\sum_{k=0}^{n+1} (-1)^k \frac{\binom{n+1}{k}}{\binom{k+j+n+1}{n+1}} s(k+j+n+1, k+j) =
\frac{(n+1)!}{2^{n+1}}.
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 5, Equation (7). -/
theorem_wanted sum_choose_div_choose_mul_signedStirlingFirst (j n : ℕ) :
    (∀ r ≤ n, ∑ k ∈ range (n + 2), (-1 : ℚ) ^ k *
        (((n + 1).choose k : ℚ) / ((k + j + r).choose r : ℚ)) *
          (signedStirlingFirst (k + j + r) (k + j) : ℚ) = 0) ∧
      ∑ k ∈ range (n + 2), (-1 : ℚ) ^ k *
          (((n + 1).choose k : ℚ) / ((k + j + n + 1).choose (n + 1) : ℚ)) *
            (signedStirlingFirst (k + j + n + 1) (k + j) : ℚ) =
        ((n + 1).factorial : ℚ) / 2 ^ (n + 1)

/-- **Alzer–Richards identity for Euler numbers.** Let $n \ge 1$ be an integer. For integers
$k, i \ge 0$ let $T(k, i) = 2^{-k} \sum_{j=0}^{k} \binom{k}{j} (k-2j)^i$ (with $0^0 = 1$), and
let $E_k$ be the Euler numbers: $E_k = 0$ for odd $k$, and for even $k$ they are given by
$E_0 = 1$ and $E_{2m} = -\sum_{s=0}^{m-1} \binom{2m}{2s} E_{2s}$ for $m \ge 1$. Then
$$
\sum_{k=0}^{n-1} \binom{n}{k} E_k \sum_{\nu=0}^{n+1} \binom{n+1}{\nu} T(\nu, n-k) +
(2^{n+1} - 1) E_n = \sum_{k=0}^{n} \binom{n+1}{k+1} T(k, n).
$$

With these conventions $1/\cosh x = \sum_{k \ge 0} E_k x^k / k!$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 6. -/
theorem_wanted sum_eulerNumber_mul_sum_centralPowerSum {n : ℕ} (hn : 1 ≤ n)
    (T : ℕ → ℕ → ℚ)
    (hT : ∀ k n, T k n = (∑ j ∈ range (k + 1), (k.choose j : ℚ) * ((k : ℚ) - 2 * j) ^ n) / 2 ^ k) :
    ∑ k ∈ range n, (n.choose k : ℚ) * ((if k % 2 = 1 then 0 else chapter5EulerEven (k / 2) : ℤ) : ℚ) *
        ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℚ) * T ν (n - k) +
      (2 ^ (n + 1) - 1) * ((if n % 2 = 1 then 0 else chapter5EulerEven (n / 2) : ℤ) : ℚ) =
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℚ) * T k n

/-- **Alzer–Richards identity for Fubini numbers.** Let $n \ge 1$ be an integer, let $a(k)$ be
the $k$-th Fubini (ordered Bell) number and $S(r, j)$ the Stirling numbers of the second kind,
and for integers $r, k \ge 0$ let
$A(r, k) = \sum_{j=0}^{k} (-1)^j \binom{k}{j} j! \, S(r, j)$. Then
$$
\sum_{k=0}^{n-1} \binom{n}{k} a(k) \sum_{\nu=0}^{n+1} \binom{n+1}{\nu} A(n-k, \nu) +
(2^{n+1} - 1) a(n) = \sum_{k=0}^{n} \binom{n+1}{k+1} A(n, k).
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 7, Equation (8). -/
theorem_wanted sum_fubiniNumber_mul_sum_alternatingStirling {n : ℕ} (hn : 1 ≤ n)
    (A : ℕ → ℕ → ℤ)
    (hA : ∀ r k, A r k = ∑ j ∈ range (k + 1),
      (-1 : ℤ) ^ j * (k.choose j : ℤ) * (j.factorial : ℤ) * (Nat.stirlingSecond r j : ℤ)) :
    ∑ k ∈ range n, (n.choose k : ℤ) * fubiniNumber k *
        ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℤ) * A (n - k) ν +
      (2 ^ (n + 1) - 1) * fubiniNumber n =
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℤ) * A n k

/-- **Sabar's identity for complex arguments.** For a complex number $w$ and a natural number $j$
write $\binom{w}{j} = w(w-1)\cdots(w-j+1)/j!$. For every natural number $p \ge 1$ and every
complex number $z$,
$$
z^p - z(z-1)\cdots(z-p+1) =
\sum_{k=0}^{p-1} (-1)^{p-k-1} k^p \binom{z}{k} \binom{z-k-1}{p-k-1}.
$$

Sabar proved this formula for natural numbers $z = n \ge p$; here it is extended to complex $z$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 8, Equation (9). -/
theorem_wanted pow_sub_descPochhammer_eq_sum_choose {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    z ^ p - (descPochhammer ℂ p).eval z =
      ∑ k ∈ range p, (-1 : ℂ) ^ (p - k - 1) * (k : ℂ) ^ p * Ring.choose z k *
        Ring.choose (z - k - 1) (p - k - 1)

/-- **A reciprocal-sum identity for generalized binomial coefficients.** For a complex number $w$
and a natural number $j$ write $\binom{w}{j} = w(w-1)\cdots(w-j+1)/j!$. Let $p \ge 1$ be a
natural number and let $z$ be a complex number with $z \ne k$ for every natural number $k < p$.
Then
$$
p z^{p-1} - z^p \sum_{k=0}^{p-1} \frac{1}{z-k} =
\sum_{k=0}^{p-1} \frac{(-1)^{p-k} k^p}{z-k} \binom{z}{k} \binom{z-k-1}{p-k-1}.
$$

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 1, Equation (10). -/
theorem_wanted mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose {p : ℕ} (hp : 1 ≤ p) {z : ℂ}
    (hz : ∀ k < p, z ≠ k) :
    p * z ^ (p - 1) - z ^ p * ∑ k ∈ range p, 1 / (z - k) =
      ∑ k ∈ range p, (-1 : ℂ) ^ (p - k) * (k : ℂ) ^ p / (z - k) * Ring.choose z k *
        Ring.choose (z - k - 1) (p - k - 1)

/-- **The Alzer–Richards binomial sum as a ${}_3F_2$ series.** Let $m \ge 1$ be an integer and
let $p, x$ be complex numbers with $p \ne -j$ and $x \ne -j$ for every integer $j$ with
$1 \le j \le \lfloor m/2 \rfloor$. Write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex $z$
and $(z)_n = z(z+1)\cdots(z+n-1)$ for the rising factorial. Then
$$
\sum_{k=0}^{\lfloor m/2 \rfloor} \frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k+p}{k}} =
\frac{(x+1)_m}{m!} \sum_{n=0}^{\lfloor m/2 \rfloor}
\frac{(-m/2)_n \, ((1-m)/2)_n}{(p+1)_n \, (x+1)_n}.
$$

The sum on the right is the terminating hypergeometric series
${}_3F_2(-m/2, (1-m)/2, 1; p+1, x+1; 1)$, written out up to $n = \lfloor m/2 \rfloor$, beyond
which its terms vanish.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 9 (i), Equation (15). -/
theorem_wanted sum_choose_mul_choose_div_choose_eq_hypergeometric3F2 {m : ℕ} (hm : 1 ≤ m)
    {p x : ℂ} (hp : ∀ j : ℕ, 1 ≤ j → j ≤ m / 2 → p ≠ -j)
    (hx : ∀ j : ℕ, 1 ≤ j → j ≤ m / 2 → x ≠ -j) :
    ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
        (2 ^ (2 * k) * Ring.choose ((k : ℂ) + p) k) =
      (ascPochhammer ℂ m).eval (x + 1) / (m.factorial : ℂ) *
        ∑ n ∈ range (m / 2 + 1), (ascPochhammer ℂ n).eval (-(m : ℂ) / 2) *
          (ascPochhammer ℂ n).eval ((1 - (m : ℂ)) / 2) /
            ((ascPochhammer ℂ n).eval (p + 1) * (ascPochhammer ℂ n).eval (x + 1))

/-- **A binomial sum as a terminating ${}_2F_1$ series.** Write
$x^{\overline{n}} = x(x+1)\cdots(x+n-1)$ for the rising factorial of a complex number $x$, and
$\binom{w}{k} = w(w-1)\cdots(w-k+1)/k!$ for a complex number $w$ and a natural number $k$. Let
$m$ and $\nu$ be natural numbers with $1 \le \nu \le \lfloor m/2 \rfloor$, and let $p$ be a
complex number with $p \ne -j$ for every natural number $j$ with $1 \le j \le \lfloor m/2 \rfloor$.
Then
$$
\sum_{k=0}^{\lfloor m/2 \rfloor} \frac{\binom{m-k}{k} \binom{m-\nu}{m-k}}{2^{2k} \binom{k+p}{k}} =
\frac{(m-\nu)!}{2^{2\nu} \, m!} \cdot \frac{(-m)^{\overline{2\nu}}}{(p+1)^{\overline{\nu}}}
\sum_{n=0}^{\lfloor m/2 \rfloor - \nu}
\frac{(\nu - m/2)^{\overline{n}} \, (\nu - (m-1)/2)^{\overline{n}}}
{(\nu + p + 1)^{\overline{n}} \, n!}.
$$

The last sum is the terminating hypergeometric series
${}_2F_1(\nu - m/2, \nu - (m-1)/2; \nu + p + 1; 1)$, whose terms vanish beyond
$n = \lfloor m/2 \rfloor - \nu$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 9 (ii), Equation (16). -/
theorem_wanted sum_choose_mul_choose_div_choose_eq_hypergeometric2F1 {m ν : ℕ} (hν : 1 ≤ ν)
    (hνm : ν ≤ m / 2) {p : ℂ} (hp : ∀ j : ℕ, 1 ≤ j → j ≤ m / 2 → p ≠ -j) :
    ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * ((m - ν).choose (m - k) : ℂ) /
        (2 ^ (2 * k) * Ring.choose ((k : ℂ) + p) k) =
      ((m - ν).factorial : ℂ) / (2 ^ (2 * ν) * (m.factorial : ℂ)) *
        ((ascPochhammer ℂ (2 * ν)).eval (-(m : ℂ)) / (ascPochhammer ℂ ν).eval (p + 1)) *
        ∑ n ∈ range (m / 2 - ν + 1), (ascPochhammer ℂ n).eval ((ν : ℂ) - m / 2) *
          (ascPochhammer ℂ n).eval ((ν : ℂ) - ((m : ℂ) - 1) / 2) /
            ((ascPochhammer ℂ n).eval ((ν : ℂ) + p + 1) * (n.factorial : ℂ))

/-- **Closed form of the Alzer–Richards binomial sum for even $m$.** Let $m \ge 2$ be an even
integer and $x$ a complex number, and write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex
$z$. Put
$$
S(x) = \sum_{k=0}^{m/2} \frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k-m/2-1/2}{k}}.
$$
If $x \ne -m/2$, then $S(x) = \frac{x}{x+m/2} \binom{x+m}{m}$; if $x = -m/2$, then
$S(x) = \frac{(-1)^{m/2}}{2^m \binom{(m-1)/2}{m/2}}$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 2 (i), Equation (19). -/
theorem_wanted sum_choose_mul_choose_div_choose_of_even {m : ℕ} (hm : 2 ≤ m) (hme : Even m)
    (x : ℂ) :
    (x ≠ -(m : ℂ) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m / 2 - 1 / 2) k) =
        x / (x + m / 2) * Ring.choose (x + m) m) ∧
    (x = -(m : ℂ) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m / 2 - 1 / 2) k) =
        (-1 : ℂ) ^ (m / 2) / (2 ^ m * Ring.choose (((m : ℂ) - 1) / 2) (m / 2)))

/-- **Closed form of the Alzer–Richards binomial sum for odd $m$.** Let $m$ be an odd positive
integer and $x$ a complex number, and write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex
$z$. Put
$$
S(x) = \sum_{k=0}^{(m-1)/2} \frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k-m/2-1}{k}}.
$$
If $x \ne (1-m)/2$, then $S(x) = \frac{x}{x+(m-1)/2} \binom{x+m}{m}$; if $x = (1-m)/2$, then
$S(x) = \frac{(-1)^{(m-1)/2} (m+1)}{2^m \binom{m/2}{(m-1)/2}}$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 2 (ii), Equation (20). -/
theorem_wanted sum_choose_mul_choose_div_choose_of_odd {m : ℕ} (hmo : Odd m) (x : ℂ) :
    (x ≠ (1 - (m : ℂ)) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m / 2 - 1) k) =
        x / (x + ((m : ℂ) - 1) / 2) * Ring.choose (x + m) m) ∧
    (x = (1 - (m : ℂ)) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m / 2 - 1) k) =
        (-1 : ℂ) ^ ((m - 1) / 2) * (m + 1) / (2 ^ m * Ring.choose ((m : ℂ) / 2) ((m - 1) / 2)))

/-- **Closed form of the shifted Alzer–Richards binomial sum.** Let $m \ge 1$ be an integer and
$x$ a complex number, write $\binom{z}{k} = z(z-1)\cdots(z-k+1)/k!$ for complex $z$, and assume
$\binom{k-m+1/2-x}{k} \ne 0$ for $0 \le k \le \lfloor m/2 \rfloor$. Put
$$
S(x) = \sum_{k=0}^{\lfloor m/2 \rfloor}
\frac{\binom{m-k}{k} \binom{m+x}{m-k}}{2^{2k} \binom{k-m+1/2-x}{k}}.
$$
If $x \ne -m/2$ and $x \ne (1-m)/2$, then
$S(x) = \frac{x (x+m-1/2)}{(x+m/2)(x+(m-1)/2)} \binom{x+m}{m}$. If $m$ is even and
$x = -m/2$, then $S(x) = \frac{(-1)^{m/2}}{2^m \binom{(m-3)/2}{m/2}}$. If $m$ is odd and
$x = (1-m)/2$, then $S(x) = \frac{(-1)^{(m-1)/2} (m+1)}{2^m \binom{m/2-1}{(m-1)/2}}$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 2 (iii), Equation (21). -/
theorem_wanted sum_choose_mul_choose_div_choose_shifted {m : ℕ} (hm : 1 ≤ m) {x : ℂ}
    (hx : ∀ k ≤ m / 2, Ring.choose ((k : ℂ) - m + 1 / 2 - x) k ≠ 0) :
    (x ≠ -(m : ℂ) / 2 → x ≠ (1 - (m : ℂ)) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m + 1 / 2 - x) k) =
        x * (x + m - 1 / 2) / ((x + m / 2) * (x + ((m : ℂ) - 1) / 2)) *
          Ring.choose (x + m) m) ∧
    (Even m → x = -(m : ℂ) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m + 1 / 2 - x) k) =
        (-1 : ℂ) ^ (m / 2) / (2 ^ m * Ring.choose (((m : ℂ) - 3) / 2) (m / 2))) ∧
    (Odd m → x = (1 - (m : ℂ)) / 2 →
      ∑ k ∈ range (m / 2 + 1), ((m - k).choose k : ℂ) * Ring.choose ((m : ℂ) + x) (m - k) /
          (2 ^ (2 * k) * Ring.choose ((k : ℂ) - m + 1 / 2 - x) k) =
        (-1 : ℂ) ^ ((m - 1) / 2) * (m + 1) /
          (2 ^ m * Ring.choose ((m : ℂ) / 2 - 1) ((m - 1) / 2)))

/-- **Derivatives at zero of powers of $(1 - e^x)/x$.** Write $S(n, k)$ for the Stirling numbers
of the second kind. Let $f : \mathbb{R} \to \mathbb{R}$ satisfy $f(0) = -1$ and
$f(x) = (1 - e^x)/x$ for every $x \ne 0$. Then for all natural numbers $k$ and $r$, the $r$-th
derivative of $f^k$ at $0$ equals $(-1)^k S(r+k, k) / \binom{r+k}{k}$.

This is the expansion recorded in Gradshteyn and Ryzhik, p. 1047.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 1. -/
theorem_wanted iteratedDeriv_pow_one_sub_exp_div_self_zero {f : ℝ → ℝ} (hf0 : f 0 = -1)
    (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (k r : ℕ) :
    iteratedDeriv r (fun x => f x ^ k) 0 =
      (-1 : ℝ) ^ k * (Nat.stirlingSecond (r + k) k : ℝ) / ((r + k).choose k : ℝ)

/-- **Derivatives of $x/(1 - e^x)$ at zero.** Write $B_k$ for the $k$-th Bernoulli number,
with the convention $B_1 = -1/2$. Let $f : \mathbb{R} \to \mathbb{R}$ satisfy $f(0) = -1$ and
$f(x) = (1 - e^x)/x$ for every $x \ne 0$. Then for every natural number $k$, the $k$-th
derivative of $1/f$ at $0$ equals $-B_k$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 2. -/
theorem_wanted iteratedDeriv_inv_one_sub_exp_div_self_zero {f : ℝ → ℝ} (hf0 : f 0 = -1)
    (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (k : ℕ) :
    iteratedDeriv k (fun x => 1 / f x) 0 = -(bernoulli k : ℝ)

/-- **Derivatives at zero of $(1 + (1 - e^x)/x)^{n+1}$.** Let $f : \mathbb{R} \to \mathbb{R}$
satisfy $f(0) = -1$ and $f(x) = (1 - e^x)/x$ for every $x \ne 0$, and let $n$ be a natural
number. Then for every natural number $r \le n$, the $r$-th derivative of $(1 + f)^{n+1}$ at $0$
is $0$, and the $(n+1)$-th derivative of $(1 + f)^{n+1}$ at $0$ equals $(-1/2)^{n+1} (n+1)!$.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 3, Equation (26). -/
theorem_wanted iteratedDeriv_one_add_one_sub_exp_div_self_pow_zero {f : ℝ → ℝ}
    (hf0 : f 0 = -1) (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (n : ℕ) :
    (∀ r ≤ n, iteratedDeriv r (fun x => (1 + f x) ^ (n + 1)) 0 = 0) ∧
      iteratedDeriv (n + 1) (fun x => (1 + f x) ^ (n + 1)) 0 =
        (-1 / 2 : ℝ) ^ (n + 1) * ((n + 1).factorial : ℝ)

end

end MetaMathlibExt
