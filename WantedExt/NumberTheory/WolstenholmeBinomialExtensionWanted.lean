/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Binomial
public import MathlibExt.NumberTheory.HigherOrderHarmonic

/-!
# Extensions of Wolstenholme's theorem by binomial coefficients

Statements from Kehila's INTEGERS paper on `binom(np, kp)` modulo powers of `p`.
A rational congruence `x ≡ y (mod p^s)` (both sides `p`-integral) is written
`x - y = 0 ∨ s ≤ padicValRat p (x - y)`. The generalized harmonic numbers
`H_{p-1}(s) = ∑_{j=1}^{p-1} j^{-s}` are `higherHarmonic (p - 1) s`, and the
multiple harmonic sum `H_{p-1}(1, 1) = ∑_{1 ≤ i < j ≤ p-1} 1 / (i j)` is written
out with a strict inner range. Where the modulus is `p^{s + v_p(B)}` with an integer
`B`, the congruence is `X = 0 ∨ (B ≠ 0 ∧ s + padicValRat p B ≤ padicValRat p X)`, so
`B = 0` (`v_p(B) = ∞`) demands equality. The higher `p`-adic mean value theorem is stated
over `K = ℚ_p` for an ultrametric normed `ℚ_p`-space `B`.
-/

namespace MetaMathlibExt

open Polynomial

@[expose] public section

/-- **Coefficients of $(x + 1)^{jp} (x^p + 1)^{n-j}$.** Let $n$, $j$ and $k$ be natural numbers and
$p$ a positive integer, and let $d = \max(n - j, 0)$. Then the coefficient of $x^{kp}$ in the
polynomial $(x + 1)^{jp} (x^p + 1)^{d}$ is
$$\sum_{s=0}^{\min(j, k)} \binom{jp}{sp} \binom{d}{k - s}.$$

The source takes $p$ prime; here $p$ is any positive integer.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 2
(`integers-2026-A32-lem-2`). -/
public theorem_wanted coeff_add_one_pow_mul_X_pow_add_one_pow (p n j k : ℕ) (hp : 0 < p) :
    ((X + 1 : ℕ[X]) ^ (j * p) * (X ^ p + 1) ^ (n - j)).coeff (k * p) =
      ∑ s ∈ Finset.range (j + 1),
        if s ≤ k then (j * p).choose (s * p) * (n - j).choose (k - s) else 0

/-- **Binomial coefficients with upper index $-np$.** Let $p$, $n$ and $k$ be natural numbers
with $p \ge 1$ and $k \ge 1$. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$. Then
$$
\binom{-np}{kp} = (-1)^{kp} \, \frac{n}{k} \binom{(n+k)p - 1}{kp - 1} =
(-1)^{kp} \, \frac{n}{n+k} \binom{(n+k)p}{kp}.
$$

The paper takes $p$ prime.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 5
(`integers-2026-A32-lem-5`). -/
public theorem_wanted ringChoose_neg_mul_mul_eq (p n k : ℕ) (hp : 0 < p) (hk : 1 ≤ k) :
    ((Ring.choose (-((n * p : ℕ) : ℤ)) (k * p) : ℤ) : ℚ) =
        (-1) ^ (k * p) * ((n : ℚ) / k) * (((n + k) * p - 1).choose (k * p - 1) : ℚ) ∧
      ((Ring.choose (-((n * p : ℕ) : ℤ)) (k * p) : ℤ) : ℚ) =
        (-1) ^ (k * p) * ((n : ℚ) / (n + k)) * (((n + k) * p).choose (k * p) : ℚ)

/-- **Congruences for $\binom{tp}{p}$ modulo $p^5$, $p^6$ and $p^7$.** Let $p \ge 11$ be a prime
and $t$ a natural number. Write $H_{p-1}^{(r)} = \sum_{j=1}^{p-1} 1/j^r$ for the harmonic number of
order $r$ and $H_{p-1}(1, 1) = \sum_{1 \le i < j \le p-1} 1/(ij)$. For rational numbers $x$, $y$
and a natural number $s$, write $x \equiv y \pmod{p^s}$ when $x = y$ or $v_p(x - y) \ge s$, where
$v_p$ is the $p$-adic valuation on $\mathbb{Q}$. Then
$$\binom{tp}{p} \equiv t + (-t^5 + 2t^4 - t^2) \, p \, H_{p-1}^{(1)} +
t^3 (t-1)^2 p^2 H_{p-1}(1, 1) \pmod{p^7},$$
$$\binom{tp}{p} \equiv t + (-t^5 + 2t^4 - t^2) \, p \, H_{p-1}^{(1)} -
\frac{t^3 (t-1)^2}{2} \, p^2 H_{p-1}^{(2)} \pmod{p^6},$$
and
$$\binom{tp}{p} \equiv t + t^2 (t-1) \, p \, H_{p-1}^{(1)} \pmod{p^5}.$$

The double sum $H_{p-1}(1, 1)$ is taken over $i < j$; under this reading the first two
congruences agree modulo $p^6$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 10
(`integers-2026-A32-thm-10`). -/
public theorem_wanted choose_mul_prime_prime_harmonic_congr (p t : ℕ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let H1 : ℚ := higherHarmonic (p - 1) 1
    let H2 : ℚ := higherHarmonic (p - 1) 2
    let H11 : ℚ := ∑ j ∈ Finset.Icc 1 (p - 1), ∑ i ∈ Finset.Ico 1 j, 1 / ((i : ℚ) * j)
    let T : ℚ := t
    let B : ℚ := ((t * p).choose p : ℚ)
    (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 + T ^ 3 * (T - 1) ^ 2 * p ^ 2 * H11) = 0 ∨
        7 ≤ padicValRat p
          (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 + T ^ 3 * (T - 1) ^ 2 * p ^ 2 * H11))) ∧
      (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 - T ^ 3 * (T - 1) ^ 2 / 2 * p ^ 2 * H2) = 0 ∨
        6 ≤ padicValRat p
          (B - (T + (-T ^ 5 + 2 * T ^ 4 - T ^ 2) * p * H1 - T ^ 3 * (T - 1) ^ 2 / 2 * p ^ 2 * H2))) ∧
      (B - (T + T ^ 2 * (T - 1) * p * H1) = 0 ∨
        5 ≤ padicValRat p (B - (T + T ^ 2 * (T - 1) * p * H1)))

/-- **Congruences modulo $p^7$ for $\binom{\alpha p - 1}{p - 1} \binom{(\alpha + 1)p - 1}{p - 1}$
and $\binom{2p - 1}{p - 1}^{-1}$.** Let $p \ge 11$ be a prime and let $\alpha$ be an integer. For
an integer $x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, let
$H_{p-1}^{(r)} = \sum_{j=1}^{p-1} 1/j^r$ be the harmonic number of order $r$, and let $v_p$ be the
$p$-adic valuation on $\mathbb{Q}$. Put
$$
X = \binom{\alpha p - 1}{p - 1} \binom{(\alpha + 1)p - 1}{p - 1} - 1 +
(\alpha p)^2 H_{p-1}^{(2)} - \frac{(\alpha p)^4}{2} \Big(\big(H_{p-1}^{(2)}\big)^2 -
H_{p-1}^{(4)}\Big)
$$
and
$$
Y = \binom{2p - 1}{p - 1}^{-1} - 1 - p^2 H_{p-1}^{(2)} -
\frac{p^4}{2} \Big(\big(H_{p-1}^{(2)}\big)^2 + H_{p-1}^{(4)}\Big).
$$
Then either $X = 0$ or $v_p(X) \ge 7$, and either $Y = 0$ or $v_p(Y) \ge 7$.

The paper allows $\alpha \in \mathbb{Z}_p$; only integers $\alpha$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 13
(`integers-2026-A32-thm-13`). -/
public theorem_wanted ringChoose_mul_prime_sub_one_mul_congr (p : ℕ) (α : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let H2 : ℚ := higherHarmonic (p - 1) 2
    let H4 : ℚ := higherHarmonic (p - 1) 4
    let A : ℚ := α * p
    let L : ℚ := ((Ring.choose (α * p - 1) (p - 1) : ℤ) : ℚ) *
      ((Ring.choose ((α + 1) * p - 1) (p - 1) : ℤ) : ℚ)
    let R : ℚ := ((2 * p - 1).choose (p - 1) : ℚ)⁻¹
    (L - (1 - A ^ 2 * H2 + A ^ 4 / 2 * (H2 ^ 2 - H4)) = 0 ∨
        7 ≤ padicValRat p (L - (1 - A ^ 2 * H2 + A ^ 4 / 2 * (H2 ^ 2 - H4)))) ∧
      (R - (1 + (p : ℚ) ^ 2 * H2 + (p : ℚ) ^ 4 / 2 * (H2 ^ 2 + H4)) = 0 ∨
        7 ≤ padicValRat p (R - (1 + (p : ℚ) ^ 2 * H2 + (p : ℚ) ^ 4 / 2 * (H2 ^ 2 + H4))))

/-! ### Higher `p`-adic mean value theorem -/

/-- **Coefficient bound for the divided derivatives $D^n/n!$.** Let $p$ be a prime and $B$ a
normed vector space over $\mathbb{Q}_p$ whose norm is ultrametric. Let $(a_k)_{k \ge 0}$ be a
sequence in $B$ and $C$ a real number with $\|a_k\| \le C$ for every $k$. Then for all natural
numbers $n$ and $k$,
$$\Big\| \binom{k+n}{n} a_{k+n} \Big\| \le C.$$

The vectors $\binom{k+n}{n} a_{k+n}$ are the coefficients of $D^n f / n!$ for
$f = \sum_k a_k t^k$, so this is the coefficientwise form of the bound $\|D^n / n!\| \le 1$ on
the Tate algebra $B\{t\}$ with the sup norm.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 1
(`integers-2026-A32-lem-1`). -/
public theorem_wanted norm_choose_nsmul_coeff_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (a : ℕ → B) (C : ℝ)
    (hC : ∀ k, ‖a k‖ ≤ C) (n k : ℕ) :
    ‖(k + n).choose n • a (k + n)‖ ≤ C

/-- **Higher $p$-adic mean value theorem.** Let $p$ be a prime, let $|\cdot|$ be the $p$-adic
absolute value on $\mathbb{Q}_p$, and let $B$ be a normed vector space over $\mathbb{Q}_p$ whose
norm is ultrametric. Let $N$ and $m$ be natural numbers with $1 \le m \le p$, let
$f(t) = \sum_{j<N} a_j t^j$ be a polynomial with coefficients $a_j \in B$, and let
$t, h \in \mathbb{Q}_p$ with $|t| \le 1$. Suppose that $|h| \le p^{-1/(p-m)}$ if $m < p$, that
$|h| \le p^{-1/p}$ if $m = p$, and that $C \ge 0$ is a real number with
$\|j(j-1)\cdots(j-m+1) \, a_j\| \le C$ for every $j < N$. Then
$$\Big\| f(t+h) - \sum_{q<m} \sum_{q \le j < N} \binom{j}{q} t^{j-q} h^q a_j \Big\| \le
\Big| \frac{h^m}{m} \Big| \, C.$$

The inner sum $\sum_{q \le j < N} \binom{j}{q} t^{j-q} a_j$ is $f^{(q)}(t)/q!$, and the least
admissible $C$ is the sup of the norms of the coefficients of $f^{(m)}$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 1
(`integers-2026-A32-thm-1`). -/
public theorem_wanted norm_sub_taylor_le_of_norm_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (C : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hh₁ : m < p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - m))))
    (hh₂ : m = p → ‖h‖ ≤ (p : ℝ) ^ (-(1 / (p : ℝ))))
    (hC₀ : 0 ≤ C) (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ C) :
    ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖ ≤
      ‖h ^ m / (m : ℚ_[p])‖ * C

/-- **Congruence form of the higher $p$-adic mean value theorem.** Let $p$ be a prime, let
$|\cdot|$ be the $p$-adic absolute value on $\mathbb{Q}_p$, and let $B$ be a normed vector space
over $\mathbb{Q}_p$ whose norm is ultrametric. Let $N$ and $m$ be natural numbers with
$1 \le m \le p$, let $f(t) = \sum_{j<N} a_j t^j$ with $a_j \in B$, let $t, h \in \mathbb{Q}_p$
with $|t| \le 1$, and let $w$ be a real number with
$\|j(j-1)\cdots(j-m+1) \, a_j\| \le p^{-w}$ for every $j < N$. Write
$$R = \Big\| f(t+h) - \sum_{q<m} \sum_{q \le j < N} \binom{j}{q} t^{j-q} h^q a_j \Big\|$$
and let $v_p(h)$ be the $p$-adic valuation of $h$, taken to be $0$ when $h = 0$. Then
$R \le p^{-(m v_p(h) + w)}$ if $m < p$ and $v_p(h) \ge 1/(p-m)$;
$R \le p^{-(p v_p(h) + w - 1)}$ if $m = p$ and $v_p(h) \ge 1/p$; and $R = 0$ if $h = 0$.

Reading a congruence modulo $p^v$ in $B$ as norm at most $p^{-v}$, the first two bounds say
$f(t+h) \equiv \sum_{q<m} f^{(q)}(t) h^q / q!$ modulo $p^{m v_p(h) + w}$ and
$p^{p v_p(h) + w - 1}$ respectively.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 2
(`integers-2026-A32-thm-2`). -/
public theorem_wanted norm_sub_taylor_le_zpow_valuation {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (w : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ (p : ℝ) ^ (-w)) :
    let R : ℝ := ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖
    (m < p → 1 / ((p : ℝ) - m) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((m : ℝ) * h.valuation + w))) ∧
      (m = p → 1 / (p : ℝ) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((p : ℝ) * h.valuation + w - 1))) ∧
      (h = 0 → R = 0)

/-! ### The general congruence for `binom(np, kp)` -/

/-- **Alternating binomial sum identities.** For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$ for the generalized binomial coefficient. Let $m$, $n$
and $k$ be natural numbers. Then for every natural number $j \le m$,
$$\sum_{s=j}^{m} (-1)^{s-j} \binom{n}{s} \binom{s}{j} = (-1)^{m-j} \binom{n}{j} \binom{n-j-1}{m-j}
= \binom{n}{j} \binom{m-n}{m-j},$$
and
$$\sum_{j=0}^{m} (-1)^{m-j} \binom{n}{j} \binom{n-j-1}{m-j} \binom{n-j}{k} =
\binom{n}{k} \binom{m-k}{m},$$
$$\sum_{j=0}^{\min(m, k)} (-1)^{m-j} \binom{n}{j} \binom{n-j-1}{m-j} \binom{n-j}{k-j} =
\binom{n}{k} \binom{k+m-n}{m}.$$

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 3
(`integers-2026-A32-lem-3`). -/
public theorem_wanted alternating_choose_sum_identities (m n k : ℕ) :
    let C : ℤ → ℕ → ℤ := fun x r => Ring.choose x r
    (∀ j ≤ m, ∑ s ∈ Finset.Icc j m, (-1 : ℤ) ^ (s - j) * C n s * C s j =
          (-1) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) ∧
        (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) =
          C n j * C ((m : ℤ) - n) (m - j)) ∧
      ∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) * C ((n : ℤ) - j) k =
        C n k * C ((m : ℤ) - k) m ∧
      ∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) *
            (if j ≤ k then C ((n : ℤ) - j) (k - j) else 0) =
        C n k * C ((k : ℤ) + m - n) m

/-- **The general congruence for $\binom{np}{kp}$.** Let $p$ be a prime, let $m$ and $k$ be
natural numbers with $m + 1 < p$, and let $n$ be an integer. For an integer $x$ and a natural
number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic
valuation on $\mathbb{Q}$. For natural numbers $j$ and $l$ put
$$
c_j = \sum_{s=0}^{\min(j, k)} \binom{jp}{sp} \binom{n-j}{k-s}, \qquad
d_l = \binom{n}{l} \sum_{j=0}^{l} (-1)^{l-j} \binom{l}{j} c_j,
$$
and let $X = \binom{np}{kp} - \binom{n}{k} - (d_1 + \cdots + d_m)$. Then either $X = 0$, or
$\binom{n}{m+1} \ne 0$ and $v_p(X) \ge m + 1 + v_p\big(\binom{n}{m+1}\big)$. That is,
$\binom{np}{kp} - \binom{n}{k} \equiv d_1 + \cdots + d_m$ modulo $p^{m+1+v_p(\binom{n}{m+1})}$,
with equality when $\binom{n}{m+1} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 3
(`integers-2026-A32-thm-3`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_sum_d (p m k : ℕ) (n : ℤ) (hp : p.Prime)
    (hmp : m + 1 < p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let c : ℕ → ℚ := fun j => ∑ s ∈ Finset.range (j + 1),
      if s ≤ k then C ((j * p : ℕ) : ℤ) (s * p) * C (n - j) (k - s) else 0
    let d : ℕ → ℚ := fun l =>
      C n l * ∑ j ∈ Finset.range (l + 1), (-1) ^ (l - j) * (l.choose j : ℚ) * c j
    let X : ℚ := C (n * p) (k * p) - C n k - ∑ l ∈ Finset.Icc 1 m, d l
    X = 0 ∨ (C n (m + 1) ≠ 0 ∧
      ((m + 1 : ℕ) : ℤ) + padicValRat p (C n (m + 1)) ≤ padicValRat p X)

/-- **Congruence for $\binom{np}{kp}$ with the coefficients $\bar C_{ji}$.** Let $p$ be a prime,
let $m$ and $k$ be natural numbers with $m + 1 < p$, and let $n$ be an integer. For an integer
$x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and set
$\binom{x}{r} = 0$ for negative $r$. Let
$$\bar C_{00} = \left( \binom{m-k}{m} + \binom{k+m-n}{m} + (-1)^{m+1} \binom{n-1}{m} - 1 \right)
\binom{n}{k},$$
let $\bar C_{ji} = \binom{n}{j} \binom{m-n}{m-j} \binom{n-j}{k-i}$, and let
$$X = \binom{np}{kp} - \binom{n}{k} - \bar C_{00} -
\sum_{1 \le i < j \le m} \bar C_{ji} \binom{jp}{ip}.$$
Then either $X = 0$, or $\binom{n}{m+1} \ne 0$ and
$v_p(X) \ge m + 1 + v_p\big(\binom{n}{m+1}\big)$, where $v_p$ is the $p$-adic valuation on
$\mathbb{Q}$. With $v_p(0) = \infty$ this says $X \equiv 0 \pmod{p^{m+1+v_p(\binom{n}{m+1})}}$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 4
(`integers-2026-A32-lem-4`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_cbar (p m k : ℕ) (n : ℤ) (hp : p.Prime)
    (hmp : m + 1 < p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let C00 : ℚ :=
      (C ((m : ℤ) - k) m + C ((k : ℤ) + m - n) m + (-1) ^ (m + 1) * C (n - 1) m - 1) * C n k
    let Cbar : ℕ → ℕ → ℚ := fun j i =>
      C n j * C ((m : ℤ) - n) (m - j) * (if i ≤ k then C (n - j) (k - i) else 0)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (C00 + ∑ j ∈ Finset.Icc 1 m, ∑ i ∈ Finset.Ico 1 j, Cbar j i * C ((j * p : ℕ) : ℤ) (i * p))
    X = 0 ∨ (C n (m + 1) ≠ 0 ∧
      ((m + 1 : ℕ) : ℤ) + padicValRat p (C n (m + 1)) ≤ padicValRat p X)

/-- **The congruence for $\binom{np}{kp}$ with symmetrized coefficients.** Let $p$ be a prime,
let $m$ and $k$ be natural numbers with $m + 1 < p$, and let $n$ be an integer. For an integer
$x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, for a rational
number $x$ write $(x)_r = x(x-1)\cdots(x-r+1)$ for the falling factorial, and let $v_p$ be the
$p$-adic valuation on $\mathbb{Q}$. Put
$$
C'_{00} = \left(\binom{m-k}{m} + \binom{k+m-n}{m} + (-1)^{m+1} \binom{n-1}{m} - 1\right)
\binom{n}{k}
$$
and, for $2 \le j \le m$ and $1 \le i \le \lfloor j/2 \rfloor$,
$$
C'_{ji} = \varepsilon_{ji} \, \frac{(n-k)_{j-i} \, (k)_i + (n-k)_i \, (k)_{j-i}}{j!}
\binom{m-n}{m-j} \binom{n}{k},
$$
where $\varepsilon_{ji} = 1/2$ if $j = 2i$ and $\varepsilon_{ji} = 1$ otherwise. Let
$$
X = \binom{np}{kp} - \binom{n}{k} - C'_{00} -
\sum_{j=2}^{m} \sum_{i=1}^{\lfloor j/2 \rfloor} C'_{ji} \binom{jp}{ip}.
$$
Then either $X = 0$, or $\binom{n}{m+1} \ne 0$ and
$v_p(X) \ge m + 1 + v_p\big(\binom{n}{m+1}\big)$. That is, $\binom{np}{kp} - \binom{n}{k}$ is
congruent to $C'_{00} + \sum_{j, i} C'_{ji} \binom{jp}{ip}$ modulo
$p^{m+1+v_p(\binom{n}{m+1})}$, and equal to it when $\binom{n}{m+1} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 4
(`integers-2026-A32-thm-4`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_cprime (p m k : ℕ) (n : ℤ) (hp : p.Prime)
    (hmp : m + 1 < p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let ff : ℚ → ℕ → ℚ := fun x i => ∏ t ∈ Finset.range i, (x - t)
    let C00 : ℚ :=
      (C ((m : ℤ) - k) m + C ((k : ℤ) + m - n) m + (-1) ^ (m + 1) * C (n - 1) m - 1) * C n k
    let Cp : ℕ → ℕ → ℚ := fun j i =>
      (if j = 2 * i then (1 / 2 : ℚ) else 1) *
        ((ff ((n : ℚ) - k) (j - i) * ff k i + ff ((n : ℚ) - k) i * ff k (j - i)) / j.factorial *
          C ((m : ℤ) - n) (m - j) * C n k)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (C00 + ∑ j ∈ Finset.Icc 2 m, ∑ i ∈ Finset.Icc 1 (j / 2), Cp j i * C ((j * p : ℕ) : ℤ) (i * p))
    X = 0 ∨ (C n (m + 1) ≠ 0 ∧
      ((m + 1 : ℕ) : ℤ) + padicValRat p (C n (m + 1)) ≤ padicValRat p X)

/-- **Divisibility of the polynomial parts by $k(n-k)/2$.** Let $m$ be a natural number and $n$ an
integer. For an integer $x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$,
and for a rational number $x$ write $(x)_r = x(x-1)\cdots(x-r+1)$ for the falling factorial. Then
there is a polynomial $Q \in \mathbb{Q}[X]$ such that for every natural number $k$
$$\binom{m-k}{m} + \binom{k+m-n}{m} + (-1)^{m+1} \binom{n-1}{m} - 1 = \frac{k(n-k)}{2} \, Q(k),$$
and for all natural numbers $i$ and $j$ with $1 \le i < j$ there is a polynomial
$Q \in \mathbb{Q}[X]$ such that for every natural number $k$
$$\frac{(n-k)_{j-i} \, (k)_i + (n-k)_i \, (k)_{j-i}}{j!} \binom{m-n}{\max(m-j, 0)} =
\frac{k(n-k)}{2} \, Q(k).$$

For $j \le m$ the left-hand sides are the polynomial parts of the coefficients
$C'_{00}(m, n, k)$ and $C'_{ji}(m, n, k)$ of Theorem 4 (the halving at $j = 2i$ does not affect
divisibility); agreement at every natural number $k$ amounts to divisibility by $k(n-k)/2$
in $\mathbb{Q}[k]$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 1
(`integers-2026-A32-prop-1`). -/
public theorem_wanted exists_polynomial_part_eq_mul_half_mul (m : ℕ) (n : ℤ) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let ff : ℚ → ℕ → ℚ := fun x i => ∏ t ∈ Finset.range i, (x - t)
    (∃ Q : ℚ[X], ∀ k : ℕ,
        C ((m : ℤ) - k) m + C ((k : ℤ) + m - n) m + (-1) ^ (m + 1) * C (n - 1) m - 1 =
          (k : ℚ) * (n - k) / 2 * Q.eval (k : ℚ)) ∧
      ∀ j i : ℕ, 1 ≤ i → i < j → ∃ Q : ℚ[X], ∀ k : ℕ,
        (ff ((n : ℚ) - k) (j - i) * ff k i + ff ((n : ℚ) - k) i * ff k (j - i)) / j.factorial *
            C ((m : ℤ) - n) (m - j) =
          (k : ℚ) * (n - k) / 2 * Q.eval (k : ℚ)

/-! ### Explicit congruences modulo `p^3`, ..., `p^7` -/

/-- **The congruence for $\binom{np}{kp}$ modulo $p^3$.** Let $p \ge 5$ be a prime, let $k$ be a
natural number and let $n$ be an integer. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic valuation on
$\mathbb{Q}$. Let
$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \left(\binom{2p}{p} - 2\right).
$$
Then either $X = 0$, or $\binom{n}{3} \ne 0$ and $v_p(X) \ge 3 + v_p\big(\binom{n}{3}\big)$; that
is, $X \equiv 0 \pmod{p^{3+v_p(\binom{n}{3})}}$, and $X = 0$ when $\binom{n}{3} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 2
(`integers-2026-A32-prop-2`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_three (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (k : ℚ) * (n - k) / 2 * C n k * (((2 * p).choose p : ℚ) - 2)
    X = 0 ∨ (C n 3 ≠ 0 ∧ 3 + padicValRat p (C n 3) ≤ padicValRat p X)

/-- **Equivalent forms of Wolstenholme's congruence.** Let $p \ge 5$ be a prime and let $n$ and
$k$ be natural numbers. Then the congruences $\binom{2p}{p} \equiv 2$, $\binom{np}{p} \equiv n$ and
$\binom{np}{kp} \equiv \binom{n}{k}$ modulo $p^3$ are equivalent.

By Wolstenholme's theorem all three hold for every such $p$.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Corollary 2
(`integers-2026-A32-cor-2`). -/
public theorem_wanted choose_two_mul_prime_congr_iff_pow_three (p n k : ℕ) (hp : p.Prime)
    (hp5 : 5 ≤ p) :
    ((p : ℤ) ^ 3 ∣ ((2 * p).choose p : ℤ) - 2 ↔ (p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n) ∧
      ((p : ℤ) ^ 3 ∣ ((n * p).choose p : ℤ) - n ↔
        (p : ℤ) ^ 3 ∣ ((n * p).choose (k * p) : ℤ) - n.choose k)

/-- **The congruence for $\binom{np}{kp}$ modulo $p^4$ via $\binom{2p}{p}$ and $\binom{3p}{p}$.**
Let $p \ge 7$ be a prime, let $k$ be a natural number and let $n$ be an integer. For an integer
$x$ and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be
the $p$-adic valuation on $\mathbb{Q}$. Let
$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \left((n - 4) +
(3 - n) \binom{2p}{p} + \frac{n - 2}{3} \binom{3p}{p}\right).
$$
Then either $X = 0$, or $\binom{n}{4} \ne 0$ and $v_p(X) \ge 4 + v_p\big(\binom{n}{4}\big)$; that
is, $X \equiv 0 \pmod{p^{4+v_p(\binom{n}{4})}}$, and $X = 0$ when $\binom{n}{4} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 3
(`integers-2026-A32-prop-3`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_four (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp7 : 7 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let N : ℚ := n
    let X : ℚ := C (n * p) (k * p) - C n k -
      (k : ℚ) * (N - k) / 2 * C n k *
        ((N - 4) + (3 - N) * ((2 * p).choose p : ℚ) + (N - 2) / 3 * ((3 * p).choose p : ℚ))
    X = 0 ∨ (C n 4 ≠ 0 ∧ 4 + padicValRat p (C n 4) ≤ padicValRat p X)

/-- **The congruence for $\binom{np}{kp}$ modulo $p^4$ via $\binom{2p}{p}$ alone.** Let
$p \ge 7$ be a prime, let $k$ be a natural number and let $n$ be an integer. For an integer $x$
and a natural number $r$ write $\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the
$p$-adic valuation on $\mathbb{Q}$, with the convention $v_p(0) = 0$. Let
$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{nk(n-k)}{4} \binom{n}{k} \left(\binom{2p}{p} - 2\right).
$$
Then either $X = 0$ or $v_p(X) \ge 4 + v_p\big(\binom{n}{4}\big)$. In particular, when
$\binom{n}{4} = 0$, that is $n \in \{0, 1, 2, 3\}$, the conclusion is only that $X = 0$ or
$v_p(X) \ge 4$.

Equality cannot be demanded when $\binom{n}{4} = 0$: for $p = 7$, $n = 3$ and $k = 1$ one has
$X = 100842 = 6 \cdot 7^5$. The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered
here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 6
(`integers-2026-A32-thm-6`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_four_two_mul (p k : ℕ) (n : ℤ)
    (hp : p.Prime) (hp7 : 7 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let X : ℚ := C (n * p) (k * p) - C n k -
      (n : ℚ) * k * (n - k) / 4 * C n k * (((2 * p).choose p : ℚ) - 2)
    X = 0 ∨ 4 + padicValRat p (C n 4) ≤ padicValRat p X

/-- **The congruence for $\binom{np}{kp}$ modulo $p^5$.** Let $p \ge 11$ be a prime, let $k$ be a
natural number and let $n$ be an integer. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic valuation on
$\mathbb{Q}$. Put $C_{00} = -(k^2 - kn + 2n^2 - 15n + 35)/6$, $C_{21} = (n-4)(n-3)/2$,
$C_{31} = (n-2)(4-n)/3$, $C_{41} = (2k^2 - 2kn + n^2 - 3n + 4)/12$ and
$C_{42} = (n-k-1)(k-1)/12$, and let
$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \Big(C_{00} +
C_{21} \binom{2p}{p} + C_{31} \binom{3p}{p} + C_{41} \binom{4p}{p} + C_{42} \binom{4p}{2p}\Big).
$$
Then either $X = 0$, or $\binom{n}{5} \ne 0$ and $v_p(X) \ge 5 + v_p\big(\binom{n}{5}\big)$; that
is, $X \equiv 0 \pmod{p^{5+v_p(\binom{n}{5})}}$, and $X = 0$ when $\binom{n}{5} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 4
(`integers-2026-A32-prop-4`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_five (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let b : ℕ → ℕ → ℚ := fun j i => ((j * p).choose (i * p) : ℚ)
    let N : ℚ := n
    let K : ℚ := k
    let X : ℚ := C (n * p) (k * p) - C n k -
      K * (N - K) / 2 * C n k *
        (-(K ^ 2 - K * N + 2 * N ^ 2 - 15 * N + 35) / 6 + (N - 4) * (N - 3) / 2 * b 2 1 +
          (N - 2) * (4 - N) / 3 * b 3 1 + (2 * K ^ 2 - 2 * K * N + N ^ 2 - 3 * N + 4) / 12 * b 4 1 +
          (N - K - 1) * (K - 1) / 12 * b 4 2)
    X = 0 ∨ (C n 5 ≠ 0 ∧ 5 + padicValRat p (C n 5) ≤ padicValRat p X)

/-- **The congruence for $\binom{np}{kp}$ modulo $p^6$.** Let $p \ge 11$ be a prime, let $k$ be a
natural number and let $n$ be an integer. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic valuation on
$\mathbb{Q}$. Put $C_{00} = (n-6)(n^2 - nk - 6n + k^2 + 15)/12$,
$C_{21} = (5-n)(4-n)(3-n)/6$, $C_{31} = (n-2)(n-5)(n-4)/6$,
$C_{41} = (2k^2 - 2kn + n^2 - 3n + 4)(5-n)/12$, $C_{42} = (k+1-n)(k-1)(n-5)/12$,
$C_{51} = (n-4)(3k^2 - 3kn + n^2 - 2n + 3)/60$ and $C_{52} = (n-k-1)(k-1)(n-4)/60$, and let
$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \Big(C_{00} +
\sum_{j=2}^{5} \sum_{i=1}^{\lfloor j/2 \rfloor} C_{ji} \binom{jp}{ip}\Big).
$$
Then either $X = 0$, or $\binom{n}{6} \ne 0$ and $v_p(X) \ge 6 + v_p\big(\binom{n}{6}\big)$; that
is, $X \equiv 0 \pmod{p^{6+v_p(\binom{n}{6})}}$, and $X = 0$ when $\binom{n}{6} = 0$.

The paper allows $n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 5
(`integers-2026-A32-prop-5`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_six (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let b : ℕ → ℕ → ℚ := fun j i => ((j * p).choose (i * p) : ℚ)
    let N : ℚ := n
    let K : ℚ := k
    let X : ℚ := C (n * p) (k * p) - C n k -
      K * (N - K) / 2 * C n k *
        ((N - 6) * (N ^ 2 - N * K - 6 * N + K ^ 2 + 15) / 12 +
          (5 - N) * (4 - N) * (3 - N) / 6 * b 2 1 + (N - 2) * (N - 5) * (N - 4) / 6 * b 3 1 +
          (2 * K ^ 2 - 2 * K * N + N ^ 2 - 3 * N + 4) * (5 - N) / 12 * b 4 1 +
          (K + 1 - N) * (K - 1) * (N - 5) / 12 * b 4 2 +
          (N - 4) * (3 * K ^ 2 - 3 * K * N + N ^ 2 - 2 * N + 3) / 60 * b 5 1 +
          (N - K - 1) * (K - 1) * (N - 4) / 60 * b 5 2)
    X = 0 ∨ (C n 6 ≠ 0 ∧ 6 + padicValRat p (C n 6) ≤ padicValRat p X)

/-- **The congruence for $\binom{np}{kp}$ modulo $p^7$.** Let $p \ge 11$ be a prime, let $k$ be a
natural number and let $n$ be an integer. For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$, and let $v_p$ be the $p$-adic valuation on
$\mathbb{Q}$. Put
$$
C_{00} = -\frac{1}{360} \big(2k^4 - 4k^3 n + 11k^2 n^2 - 9k n^3 + 6n^4 - 105k^2 n + 105k n^2 -
105n^3 + 350k^2 - 350kn + 700n^2 - 2205n + 3248\big),
$$
$C_{21} = (6-n)(5-n)(4-n)(3-n)/24$, $C_{31} = (n-2)(6-n)(5-n)(4-n)/18$,
$C_{41} = (6-n)(5-n)(2k^2 - 2kn + n^2 - 3n + 4)/24$,
$C_{42} = (n-k-1)(k-1)(6-n)(5-n)/24$,
$C_{51} = (4-n)(n-6)(3k^2 - 3kn + n^2 - 2n + 3)/60$,
$C_{52} = (k+1-n)(k-1)(n-4)(n-6)/60$,
$$
C_{61} = \frac{1}{360} \big(2k^4 - 4k^3 n + 6k^2 n^2 - 4k n^3 + n^4 - 30k^2 n + 30k n^2 -
10n^3 + 70k^2 - 70kn + 35n^2 - 50n + 48\big),
$$
$C_{62} = (n-k-1)(k-1)(2k^2 - 2kn + n^2 - 5n + 12)/360$ and
$C_{63} = (n-k-1)(n-k-2)(k-1)(k-2)/360$, and let
$$
X = \binom{np}{kp} - \binom{n}{k} - \frac{k(n-k)}{2} \binom{n}{k} \Big(C_{00} +
\sum_{j=2}^{6} \sum_{i=1}^{\lfloor j/2 \rfloor} C_{ji} \binom{jp}{ip}\Big).
$$
Then either $X = 0$, or $\binom{n}{7} \ne 0$ and $v_p(X) \ge 7 + v_p\big(\binom{n}{7}\big)$; that
is, $X \equiv 0 \pmod{p^{7+v_p(\binom{n}{7})}}$, and $X = 0$ when $\binom{n}{7} = 0$.

Two coefficients differ from the printed paper and follow its Definition 1 and Theorem 4:
$C_{00}$ has the prefactor $-1/360$ (printed $-1/720$), and $C_{63}$ has the factor
$(n-k-1)(n-k-2)$ (printed $(k-n-1)(k-n-2)$). With the printed values the congruence fails
already modulo $p$, for instance at $p = 11$, $n = 7$, $k = 1$. The paper allows
$n \in \mathbb{Z}_p$; only integers $n$ are covered here.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Proposition 6
(`integers-2026-A32-prop-6`). -/
public theorem_wanted ringChoose_mul_prime_sub_congr_pow_seven (p k : ℕ) (n : ℤ) (hp : p.Prime)
    (hp11 : 11 ≤ p) :
    let C : ℤ → ℕ → ℚ := fun x r => ((Ring.choose x r : ℤ) : ℚ)
    let b : ℕ → ℕ → ℚ := fun j i => ((j * p).choose (i * p) : ℚ)
    let N : ℚ := n
    let K : ℚ := k
    let X : ℚ := C (n * p) (k * p) - C n k -
      K * (N - K) / 2 * C n k *
        (-(2 * K ^ 4 - 4 * K ^ 3 * N + 11 * K ^ 2 * N ^ 2 - 9 * K * N ^ 3 + 6 * N ^ 4 -
              105 * K ^ 2 * N + 105 * K * N ^ 2 - 105 * N ^ 3 + 350 * K ^ 2 - 350 * N * K +
              700 * N ^ 2 - 2205 * N + 3248) / 360 +
          (6 - N) * (5 - N) * (4 - N) * (3 - N) / 24 * b 2 1 +
          (N - 2) * (6 - N) * (5 - N) * (4 - N) / 18 * b 3 1 +
          (6 - N) * (5 - N) * (2 * K ^ 2 - 2 * K * N + N ^ 2 - 3 * N + 4) / 24 * b 4 1 +
          (N - K - 1) * (K - 1) * (6 - N) * (5 - N) / 24 * b 4 2 +
          (4 - N) * (N - 6) * (3 * K ^ 2 - 3 * K * N + N ^ 2 - 2 * N + 3) / 60 * b 5 1 +
          (-N + K + 1) * (K - 1) * (N - 4) * (N - 6) / 60 * b 5 2 +
          (2 * K ^ 4 - 4 * K ^ 3 * N + 6 * K ^ 2 * N ^ 2 - 4 * K * N ^ 3 + N ^ 4 -
              30 * K ^ 2 * N + 30 * K * N ^ 2 - 10 * N ^ 3 + 70 * K ^ 2 - 70 * K * N +
              35 * N ^ 2 - 50 * N + 48) / 360 * b 6 1 +
          (N - K - 1) * (K - 1) * (2 * K ^ 2 - 2 * K * N + N ^ 2 - 5 * N + 12) / 360 * b 6 2 +
          (N - K - 1) * (N - K - 2) * (K - 1) * (K - 2) / 360 * b 6 3)
    X = 0 ∨ (C n 7 ≠ 0 ∧ 7 + padicValRat p (C n 7) ≤ padicValRat p X)

/-- **$\binom{np}{mp}$ as a quotient of products.** Let $p$ be a prime and let $m$ and $n$ be
natural numbers with $1 \le m \le n$. Then
$$\binom{np}{mp} = \frac{\binom{n}{m} \prod_{j=0}^{m-1} \binom{(n-m+j+1)p-1}{p-1}}
{\prod_{j=0}^{m-1} \binom{(j+1)p-1}{p-1}} = \frac{\prod_{j=0}^{m-1} \binom{(n-m+j+1)p}{p}}
{\prod_{j=0}^{m-1} \binom{(j+1)p}{p}}.$$

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 6
(`integers-2026-A32-lem-6`). -/
public theorem_wanted choose_mul_prime_eq_prod_div_prod (p m n : ℕ) (hp : p.Prime) (hm : 1 ≤ m)
    (hmn : m ≤ n) :
    ((n * p).choose (m * p) : ℚ) =
        (n.choose m : ℚ) * (∏ j ∈ Finset.range m, (((n - m + j + 1) * p - 1).choose (p - 1) : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p - 1).choose (p - 1) : ℚ) ∧
      ((n * p).choose (m * p) : ℚ) =
        (∏ j ∈ Finset.range m, (((n - m + j + 1) * p).choose p : ℚ)) /
          ∏ j ∈ Finset.range m, (((j + 1) * p).choose p : ℚ)

end

end MetaMathlibExt
