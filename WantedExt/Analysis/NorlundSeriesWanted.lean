/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Series associated with Nörlund's digamma identity

Statements from Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18 (primary text: arXiv:2410.22343).

Harmonic numbers of complex argument enter through `H_α = ψ(α + 1) + γ` (the paper's relation
(4)), written with `Complex.digamma`. Where a statement uses only differences of harmonic
numbers, `γ` cancels; Lemma 1 and Theorems 4, 6 and 7 contain standalone `H_{k-1/2}`, `H_{n+z}`
or `H_z` terms, and there `γ` appears explicitly as `Real.eulerMascheroniConstant`. The
binomial coefficient `C(n + z, n)` of complex `z` is `∏_{j=1}^n (z + j)/j`.
Differences of second-order harmonic numbers of complex argument are written through
`H^{(2)}_α = Σ_{j≥1} (1/j² - 1/(j + α)²)` (the paper's relation `H^{(2)}_α = ζ(2) - ψ'(α + 1)`),
and the odd harmonic numbers `O^{(r)}_n = Σ_{j=1}^n 1/(2j - 1)^r` of natural index as finite sums.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MetaMathlibExt

@[expose] public section

/-- **A product series for $\pi \cot(\pi/k)$.** For every integer $k \ge 2$,
$$(k - 2)\Bigl(1 + \sum_{n=1}^{\infty} \frac{1}{n + 1}
\prod_{j=1}^{n} \frac{kj - (k - 2)}{kj + 1}\Bigr) = \pi \cot\frac{\pi}{k}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 1 (`integers-2025-A18-thm-1`). -/
public theorem_wanted sub_two_mul_one_add_tsum_prod_eq_pi_mul_cot {k : ℕ} (hk : 2 ≤ k) :
    ((k : ℝ) - 2) * (1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) *
        ∏ j ∈ Finset.Icc 1 (n + 1), ((k : ℝ) * j - (k - 2)) / (k * j + 1)) =
      Real.pi * Real.cot (Real.pi / k)

/-- **Adegoke–Frontczak series for the tangent.** For every complex number $z$ with
$-\frac12 < \operatorname{Re} z < \frac12$,
$$
\sum_{n \ge 0} \frac{2^{n+1}}{n+1} \prod_{j=0}^{n} \frac{2z - j}{2z - (2j+1)} = -\pi \tan(\pi z).
$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 2 (`integers-2025-A18-thm-2`). -/
public theorem_wanted tsum_two_pow_prod_eq_neg_pi_mul_tan {z : ℂ} (hz₁ : -1 / 2 < z.re)
    (hz₂ : z.re < 1 / 2) :
    ∑' n : ℕ, (2 : ℂ) ^ (n + 1) / ((n : ℂ) + 1) *
        ∏ j ∈ Finset.range (n + 1), (2 * z - j) / (2 * z - (2 * j + 1)) =
      -(Real.pi : ℂ) * Complex.tan (Real.pi * z)

/-- **Harmonic numbers of half-integer index.** Let $k$ be a natural number. For each integer
$r \ge 1$ let $O^{(r)}_k = \sum_{j=1}^{k} \frac{1}{(2j - 1)^r}$, and let $O_k = O^{(1)}_k$.
Let $\psi$ be the digamma function, $\gamma$ the Euler–Mascheroni constant and $\zeta$ the
Riemann zeta function. Then
$$\psi\bigl(k + \tfrac12\bigr) + \gamma = 2 O_k - 2 \log 2,$$
$$\sum_{j=0}^{\infty} \Bigl(\frac{1}{(j + 1)^2} - \frac{1}{(j + k + \frac12)^2}\Bigr) =
-2 \zeta(2) + 4 O^{(2)}_k,$$
$$\sum_{j=0}^{\infty} \Bigl(\frac{1}{(j + 1)^3} - \frac{1}{(j + \frac12)^3}\Bigr) = -6 \zeta(3),$$
and for every natural number $m$,
$$\sum_{j=0}^{\infty} \Bigl(\frac{1}{(j+\frac12)^{m+1}} - \frac{1}{(j+k+\frac12)^{m+1}}\Bigr) =
2^{m+1} O^{(m+1)}_k.$$

With $H_\alpha = \psi(\alpha + 1) + \gamma$ and
$H^{(r)}_\alpha = \sum_{j \ge 1} (j^{-r} - (j + \alpha)^{-r})$, these read
$H_{k-1/2} = 2O_k - 2\log 2$, $H^{(2)}_{k-1/2} = -2\zeta(2) + 4O^{(2)}_k$,
$H^{(3)}_{-1/2} = -6\zeta(3)$ and $H^{(m+1)}_{k-1/2} - H^{(m+1)}_{-1/2} = 2^{m+1} O^{(m+1)}_k$.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Lemma 1 (`integers-2025-A18-lem-1`). -/
public theorem_wanted harmonic_nat_sub_half_values (k : ℕ) :
    Complex.digamma (k + 1 / 2) + Real.eulerMascheroniConstant =
        2 * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) - 2 * Complex.log 2 ∧
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 2 - 1 / ((j : ℂ) + k + 1 / 2) ^ 2) =
        -2 * riemannZeta 2 + 4 * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) ^ 2 ∧
      ∑' j : ℕ, (1 / ((j : ℂ) + 1) ^ 3 - 1 / ((j : ℂ) + 1 / 2) ^ 3) = -6 * riemannZeta 3 ∧
      ∀ m : ℕ, ∑' j : ℕ, (1 / ((j : ℂ) + 1 / 2) ^ (m + 1) - 1 / ((j : ℂ) + k + 1 / 2) ^ (m + 1)) =
        2 ^ (m + 1) * ∑ j ∈ Finset.range k, 1 / (2 * (j : ℂ) + 1) ^ (m + 1)

/-- **The Gamma function at $r + \tfrac12$ and at $\tfrac12 - r$.** For every complex number $r$
that is not a negative integer,
$$\Gamma\bigl(r + \tfrac12\bigr) =
\frac{\sqrt{\pi}}{2^{2r}} \cdot \frac{\Gamma(2r + 1)}{\Gamma(r + 1)},$$
where $2^{2r} = e^{2r \log 2}$; and for every natural number $r$,
$$\Gamma\bigl(\tfrac12 - r\bigr) = \frac{(-1)^r \, 2^{2r} \sqrt{\pi}}{r! \binom{2r}{r}}.$$

In the first identity $\Gamma$ is taken to be $0$ at the non-positive integers, so for
$r = -\tfrac12, -\tfrac32, \dots$ both sides are $0$.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Lemma 2 (`integers-2025-A18-lem-2`). -/
public theorem_wanted Gamma_add_half_and_Gamma_half_sub_nat :
    (∀ r : ℂ, (∀ m : ℕ, r ≠ -((m : ℂ) + 1)) →
      Complex.Gamma (r + 1 / 2) =
        (Real.sqrt Real.pi : ℂ) / (2 : ℂ) ^ (2 * r) *
          (Complex.Gamma (2 * r + 1) / Complex.Gamma (r + 1))) ∧
    ∀ r : ℕ, Complex.Gamma (1 / 2 - r) =
      (Real.sqrt Real.pi : ℂ) * (-1) ^ r / r.factorial * 2 ^ (2 * r) / (2 * r).choose r

/-- **A Catalan series in terms of the digamma function.** Let $z$ be a complex number with
$\operatorname{Re} z > 0$, let $\binom{n+z}{n} = \prod_{j=1}^{n} \frac{z + j}{j}$, let $C_n$ be the
$n$th Catalan number and $\psi$ the digamma function. Then
$$\sum_{n=0}^{\infty} \frac{C_n}{4^n \binom{n+z}{n}} =
-2z \bigl(\psi(z) - \psi(z + \tfrac12)\bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 3, identity (7) (`integers-2025-A18-thm-3`). -/
public theorem_wanted tsum_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 0 < z.re) :
    ∑' n : ℕ, (catalan n : ℂ) / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      -2 * z * (Complex.digamma z - Complex.digamma (z + 1 / 2))

/-- **Catalan series summing to $4(1 - \log 2)$ and $\frac{10}{3} - 4 \log 2$.** With $C_n$ the
$n$th Catalan number,
$$\sum_{n=0}^{\infty} \frac{C_n}{4^n (n + 1)} = 4 (1 - \log 2)$$
and
$$\sum_{n=0}^{\infty} \frac{C_n}{4^n (n + 1)(n + 2)} = \frac{10}{3} - 4 \log 2.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 3, first two identities
(`integers-2025-A18-thm-3`). -/
public theorem_wanted tsum_catalan_div_four_pow_special :
    ∑' n : ℕ, (catalan n : ℝ) / (4 ^ n * ((n : ℝ) + 1)) = 4 * (1 - Real.log 2) ∧
      ∑' n : ℕ, (catalan n : ℝ) / (4 ^ n * ((n : ℝ) + 1) * ((n : ℝ) + 2)) =
        10 / 3 - 4 * Real.log 2

/-- **An odd harmonic series for $\pi^2/6$ and a Catalan–harmonic series for $8 - 2\pi^2/3$.**
Let $O_k = \sum_{j=1}^{k} 1/(2j-1)$ be the $k$-th odd harmonic number, $C_n$ the $n$-th Catalan
number and $H_k = \sum_{j=1}^{k} 1/j$ the $k$-th harmonic number. Then
$$\sum_{n=0}^{\infty} \frac{O_{n+1}}{(n+1)(2n+1)} = \frac{\pi^2}{6}$$
and
$$\sum_{n=0}^{\infty} \frac{C_n H_{n+1}}{4^n (n+1)} = 8 - \frac{2\pi^2}{3}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 4, identities (8) and (9)
(`integers-2025-A18-thm-4`). -/
public theorem_wanted tsum_odd_harmonic_div_and_catalan_mul_harmonic_special :
    ∑' n : ℕ, (∑ j ∈ Finset.range (n + 1), 1 / (2 * (j : ℝ) + 1)) / (((n : ℝ) + 1) * (2 * n + 1)) =
        Real.pi ^ 2 / 6 ∧
      ∑' n : ℕ, (catalan n : ℝ) / 4 ^ n * (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) =
        8 - 2 * Real.pi ^ 2 / 3

/-- **A Catalan series weighted by harmonic numbers of complex argument.** Let $z$ be a complex
number with $\operatorname{Re} z > 0$, let $\binom{n+z}{n} = \prod_{j=1}^{n} \frac{z + j}{j}$, let
$C_n$ be the $n$th Catalan number, $\psi$ the digamma function and $\gamma$ the Euler–Mascheroni
constant. Then
$$\sum_{n=0}^{\infty} \frac{C_n \bigl(\psi(n + z + 1) + \gamma\bigr)}{4^n \binom{n+z}{n}} =
2 \bigl(\psi(z) - \psi(z + \tfrac12)\bigr) \bigl(1 - z (\psi(z + 1) + \gamma)\bigr) +
2z \sum_{j=0}^{\infty} \Bigl(\frac{1}{(j + z)^2} - \frac{1}{(j + z + \frac12)^2}\Bigr).$$

In terms of $H_\alpha = \psi(\alpha + 1) + \gamma$, the summand is
$C_n H_{n+z} / (4^n \binom{n+z}{n})$.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 4, identity (10)
(`integers-2025-A18-thm-4`). -/
public theorem_wanted tsum_catalan_mul_harmonic_div_four_pow_mul_binom {z : ℂ} (hz : 0 < z.re) :
    ∑' n : ℕ, (catalan n : ℂ) * (Complex.digamma (n + z + 1) + Real.eulerMascheroniConstant) /
        (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * (Complex.digamma z - Complex.digamma (z + 1 / 2)) *
          (1 - z * (Complex.digamma (z + 1) + Real.eulerMascheroniConstant)) +
        2 * z * ∑' j : ℕ, (1 / ((j : ℂ) + z) ^ 2 - 1 / ((j : ℂ) + z + 1 / 2) ^ 2)

/-- **Digamma evaluation of the $(2n+1)$-weighted Catalan series with binomial denominators.**
Let $C_n$ be the $n$-th Catalan number and $\psi$ the digamma function, and for complex $z$ write
$\binom{n+z}{n} = \prod_{j=1}^{n} (z+j)/j$. For every complex number $z$ with
$\operatorname{Re} z > 1/2$,
$$\sum_{n=0}^{\infty} \frac{(2n+1)\,C_n}{4^n \binom{n+z}{n}} =
2z\bigl(\psi(z) - \psi(z - \tfrac12)\bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 5, identity (11) (`integers-2025-A18-thm-5`). -/
public theorem_wanted tsum_odd_mul_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (2 * (n : ℂ) + 1) * catalan n / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * z * (Complex.digamma z - Complex.digamma (z - 1 / 2))

/-- **Catalan series over powers of $4$ equal to $4\ln 2$ and $4\ln 2 - 2$.** Let $C_n$ be the
$n$-th Catalan number. Then
$$\sum_{n=0}^{\infty} \frac{2n+1}{n+1} \cdot \frac{C_n}{4^n} = 4\ln 2$$
and
$$\sum_{n=0}^{\infty} \frac{2n+1}{(n+1)(n+2)} \cdot \frac{C_n}{4^n} = 4\ln 2 - 2.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 5, first two identities
(`integers-2025-A18-thm-5`). -/
public theorem_wanted tsum_odd_mul_catalan_div_four_pow_special :
    ∑' n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * catalan n / 4 ^ n = 4 * Real.log 2 ∧
      ∑' n : ℕ, (2 * (n : ℝ) + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) * catalan n / 4 ^ n =
        4 * Real.log 2 - 2

/-- **Digamma evaluation of the $n$-weighted Catalan series with binomial denominators.** Let
$C_n$ be the $n$-th Catalan number and $\psi$ the digamma function, and for complex $z$ write
$\binom{n+z}{n} = \prod_{j=1}^{n} (z+j)/j$. For every complex number $z$ with
$\operatorname{Re} z > 1/2$,
$$\sum_{n=0}^{\infty} \frac{n\,C_n}{4^n \binom{n+z}{n}} =
2z\,\psi(z) - z\bigl(\psi(z + \tfrac12) + \psi(z - \tfrac12)\bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Corollary 1 (`integers-2025-A18-cor-1`). -/
public theorem_wanted tsum_nat_mul_catalan_div_four_pow_mul_binom {z : ℂ} (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (n : ℂ) * catalan n / (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * z * Complex.digamma z - z * (Complex.digamma (z + 1 / 2) + Complex.digamma (z - 1 / 2))

/-- **Adegoke–Frontczak series with odd weights, Catalan numbers and harmonic numbers.** Let $z$
be a complex number with $\operatorname{Re} z > \frac12$. Write $C_n$ for the $n$-th Catalan
number, $\psi$ for the digamma function, $\gamma$ for the Euler–Mascheroni constant,
$H_\alpha = \psi(\alpha + 1) + \gamma$ for complex $\alpha$, and
$\binom{n+z}{n} = \prod_{j=1}^{n} \frac{z+j}{j}$. Then
$$
\sum_{n \ge 0} \frac{(2n+1)\, C_n\, H_{n+z}}{4^n \binom{n+z}{n}} =
2\,(z H_z - 1)\bigl(\psi(z) - \psi(z - \tfrac12)\bigr) +
2z \sum_{j \ge 0} \Bigl(\frac{1}{(j + z - \frac12)^2} - \frac{1}{(j + z)^2}\Bigr).
$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 6, identity (13)
(`integers-2025-A18-thm-6`). -/
public theorem_wanted tsum_odd_mul_catalan_mul_harmonic_div_four_pow_mul_binom {z : ℂ}
    (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (2 * (n : ℂ) + 1) * catalan n *
        (Complex.digamma (n + z + 1) + Real.eulerMascheroniConstant) /
        (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      2 * (z * (Complex.digamma (z + 1) + Real.eulerMascheroniConstant) - 1) *
          (Complex.digamma z - Complex.digamma (z - 1 / 2)) +
        2 * z * ∑' j : ℕ, (1 / ((j : ℂ) + z - 1 / 2) ^ 2 - 1 / ((j : ℂ) + z) ^ 2)

/-- **Special values of the odd-weighted Catalan–harmonic series.** Let $C_n$ be the $n$-th
Catalan number, $H_n = \sum_{k=1}^{n} \frac1k$ the $n$-th harmonic number and
$O_n = \sum_{k=1}^{n} \frac{1}{2k-1}$ the $n$-th odd harmonic number. Then
$$
\sum_{n \ge 0} \frac{2n+1}{n+1} \cdot \frac{C_n H_{n+1}}{4^n} = \frac{2\pi^2}{3}, \qquad
\sum_{n \ge 0} \frac{2n+1}{(n+2)(n+1)} \cdot \frac{C_n H_{n+2}}{4^n} =
\frac{2\pi^2}{3} + 4 \ln 2 - 8,
$$
and
$$
\sum_{n \ge 0} \frac{O_{n+2}}{(n+1)(2n+3)} = 4 - 2 \ln 2 - \frac{\pi^2}{6}.
$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 6, particular cases and identity (14)
(`integers-2025-A18-thm-6`). -/
public theorem_wanted tsum_odd_mul_catalan_mul_harmonic_special :
    ∑' n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) * catalan n * (harmonic (n + 1) : ℝ) / 4 ^ n =
        2 * Real.pi ^ 2 / 3 ∧
      ∑' n : ℕ, (2 * (n : ℝ) + 1) / (((n : ℝ) + 2) * ((n : ℝ) + 1)) * catalan n *
          (harmonic (n + 2) : ℝ) / 4 ^ n =
        2 * Real.pi ^ 2 / 3 + 4 * Real.log 2 - 8 ∧
      ∑' n : ℕ, (∑ j ∈ Finset.range (n + 2), 1 / (2 * (j : ℝ) + 1)) /
          (((n : ℝ) + 1) * (2 * n + 3)) =
        4 - 2 * Real.log 2 - Real.pi ^ 2 / 6

/-- **Digamma evaluation of the $n$-weighted Catalan–harmonic series with binomial
denominators.** Let $C_n$ be the $n$-th Catalan number, $\psi$ the digamma function and $\gamma$
the Euler–Mascheroni constant; for complex $w$ write $H_w = \psi(w + 1) + \gamma$, and for complex
$z$ write $\binom{n+z}{n} = \prod_{j=1}^{n} (z+j)/j$. For every complex number $z$ with
$\operatorname{Re} z > 1/2$,
$$\sum_{n=0}^{\infty} \frac{n\,C_n H_{n+z}}{4^n \binom{n+z}{n}} =
(z H_z - 1)\bigl(2\psi(z) - \psi(z + \tfrac12) - \psi(z - \tfrac12)\bigr) +
z \sum_{j=0}^{\infty} \Bigl(\frac{1}{(j + z + \frac12)^2} + \frac{1}{(j + z - \frac12)^2} -
\frac{2}{(j + z)^2}\Bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 7, identity (15)
(`integers-2025-A18-thm-7`). -/
public theorem_wanted tsum_nat_mul_catalan_mul_harmonic_div_four_pow_mul_binom {z : ℂ}
    (hz : 1 / 2 < z.re) :
    ∑' n : ℕ, (n : ℂ) * catalan n * (Complex.digamma (n + z + 1) + Real.eulerMascheroniConstant) /
        (4 ^ n * ∏ j ∈ Finset.Icc 1 n, (z + j) / j) =
      (z * (Complex.digamma (z + 1) + Real.eulerMascheroniConstant) - 1) *
          (2 * Complex.digamma z - Complex.digamma (z + 1 / 2) - Complex.digamma (z - 1 / 2)) +
        z * ∑' j : ℕ, (1 / ((j : ℂ) + z + 1 / 2) ^ 2 + 1 / ((j : ℂ) + z - 1 / 2) ^ 2 -
          2 / ((j : ℂ) + z) ^ 2)

/-- **Special values of the $n$-weighted Catalan–harmonic series.** Let $C_n$ be the $n$-th
Catalan number, $H_k = \sum_{j=1}^{k} 1/j$ the $k$-th harmonic number and
$O_k = \sum_{j=1}^{k} 1/(2j-1)$ the $k$-th odd harmonic number. Then
$$\sum_{n=0}^{\infty} \frac{n\,C_n H_{n+1}}{4^n (n+1)} = \frac{2\pi^2}{3} - 4$$
and
$$\sum_{n=0}^{\infty} \frac{n\,O_{n+2}}{(n+1)(2n+1)(2n+3)} =
\frac{13}{4} - 2\ln 2 - \frac{\pi^2}{6}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 7, particular cases and identity (16)
(`integers-2025-A18-thm-7`). -/
public theorem_wanted tsum_nat_mul_catalan_mul_harmonic_special :
    ∑' n : ℕ, (n : ℝ) * catalan n / 4 ^ n * (harmonic (n + 1) : ℝ) / ((n : ℝ) + 1) =
        2 * Real.pi ^ 2 / 3 - 4 ∧
      ∑' n : ℕ, (n : ℝ) * (∑ j ∈ Finset.range (n + 2), 1 / (2 * (j : ℝ) + 1)) /
          (((n : ℝ) + 1) * (2 * n + 1) * (2 * n + 3)) =
        13 / 4 - 2 * Real.log 2 - Real.pi ^ 2 / 6

/-- **Central binomial series for $\pi^2/8$ and a series for $2\ln 2$.** We have
$$\sum_{n=0}^{\infty} \frac{4^n}{\binom{2(n+1)}{n+1} (n+1)^2} = \frac{\pi^2}{8}$$
and
$$\sum_{n=0}^{\infty} \frac{1}{(2n+1)(n+1)} = 2\ln 2.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 8, identities (17) and (18)
(`integers-2025-A18-thm-8`). -/
public theorem_wanted tsum_four_pow_div_centralBinom_mul_sq_special :
    ∑' n : ℕ, (4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 8 ∧
      ∑' n : ℕ, 1 / ((2 * (n : ℝ) + 1) * ((n : ℝ) + 1)) = 2 * Real.log 2

/-- **Digamma evaluation of a central binomial series with a complex binomial parameter.** Let
$\Gamma$ be the Gamma function and $\psi$ the digamma function, and let $h$ be a complex number
that is not a nonnegative integer and has $\operatorname{Re} h > -1/2$. Writing $\binom{n}{h}^{-1}$
for $\Gamma(h+1)\,\Gamma(n-h+1)/n!$, we have
$$\sum_{n=0}^{\infty} \frac{4^n}{\binom{n}{h} \binom{2(n+1)}{n+1} (n+1)^2} =
\frac{\pi}{4} \cdot \frac{\psi(h + \tfrac12) - \psi(\tfrac12)}{\sin(\pi h)}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 8, identity (19)
(`integers-2025-A18-thm-8`). -/
public theorem_wanted tsum_four_pow_div_binom_mul_centralBinom_mul_sq {h : ℂ}
    (hh : ∀ m : ℕ, h ≠ m) (hre : -1 / 2 < h.re) :
    ∑' n : ℕ, (4 : ℂ) ^ n * (Complex.Gamma (h + 1) * Complex.Gamma (n - h + 1) / n.factorial) /
        (((n + 1).centralBinom : ℂ) * ((n : ℂ) + 1) ^ 2) =
      Real.pi / 4 * (Complex.digamma (h + 1 / 2) - Complex.digamma (1 / 2)) /
        Complex.sin (Real.pi * h)

/-- **A shifted central binomial series.** For every natural number $h$, with
$H_h = \sum_{j=1}^{h} \frac{1}{j}$ the $h$th harmonic number,
$$\sum_{n=0}^{\infty} \frac{\binom{2n}{n}}{\binom{n+h}{h} \binom{2(n+h+1)}{n+h+1} (n + h + 1)^2} =
\frac{(-1)^h (H_h + 2 \log 2)}{(h + 1) \binom{2(h+1)}{h+1}} -
\sum_{n=0}^{h-1} \frac{(-1)^{h-n} \binom{h}{n}}{\binom{2(h-n)}{h-n} \binom{2(n+1)}{n+1} (n+1)^2}.$$

After replacing $n$ by $n - h$, the left side is
$\sum_{n \ge h} \binom{2(n-h)}{n-h} / \bigl(\binom{n}{h} \binom{2(n+1)}{n+1} (n + 1)^2\bigr)$.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Corollary 2, identity (20)
(`integers-2025-A18-cor-2`). -/
public theorem_wanted tsum_centralBinom_div_choose_mul_centralBinom_mul_sq (h : ℕ) :
    ∑' n : ℕ, (n.centralBinom : ℝ) /
        (((n + h).choose h : ℝ) * ((n + h + 1).centralBinom : ℝ) * ((n : ℝ) + h + 1) ^ 2) =
      (-1) ^ h * ((harmonic h : ℝ) + 2 * Real.log 2) /
          (((h : ℝ) + 1) * ((h + 1).centralBinom : ℝ)) -
        ∑ n ∈ Finset.range h, (-1) ^ (h - n) * (h.choose n : ℝ) /
          (((h - n).centralBinom : ℝ) * ((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)

/-- **A shifted central binomial series with odd harmonic numbers.** For every natural number $h$,
write $H_h = \sum_{j=1}^{h} \frac{1}{j}$, $H^{(2)}_h = \sum_{j=1}^{h} \frac{1}{j^2}$ and
$O_n = \sum_{j=1}^{n} \frac{1}{2j - 1}$. Then
$$\sum_{n=0}^{\infty} \frac{\binom{2n}{n} O_n}{\binom{n+h}{h} \binom{2(n+h+1)}{n+h+1} (n + h + 1)^2}
= -\frac{(-1)^h \bigl(\frac{\pi^2}{6} - H^{(2)}_h\bigr)}{2 (h + 1) \binom{2(h+1)}{h+1}} +
\frac{(-1)^h (H_h + 2 \log 2) \, O_{h+1}}{(h + 1) \binom{2(h+1)}{h+1}} -
\sum_{n=0}^{h-1} \frac{(-1)^{h-n} \binom{h}{n} \, O_{h-n}}
{\binom{2(h-n)}{h-n} \binom{2(n+1)}{n+1} (n+1)^2}.$$

After replacing $n$ by $n - h$, the left side is
$\sum_{n \ge h} \binom{2(n-h)}{n-h} O_{n-h} /
\bigl(\binom{n}{h} \binom{2(n+1)}{n+1} (n + 1)^2\bigr)$.

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 9, identity (22)
(`integers-2025-A18-thm-9`). -/
public theorem_wanted tsum_centralBinom_mul_odd_harmonic_div_choose_mul_centralBinom_mul_sq
    (h : ℕ) :
    ∑' n : ℕ, (n.centralBinom : ℝ) * (∑ j ∈ Finset.range n, 1 / (2 * (j : ℝ) + 1)) /
        (((n + h).choose h : ℝ) * ((n + h + 1).centralBinom : ℝ) * ((n : ℝ) + h + 1) ^ 2) =
      -((-1) ^ h * (Real.pi ^ 2 / 6 - ∑ j ∈ Finset.range h, 1 / ((j : ℝ) + 1) ^ 2) /
          (2 * ((h : ℝ) + 1) * ((h + 1).centralBinom : ℝ))) +
        (-1) ^ h * ((harmonic h : ℝ) + 2 * Real.log 2) /
            (((h : ℝ) + 1) * ((h + 1).centralBinom : ℝ)) *
          ∑ j ∈ Finset.range (h + 1), 1 / (2 * (j : ℝ) + 1) -
        ∑ n ∈ Finset.range h, (-1) ^ (h - n) * (h.choose n : ℝ) /
            (((h - n).centralBinom : ℝ) * ((n + 1).centralBinom : ℝ)) *
          (∑ j ∈ Finset.range (h - n), 1 / (2 * (j : ℝ) + 1)) / ((n : ℝ) + 1) ^ 2

/-- **Series over $4^n$ with binomial and central binomial denominators.** Write
$O^{(2)}_k = \sum_{j=1}^{k} 1/(2j-1)^2$. For every positive integer $m$,
$$\sum_{n=0}^{\infty} \frac{4^n}{(n+1) \binom{n+m}{m} \binom{2(n+m)}{n+m}} =
\frac{m}{4} \cdot \frac{3 \cdot \pi^2/6 - 4 O^{(2)}_{m-1}}{\binom{2(m-1)}{m-1}}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 10, identity (23)
(`integers-2025-A18-thm-10`). -/
public theorem_wanted tsum_four_pow_div_succ_mul_choose_mul_centralBinom {m : ℕ} (hm : 0 < m) :
    ∑' n : ℕ, (4 : ℝ) ^ n /
        (((n : ℝ) + 1) * ((n + m).choose m : ℝ) * ((n + m).centralBinom : ℝ)) =
      (m : ℝ) / 4 *
          (3 * (Real.pi ^ 2 / 6) - 4 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) ^ 2) /
        ((m - 1).centralBinom : ℝ)

/-- **An odd harmonic series with binomial and central binomial denominators.** Let $\zeta$ be
the Riemann zeta function, let $O^{(r)}_k = \sum_{j=1}^{k} 1/(2j-1)^r$ be the $k$-th odd harmonic
number of order $r$, and write $O_k = O^{(1)}_k$. For every positive integer $m$,
$$\sum_{n=0}^{\infty} \frac{4^n O_{n+m}}{(n+1) \binom{n+m}{m} \binom{2(n+m)}{n+m}} =
\frac{m}{4 \binom{2(m-1)}{m-1}} \Bigl(7\zeta(3) - 8 O^{(3)}_{m-1} +
O_{m-1} \bigl(3\zeta(2) - 4 O^{(2)}_{m-1}\bigr)\Bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 11, identity (27)
(`integers-2025-A18-thm-11`). -/
public theorem_wanted tsum_four_pow_mul_odd_harmonic_div_succ_mul_choose_mul_centralBinom {m : ℕ}
    (hm : 0 < m) :
    ∑' n : ℕ, (4 : ℂ) ^ n * (∑ j ∈ Finset.range (n + m), 1 / (2 * (j : ℂ) + 1)) /
        (((n : ℂ) + 1) * ((n + m).choose m : ℂ) * ((n + m).centralBinom : ℂ)) =
      (m : ℂ) / 4 / ((m - 1).centralBinom : ℂ) *
        (7 * riemannZeta 3 - 8 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℂ) + 1) ^ 3 +
          (∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℂ) + 1)) *
            (3 * riemannZeta 2 - 4 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℂ) + 1) ^ 2))

/-- **Catalan numbers over binomial and central binomial coefficients.** Let $m$ be a positive
integer, $C_n$ the $n$th Catalan number, $H_n = \sum_{j=1}^{n} \frac{1}{j}$ the $n$th harmonic
number and $O_n = \sum_{j=1}^{n} \frac{1}{2j - 1}$. Then
$$\sum_{n=0}^{\infty} \frac{C_n}{\binom{n+m}{n} \binom{2(n+m)}{n+m}} =
\frac{m}{2} \cdot \frac{H_{m-1} - 2 O_{m-1} + 2 \log 2}{\binom{2(m-1)}{m-1}}.$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 12, identity (28)
(`integers-2025-A18-thm-12`). -/
public theorem_wanted tsum_catalan_div_choose_mul_centralBinom {m : ℕ} (hm : 0 < m) :
    ∑' n : ℕ, (catalan n : ℝ) / (((n + m).choose n : ℝ) * ((n + m).centralBinom : ℝ)) =
      (m : ℝ) / 2 *
          ((harmonic (m - 1) : ℝ) - 2 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) +
            2 * Real.log 2) /
        ((m - 1).centralBinom : ℝ)

/-- **An odd harmonic Catalan series over central binomial coefficients.** Let $m$ be a positive
integer and $C_n$ the $n$th Catalan number, and write $H_n = \sum_{j=1}^{n} \frac{1}{j}$,
$H^{(2)}_n = \sum_{j=1}^{n} \frac{1}{j^2}$, $O_n = \sum_{j=1}^{n} \frac{1}{2j - 1}$ and
$O^{(2)}_n = \sum_{j=1}^{n} \frac{1}{(2j - 1)^2}$. Then
$$\sum_{n=0}^{\infty} \frac{C_n O_{n+m}}{\binom{n+m}{m} \binom{2(n+m)}{n+m}} =
\frac{m}{4 \binom{2(m-1)}{m-1}} \Bigl(H^{(2)}_{m-1} + \frac{\pi^2}{3} - 4 O^{(2)}_{m-1} +
2 O_{m-1} \bigl(H_{m-1} - 2 O_{m-1} + 2 \log 2\bigr)\Bigr).$$

Source: Kunle Adegoke and Robert Frontczak, *Series Associated with a Forgotten Identity of
Nörlund*, INTEGERS 25 (2025), Article A18, Theorem 13, identity (30)
(`integers-2025-A18-thm-13`). -/
public theorem_wanted tsum_catalan_mul_odd_harmonic_div_choose_mul_centralBinom {m : ℕ}
    (hm : 0 < m) :
    ∑' n : ℕ, (catalan n : ℝ) * (∑ j ∈ Finset.range (n + m), 1 / (2 * (j : ℝ) + 1)) /
        (((n + m).choose m : ℝ) * ((n + m).centralBinom : ℝ)) =
      (m : ℝ) / 4 / ((m - 1).centralBinom : ℝ) *
        (∑ j ∈ Finset.range (m - 1), 1 / ((j : ℝ) + 1) ^ 2 + 2 * (Real.pi ^ 2 / 6) -
          4 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) ^ 2 +
          2 * (∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1)) *
            ((harmonic (m - 1) : ℝ) - 2 * ∑ j ∈ Finset.range (m - 1), 1 / (2 * (j : ℝ) + 1) +
              2 * Real.log 2))

end

end MetaMathlibExt
