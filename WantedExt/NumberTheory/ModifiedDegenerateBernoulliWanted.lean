/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.Binomial

/-!
# Symmetric identities on modified degenerate Bernoulli polynomials

Statements from Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4.

The modified degenerate Bernoulli polynomial of Dolgy, Kim, Kwon and Seo is defined in the paper by
`∑ 𝔅_{n,λ}(x) tⁿ / n! = t (1+λ)^{xt/λ} / ((1+λ)^{t/λ} - 1)`. With the principal branch
`(1+λ)^w = exp (w log (1+λ))` and `c = log (1+λ) / λ` this generating function is
`t e^{cxt} / (e^{ct} - 1)`, whence `𝔅_{n,λ}(x) = c^{n-1} B_n(x)`; this closed form is the definition
below, and `modifiedDegenerateBernoulli_generating_function` proves the paper's generating function
from it. The generating function needs `λ ≠ 0` and `λ ≠ -1` (exactly the condition `c ≠ 0`), which
the statements assume. Binomial coefficients with a complex upper argument are `Ring.choose`.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Modified degenerate Bernoulli polynomials.** For a complex number $\lambda$, a natural number
$n$ and a complex number $x$, the modified degenerate Bernoulli polynomial is
$\mathfrak{B}_{n,\lambda}(x) = c^{n-1} B_n(x)$, where $c = \log(1+\lambda)/\lambda$ with the
principal branch of the logarithm, $B_n$ is the $n$-th Bernoulli polynomial (with
$B_1(x) = x - 1/2$), and the exponent $n - 1$ is an integer, so that
$\mathfrak{B}_{0,\lambda}(x) = c^{-1}$. At $\lambda = 0$ and $\lambda = -1$, where this quotient is
undefined, $c$ is taken to be $0$, with $0^{-1} = 0$ and $0^0 = 1$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1 (generating
function of Dolgy, Kim, Kwon and Seo). -/
noncomputable def modifiedDegenerateBernoulli (lam : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  (Complex.log (1 + lam) / lam) ^ ((n : ℤ) - 1) * Polynomial.aeval x (Polynomial.bernoulli n)

/-- **Generating function of the modified degenerate Bernoulli polynomials.** Let $\lambda$ and $x$
be complex numbers such that $c = \log(1+\lambda)/\lambda$ (principal branch) is nonzero, and write
$\mathfrak{B}_{n,\lambda}(x)$ for the modified degenerate Bernoulli polynomials. Then, as formal
power series in $t$ over $\mathbb{C}$,

$$
\Bigl(\sum_{n \ge 0} \mathfrak{B}_{n,\lambda}(x) \frac{t^n}{n!}\Bigr) \bigl(e^{ct} - 1\bigr) =
t\, e^{cxt}.
$$

With $(1+\lambda)^w = e^{w \log(1+\lambda)}$, this says that the series times
$(1+\lambda)^{t/\lambda} - 1$ equals $t\,(1+\lambda)^{xt/\lambda}$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1. -/
theorem modifiedDegenerateBernoulli_generating_function (lam x : ℂ)
    (h : Complex.log (1 + lam) / lam ≠ 0) :
    PowerSeries.mk (fun n => modifiedDegenerateBernoulli lam n x / n.factorial) *
        (PowerSeries.rescale (Complex.log (1 + lam) / lam) (PowerSeries.exp ℂ) - 1) =
      PowerSeries.X *
        PowerSeries.rescale (Complex.log (1 + lam) / lam * x) (PowerSeries.exp ℂ) := by
  set c := Complex.log (1 + lam) / lam with hc
  have key := congrArg (PowerSeries.rescale c)
    (Polynomial.bernoulli_generating_function (A := ℂ) x)
  rw [map_mul, map_sub, map_one, map_mul, PowerSeries.rescale_X, PowerSeries.rescale_rescale] at key
  have hmk : PowerSeries.mk (fun n => modifiedDegenerateBernoulli lam n x / n.factorial) =
      PowerSeries.C c⁻¹ * PowerSeries.rescale c (PowerSeries.mk fun n =>
        Polynomial.aeval x ((1 / n.factorial : ℚ) • Polynomial.bernoulli n)) := by
    ext n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale,
      PowerSeries.coeff_mk, map_smul, modifiedDegenerateBernoulli, zpow_sub₀ h, zpow_one,
      zpow_natCast, Rat.smul_def]
    push_cast
    field_simp
  rw [hmk, mul_assoc, key, ← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h, map_one,
    one_mul, mul_comm x c]

/-- **The first modified degenerate Bernoulli polynomial.** For all complex numbers $\lambda$ and
$x$, the modified degenerate Bernoulli polynomial $\mathfrak{B}_{1,\lambda}$ of index $1$ satisfies
$\mathfrak{B}_{1,\lambda}(x) = x - 1/2$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Section 1. -/
theorem modifiedDegenerateBernoulli_one (lam x : ℂ) :
    modifiedDegenerateBernoulli lam 1 x = x - 1 / 2 := by
  simp [modifiedDegenerateBernoulli, Polynomial.bernoulli_one]

/-- **Symmetric identity for modified degenerate Bernoulli polynomials.** Let $m \ge 2$ and
$n \ge 1$ be integers, let $\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$,
let $r_1, \ldots, r_m$ and $x_1, \ldots, x_m$ be complex numbers, write
$\mathfrak{B}_{k,\lambda}(x)$ for the modified degenerate Bernoulli polynomials, and put
$r_0 = n - r_1 - \cdots - r_m$. Then

$$
r_0 \sum_{k_1 + \cdots + k_m = n} \prod_{j=1}^{m} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j)
= -\sum_{i=1}^{m} r_i \sum_{k_1 + \cdots + k_m = n} \binom{r_0}{k_i}
\mathfrak{B}_{k_i,\lambda}(1 - x_i)
\prod_{j \ne i} \binom{r_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $\binom{w}{k} = w(w-1) \cdots
(w-k+1)/k!$ is the binomial coefficient with a complex upper argument, and $[j > i]$ is $1$ if
$j > i$ and $0$ otherwise.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Theorem 1
(`jis-2024-24.5.4-thm-1`). -/
public theorem_wanted modifiedDegenerateBernoulli_symmetric_identity (m n : ℕ) (hm : 2 ≤ m)
    (hn : 1 ≤ n) (r x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) - ∑ j, r j) * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        ∏ j, Ring.choose (r j) (k j) * modifiedDegenerateBernoulli lam (k j) (x j) =
      -∑ i, r i * ∑ k ∈ Finset.Nat.antidiagonalTuple m n,
        Ring.choose ((n : ℂ) - ∑ j, r j) (k i) * modifiedDegenerateBernoulli lam (k i) (1 - x i) *
          ∏ j ∈ univ.erase i, Ring.choose (r j) (k j) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0)

/-- **Three-term identity for modified degenerate Bernoulli polynomials.** Let $n \ge 1$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, write
$\mathfrak{B}_{k,\lambda}(x)$ for the modified degenerate Bernoulli polynomials, and for complex
numbers $s, t, x, y$ put
$\mathfrak{D}_{s,t,\lambda}(x, y) = \sum_{k=0}^{n} (-1)^k \binom{s}{k} \binom{t}{n-k}
\mathfrak{B}_{n-k,\lambda}(x) \mathfrak{B}_{k,\lambda}(y)$, where
$\binom{w}{k} = w(w-1) \cdots (w-k+1)/k!$ is the binomial coefficient with a complex upper
argument. If $r, s, t, x, y, z$ are complex numbers with $r + s + t = n$ and $x + y + z = 1$, then
$r\, \mathfrak{D}_{s,t,\lambda}(x, y) + s\, \mathfrak{D}_{t,r,\lambda}(y, z) +
t\, \mathfrak{D}_{r,s,\lambda}(z, x) = 0$.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(sunpanD) (`jis-2024-24.5.4-cor-2`). -/
public theorem_wanted modifiedDegenerateBernoulli_three_term (n : ℕ) (hn : 1 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) (r s t x y z : ℂ) (hrst : r + s + t = n)
    (hxyz : x + y + z = 1) :
    let D : ℂ → ℂ → ℂ → ℂ → ℂ := fun s t x y =>
      ∑ k ∈ range (n + 1), (-1) ^ k * Ring.choose s k * Ring.choose t (n - k) *
        modifiedDegenerateBernoulli lam (n - k) x * modifiedDegenerateBernoulli lam k y
    r * D s t x y + s * D t r y z + t * D r s z x = 0

/-- **Miki-type identity for modified degenerate Bernoulli numbers.** Let $n \ge 4$, let $\lambda$
be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, write
$\mathfrak{B}_{k,\lambda} = \mathfrak{B}_{k,\lambda}(0)$ for the value at $0$ of the modified
degenerate Bernoulli polynomial $\mathfrak{B}_{k,\lambda}(x)$, and let $H_n = \sum_{k=1}^{n} 1/k$
be the $n$-th harmonic number. Then

$$
\sum_{k=1}^{n-1} \frac{\mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda}}{k} -
\sum_{k=1}^{n-1} \binom{n}{k} \frac{\mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda}}{k} =
\frac{\lambda}{\log(1+\lambda)}\, H_n\, \mathfrak{B}_{n,\lambda} +
\frac{n}{2}\, \mathfrak{B}_{n-1,\lambda},
$$

where $\log$ is the principal branch.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(mikiD) (`jis-2024-24.5.4-cor-2`). -/
public theorem_wanted modifiedDegenerateBernoulli_miki (n : ℕ) (hn : 4 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ k ∈ Icc 1 (n - 1), modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 -
      ∑ k ∈ Icc 1 (n - 1), (n.choose k : ℂ) * modifiedDegenerateBernoulli lam k 0 / k *
        modifiedDegenerateBernoulli lam (n - k) 0 =
      lam / Complex.log (1 + lam) * (harmonic n : ℂ) * modifiedDegenerateBernoulli lam n 0 +
        n / 2 * modifiedDegenerateBernoulli lam (n - 1) 0

/-- **Matiyasevich-type identity for modified degenerate Bernoulli numbers.** Let $n \ge 4$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, and write
$\mathfrak{B}_{k,\lambda} = \mathfrak{B}_{k,\lambda}(0)$ for the value at $0$ of the modified
degenerate Bernoulli polynomial $\mathfrak{B}_{k,\lambda}(x)$. Then

$$
(n+2) \sum_{k=2}^{n-2} \mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda} =
2 \sum_{k=2}^{n-2} \binom{n+2}{k} \mathfrak{B}_{k,\lambda} \mathfrak{B}_{n-k,\lambda} +
\frac{\lambda}{\log(1+\lambda)}\, n(n+1)\, \mathfrak{B}_{n,\lambda},
$$

where $\log$ is the principal branch.

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Corollary 2, equation
(matiyasevichD) (`jis-2024-24.5.4-cor-2`). -/
public theorem_wanted modifiedDegenerateBernoulli_matiyasevich (n : ℕ) (hn : 4 ≤ n) (lam : ℂ)
    (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ((n : ℂ) + 2) * ∑ k ∈ Icc 2 (n - 2),
        modifiedDegenerateBernoulli lam k 0 * modifiedDegenerateBernoulli lam (n - k) 0 =
      2 * ∑ k ∈ Icc 2 (n - 2), ((n + 2).choose k : ℂ) *
          modifiedDegenerateBernoulli lam k 0 * modifiedDegenerateBernoulli lam (n - k) 0 +
        lam / Complex.log (1 + lam) * (n * (n + 1)) * modifiedDegenerateBernoulli lam n 0

/-- **A convolution lemma for modified degenerate Bernoulli polynomials.** Let $m \ge 2$, let
$\lambda$ be a complex number with $\lambda \ne 0$ and $\lambda \ne -1$, let $s_1, \ldots, s_m$ be
nonnegative integers with $S = s_1 + \cdots + s_m$, and let $x_1, \ldots, x_m$ be complex numbers.
Writing $\mathfrak{B}_{n,\lambda}(x)$ for the modified degenerate Bernoulli polynomials,

$$
\sum_{i=1}^{m} s_i\, \mathfrak{B}_{s_i-1,\lambda}(x_i)
\prod_{j \ne i} \mathfrak{B}_{s_j,\lambda}(x_j) =
\sum_{i=1}^{m} s_i \sum_{k_1 + \cdots + k_m = S} \mathfrak{B}_{k_i-1,\lambda}(x_i)
\prod_{j \ne i} \binom{s_j}{k_j} \mathfrak{B}_{k_j,\lambda}(x_j - x_i + [j > i]),
$$

where $k_1, \ldots, k_m$ range over nonnegative integers, $[j > i]$ is $1$ if $j > i$ and $0$
otherwise, and $\mathfrak{B}_{-1,\lambda}$ is read as $0$ (on the left this term has the factor
$s_i = 0$).

Source: Qi-Peng Su and Hao Pan, *Symmetric Identities on Modified Degenerate Bernoulli
Polynomials*, Journal of Integer Sequences 27 (2024), Article 24.5.4, Lemma 3
(`jis-2024-24.5.4-lem-3`). -/
public theorem_wanted modifiedDegenerateBernoulli_lemma_three (m : ℕ) (hm : 2 ≤ m)
    (s : Fin m → ℕ) (x : Fin m → ℂ) (lam : ℂ) (hlam : lam ≠ 0) (hlam1 : lam ≠ -1) :
    ∑ i, (s i : ℂ) * modifiedDegenerateBernoulli lam (s i - 1) (x i) *
        ∏ j ∈ univ.erase i, modifiedDegenerateBernoulli lam (s j) (x j) =
      ∑ i, (s i : ℂ) * ∑ k ∈ Finset.Nat.antidiagonalTuple m (∑ j, s j),
        (if k i = 0 then 0 else modifiedDegenerateBernoulli lam (k i - 1) (x i)) *
          ∏ j ∈ univ.erase i, ((s j).choose (k j) : ℂ) *
            modifiedDegenerateBernoulli lam (k j) (x j - x i + if i < j then 1 else 0)

end

end MetaMathlibExt
