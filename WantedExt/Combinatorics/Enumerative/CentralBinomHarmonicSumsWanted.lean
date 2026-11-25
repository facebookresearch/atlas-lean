/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.Binomial
public import MathlibExt.Combinatorics.Enumerative.BinomialHarmonicStirling
public import MathlibExt.Combinatorics.Enumerative.CentralBinomHarmonicRecurrence
public import MathlibExt.Combinatorics.Enumerative.CentralBinomHarmonicSums
public import MathlibExt.Combinatorics.Enumerative.RStirlingSecond
public import MathlibExt.Combinatorics.Enumerative.StirlingSecondExpDeriv
public import MathlibExt.NumberTheory.Harmonic.OddHarmonic

/-!
# Sums of central binomial coefficients with harmonic and odd harmonic numbers

Statements from Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums
Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109
(arXiv 2505.09636).

Conventions shared by the declarations below.

* `S_r(n)`, `S_r^O(n)`, `S_r^H(n)`, `S_r^{2H}(n)` are `centralBinomPowSum a r n` with
  `a = 1`, `oddHarmonic`, `harmonic`, `fun k => harmonic (2k)` (equations (1), (8)-(10)).
* For non-integer `t`, the paper's harmonic numbers `H_t` only occur in differences
  `H_x - H_y` with `x - y ∈ ℤ`; these are written `ψ(x+1) - ψ(y+1)` with
  `ψ = Complex.digamma` (`H_x = ψ(x+1) + γ`). The parameter `t` is taken complex and
  non-integer, and `binom(t, k)` is `Ring.choose t k`.
* `{r \brace k}` is `Nat.stirlingSecond r k`; the `v`-Stirling number
  `{m+v \brace k+v}_v` is `rStirlingSecond (m + v) (k + v) v` (Broder's `{n \brace m}_r`,
  `MathlibExt.Combinatorics.Enumerative.RStirlingSecond`); for `k ≤ n` the paper's
  `{r+n-k \brace n}_{n-k}` is `rStirlingSecond (r + (n - k)) n (n - k)`. `O_n` is
  `oddHarmonic n` (`MathlibExt.NumberTheory.Harmonic.OddHarmonic`).
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- **Recurrence for central binomial sums with odd harmonic numbers.** For a natural number $n$,
let $O_m = \sum_{i=1}^{m} 1/(2i-1)$ be the odd harmonic numbers, $c_n = \binom{2n}{n}/4^n$, and
for natural $r$ let $S_r(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r$ and
$S_r^O(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r O_k$, with $0^0 = 1$. Then
$$S_0^O(n) = c_n \big((2n+1) O_n - 2n\big),$$
and for every $r \ge 1$
$$(2r+1) S_r^O(n) = n^r c_n \big((2n+1) O_n + 1\big) - S_r(n) +
2 \sum_{j=1}^{r-1} \binom{r}{j+1} (-1)^{j+1} S_{r-j}^O(n).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 1 (`integers-2026-A109-thm-1`). -/
public theorem_wanted centralBinomPowSum_oddHarmonic_recursion (n : ℕ) :
    centralBinomPowSum oddHarmonic 0 n =
        (n.centralBinom : ℚ) / 4 ^ n * ((2 * n + 1) * oddHarmonic n - 2 * n) ∧
      ∀ r : ℕ, 1 ≤ r →
        (2 * r + 1) * centralBinomPowSum oddHarmonic r n =
          (n : ℚ) ^ r * ((n.centralBinom : ℚ) / 4 ^ n) * ((2 * n + 1) * oddHarmonic n + 1) -
            centralBinomPowSum 1 r n +
            2 * ∑ j ∈ Icc 1 (r - 1),
              ((r.choose (j + 1) : ℕ) : ℚ) * (-1) ^ (j + 1) *
                centralBinomPowSum oddHarmonic (r - j) n

/-- **Recurrence for central binomial sums with harmonic numbers of even index.** For a natural
number $n$, let $H_m = \sum_{i=1}^{m} 1/i$ be the harmonic numbers, $c_n = \binom{2n}{n}/4^n$,
and for natural $r$ let $S_r(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r$ and
$S_r^{2H}(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r H_{2k}$, with $0^0 = 1$. Then
$$S_0^{2H}(n) = c_n \big((2n+1) H_{2n} - (4n+1)\big) + 1;$$
for every $r \ge 1$
$$(2r+1) S_r^{2H}(n) = n^r c_n \Big((2n+1) H_{2n} + n + \frac{3}{2}\Big) + (-1)^r -
\frac{3}{2} S_r(n) + 2 \sum_{j=1}^{r-1} \binom{r}{j+1} (-1)^{j+1} S_{r-j}^{2H}(n) -
\sum_{j=0}^{r} \binom{r+1}{j} (-1)^{r-j} S_j(n);$$
and
$$S_1^{2H}(n) = \frac{1}{9} c_n \big(3n(2n+1) H_{2n} - 4n^2 + 7n + 3\big) - \frac{1}{3}.$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 3 (`integers-2026-A109-thm-3`). -/
public theorem_wanted centralBinomPowSum_harmonic_two_mul_recursion (n : ℕ) :
    centralBinomPowSum (fun k => harmonic (2 * k)) 0 n =
        (n.centralBinom : ℚ) / 4 ^ n * ((2 * n + 1) * harmonic (2 * n) - (4 * n + 1)) + 1 ∧
      (∀ r : ℕ, 1 ≤ r →
        (2 * r + 1) * centralBinomPowSum (fun k => harmonic (2 * k)) r n =
          (n : ℚ) ^ r * ((n.centralBinom : ℚ) / 4 ^ n) *
                ((2 * n + 1) * harmonic (2 * n) + n + 3 / 2) +
              (-1) ^ r - 3 / 2 * centralBinomPowSum 1 r n +
            2 * ∑ j ∈ Icc 1 (r - 1),
              ((r.choose (j + 1) : ℕ) : ℚ) * (-1) ^ (j + 1) *
                centralBinomPowSum (fun k => harmonic (2 * k)) (r - j) n -
            ∑ j ∈ range (r + 1),
              (((r + 1).choose j : ℕ) : ℚ) * (-1) ^ (r - j) * centralBinomPowSum 1 j n) ∧
      centralBinomPowSum (fun k => harmonic (2 * k)) 1 n =
        1 / 9 * ((n.centralBinom : ℚ) / 4 ^ n) *
            (3 * n * (2 * n + 1) * harmonic (2 * n) - 4 * n ^ 2 + 7 * n + 3) - 1 / 3

/-- **Power sums of $\binom{t}{k}(H_t - H_{t-k})$ in r-Stirling form.** Let $t$ be a complex
number that is not an integer. For complex $x$ write $\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$,
and write $H_x = \psi(x+1) + \gamma$, where $\psi$ is the digamma function and $\gamma$ is the
Euler–Mascheroni constant (only differences $H_x - H_y = \psi(x+1) - \psi(y+1)$ occur below).
Let ${a \brace b}_c$ denote the r-Stirling numbers of the second kind. For all natural numbers
$n$ and $r$ (with $0^0 = 1$),
$$\sum_{k=0}^{n} (-1)^k k^r \binom{t}{k} (H_t - H_{t-k}) =
\sum_{k=0}^{\min(r,n)} (-1)^k k! {r+n-k \brace n}_{n-k} \binom{n-t}{n-k} (H_{k-t} - H_{n-t}).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 4 (`integers-2026-A109-thm-4`). -/
public theorem_wanted sum_choose_harmonic_diff_rStirling (n r : ℕ) (t : ℂ)
    (ht : ∀ m : ℤ, t ≠ m) :
    ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ k * (k : ℂ) ^ r * Ring.choose t k *
          (Complex.digamma (t + 1) - Complex.digamma (t - k + 1)) =
      ∑ k ∈ range (min r n + 1),
        (-1 : ℂ) ^ k * k.factorial * (rStirlingSecond (r + (n - k)) n (n - k) : ℂ) *
          Ring.choose ((n : ℂ) - t) (n - k) *
            (Complex.digamma (k - t + 1) - Complex.digamma (n - t + 1))

/-- **Power sums of $\binom{t}{k}(H_t - H_{t-k})$ for exponents up to three.** Let $n$ be a
natural number and $t$ a complex number that is not an integer. For complex $x$ write
$\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$, and write $H_x = \psi(x+1) + \gamma$, where $\psi$ is
the digamma function and $\gamma$ is the Euler–Mascheroni constant (only differences
$H_x - H_y = \psi(x+1) - \psi(y+1)$ occur below). For natural $r$ let
$L_r = \sum_{k=0}^{n} (-1)^k k^r \binom{t}{k} (H_t - H_{t-k})$ (with $0^0 = 1$), and for natural
$j$ let $A_j = \binom{n-t}{n-j} (H_{j-t} - H_{n-t})$ if $j \le n$ and $A_j = 0$ if $j > n$. Then
$L_0 = A_0$, $L_1 = -A_1 + n A_0$, $L_2 = 2 A_2 - (2n-1) A_1 + n^2 A_0$ and
$L_3 = -6 A_3 + 6(n-1) A_2 - (3n^2 - 3n + 1) A_1 + n^3 A_0$.

These are the cases $r = 0, 1, 2, 3$ of the paper's Theorem 4.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 1 (`integers-2026-A109-prop-1`). -/
public theorem_wanted sum_choose_harmonic_diff_pow_le_three (n : ℕ) (t : ℂ)
    (ht : ∀ m : ℤ, t ≠ m) :
    let L : ℕ → ℂ := fun r => ∑ k ∈ range (n + 1),
      (-1 : ℂ) ^ k * (k : ℂ) ^ r * Ring.choose t k *
        (Complex.digamma (t + 1) - Complex.digamma (t - k + 1))
    let A : ℕ → ℂ := fun j => if n < j then 0 else Ring.choose ((n : ℂ) - t) (n - j) *
      (Complex.digamma (j - t + 1) - Complex.digamma (n - t + 1))
    L 0 = A 0 ∧ L 1 = -A 1 + n * A 0 ∧ L 2 = 2 * A 2 - (2 * n - 1) * A 1 + n ^ 2 * A 0 ∧
      L 3 = -6 * A 3 + 6 * (n - 1) * A 2 - (3 * n ^ 2 - 3 * n + 1) * A 1 + n ^ 3 * A 0

/-- **Odd harmonic central binomial sums via r-Stirling numbers.** For natural numbers $n$ and
$r$, let $O_m = \sum_{i=1}^{m} 1/(2i-1)$ be the odd harmonic numbers, ${a \brace b}_s$ the
r-Stirling numbers of the second kind, and $S_r^O(n) = \sum_{k=0}^{n} \binom{2k}{k} 4^{-k} k^r O_k$,
with $0^0 = 1$. Then
$$S_r^O(n) = \frac{1}{4^n} \sum_{k=0}^{\min(r,n)} (-1)^k k! {r+n-k \brace n}_{n-k} 4^k
\binom{2n+1}{2k+1} \binom{2(n-k)}{n-k} \binom{n}{k}^{-1} (O_{n+1} - O_{k+1}).$$
Moreover $S_0^O(n) = (2n+1) \binom{2n}{n} 4^{-n} (O_{n+1} - 1)$ and
$S_1^O(n) = \frac{n(2n+1)}{3} \binom{2n}{n} 4^{-n} \big(O_{n+1} - \frac{1}{3}\big)$.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 2 (`integers-2026-A109-prop-2`). -/
public theorem_wanted centralBinomPowSum_oddHarmonic_eq_rStirling (n r : ℕ) :
    centralBinomPowSum oddHarmonic r n =
        1 / 4 ^ n * ∑ k ∈ range (min r n + 1),
          (-1) ^ k * k.factorial * (rStirlingSecond (r + (n - k)) n (n - k) : ℚ) * 4 ^ k *
            ((2 * n + 1).choose (2 * k + 1) : ℚ) * ((n - k).centralBinom : ℚ) /
              (n.choose k : ℚ) * (oddHarmonic (n + 1) - oddHarmonic (k + 1)) ∧
      centralBinomPowSum oddHarmonic 0 n =
        (2 * n + 1) * (n.centralBinom : ℚ) / 4 ^ n * (oddHarmonic (n + 1) - 1) ∧
      centralBinomPowSum oddHarmonic 1 n =
        n * (2 * n + 1) / 3 * (n.centralBinom : ℚ) / 4 ^ n * (oddHarmonic (n + 1) - 1 / 3)

/-- **Central binomial sums weighted by $1 - O_{k-1}$, in r-Stirling form.** Let
$O_m = \sum_{j=1}^{m} \frac{1}{2j-1}$ be the odd harmonic numbers (so $O_0 = 0$) and let
${a \brace b}_c$ denote the r-Stirling numbers of the second kind. For all natural numbers $n$ and
$r$,
$$\sum_{k=1}^{n} \frac{k^r \binom{2k}{k}}{4^k (2k-1)} (1 - O_{k-1}) =
\frac{\binom{2n}{n}}{4^n} \sum_{k=0}^{\min(r,n)} (-1)^k k! {r+n-k \brace n}_{n-k}
\binom{n}{k} \frac{4^k}{\binom{2k}{k}} (O_n - O_k),$$
and in particular
$$\sum_{k=1}^{n} \frac{\binom{2k}{k}}{4^k (2k-1)} (1 - O_{k-1}) = \frac{\binom{2n}{n}}{4^n} O_n.$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 3 (`integers-2026-A109-prop-3`). -/
public theorem_wanted sum_centralBinom_one_sub_oddHarmonic_eq_rStirling (n r : ℕ) :
    ∑ k ∈ Icc 1 n, 1 / (4 ^ k * (2 * (k : ℚ) - 1)) * (k : ℚ) ^ r * (k.centralBinom : ℚ) *
          (1 - oddHarmonic (k - 1)) =
        (n.centralBinom : ℚ) / 4 ^ n * ∑ k ∈ range (min r n + 1),
          (-1) ^ k * k.factorial * (rStirlingSecond (r + (n - k)) n (n - k) : ℚ) *
            (n.choose k : ℚ) * 4 ^ k /
            (k.centralBinom : ℚ) * (oddHarmonic n - oddHarmonic k) ∧
      ∑ k ∈ Icc 1 n, 1 / (4 ^ k * (2 * (k : ℚ) - 1)) * (k.centralBinom : ℚ) *
          (1 - oddHarmonic (k - 1)) =
        (n.centralBinom : ℚ) / 4 ^ n * oddHarmonic n

/-- **Power-weighted convolution of $4^k$ with $\binom{2m}{m} O_m$.** Let
$O_m = \sum_{j=1}^{m} \frac{1}{2j-1}$ be the odd harmonic numbers (so $O_0 = 0$) and let
${r \brace k}$ denote the Stirling numbers of the second kind. For all natural numbers $n$ and $r$
(with $0^0 = 1$),
$$\sum_{k=0}^{n} 4^k \binom{2(n-k)}{n-k} k^r O_{n-k} =
(2n+1) \binom{2n}{n} \sum_{k=0}^{r} \frac{4^k\, k!}{(2k+1) \binom{2k}{k}} {r \brace k}
\binom{n}{k} (O_{n+1} - O_{k+1}).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 4 (`integers-2026-A109-prop-4`). -/
public theorem_wanted sum_four_pow_centralBinom_oddHarmonic_eq_stirling (n r : ℕ) :
    ∑ k ∈ range (n + 1), 4 ^ k * ((n - k).centralBinom : ℚ) * (k : ℚ) ^ r * oddHarmonic (n - k) =
      (2 * n + 1) * (n.centralBinom : ℚ) * ∑ k ∈ range (r + 1),
        4 ^ k / (2 * k + 1) * k.factorial * (Nat.stirlingSecond r k : ℚ) * (n.choose k : ℚ) /
          (k.centralBinom : ℚ) * (oddHarmonic (n + 1) - oddHarmonic (k + 1))

/-- **Power-weighted convolution of $4^k$ with $\binom{2m}{m} (1 - O_{m-1})/(2m-1)$.** Let
$O_m = \sum_{j=1}^{m} \frac{1}{2j-1}$ be the odd harmonic numbers (so $O_0 = 0$) and let
${r \brace k}$ denote the Stirling numbers of the second kind. For all natural numbers $n$ and $r$
(with $0^0 = 1$),
$$\sum_{k=0}^{n-1} \frac{4^k}{2(n-k)-1} \binom{2(n-k)}{n-k} k^r (1 - O_{n-k-1}) =
\binom{2n}{n} \sum_{k=0}^{r} \frac{4^k}{\binom{2k}{k}} k! {r \brace k} \binom{n}{k}
(O_n - O_k).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 5 (`integers-2026-A109-prop-5`). -/
public theorem_wanted sum_four_pow_centralBinom_one_sub_oddHarmonic_eq_stirling (n r : ℕ) :
    ∑ k ∈ range n, 4 ^ k / (2 * ((n - k : ℕ) : ℚ) - 1) * ((n - k).centralBinom : ℚ) *
        (k : ℚ) ^ r * (1 - oddHarmonic (n - k - 1)) =
      (n.centralBinom : ℚ) * ∑ k ∈ range (r + 1),
        4 ^ k / (k.centralBinom : ℚ) * k.factorial * (Nat.stirlingSecond r k : ℚ) *
          (n.choose k : ℚ) * (oddHarmonic n - oddHarmonic k)

/-- **Alternating reciprocal central binomial sum with $O_{n+1} - O_{k+1}$.** Let
$O_m = \sum_{j=1}^{m} \frac{1}{2j-1}$ be the odd harmonic numbers (so $O_0 = 0$) and let
${r \brace k}$ denote the Stirling numbers of the second kind. For all natural numbers $n$ and $r$
(with $0^0 = 1$),
$$\sum_{k=0}^{n} \frac{(-1)^k}{2k+1} \binom{n}{k} \frac{4^k}{\binom{2k}{k}} k^r
(O_{n+1} - O_{k+1}) =
\frac{1}{(2n+1)\binom{2n}{n}} \sum_{k=0}^{\min(r,n)} (-1)^k k! {r \brace k} 4^k
\binom{2(n-k)}{n-k} O_{n-k}.$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 6 (`integers-2026-A109-prop-6`). -/
public theorem_wanted sum_alternating_inv_centralBinom_oddHarmonic_eq_stirling (n r : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k / (2 * (k : ℚ) + 1) * (n.choose k : ℚ) * 4 ^ k /
        (k.centralBinom : ℚ) * (k : ℚ) ^ r * (oddHarmonic (n + 1) - oddHarmonic (k + 1)) =
      1 / ((2 * n + 1) * (n.centralBinom : ℚ)) * ∑ k ∈ range (min r n + 1),
        (-1) ^ k * k.factorial * (Nat.stirlingSecond r k : ℚ) * 4 ^ k *
          ((n - k).centralBinom : ℚ) * oddHarmonic (n - k)

/-- **Alternating reciprocal central binomial sum with $O_n - O_k$.** Let
$O_m = \sum_{j=1}^{m} \frac{1}{2j-1}$ be the odd harmonic numbers (so $O_0 = 0$) and let
${r \brace k}$ denote the Stirling numbers of the second kind. For all natural numbers $n$ and $r$
(with $0^0 = 1$),
$$\sum_{k=0}^{n} (-1)^k \binom{n}{k} \frac{4^k}{\binom{2k}{k}} k^r (O_n - O_k) =
\frac{1}{\binom{2n}{n}} \sum_{k=0}^{\min(r,\, n-1)} \frac{(-1)^k}{2(n-k)-1}\, k! {r \brace k}
4^k \binom{2(n-k)}{n-k} (1 - O_{n-k-1}),$$
where the right-hand sum is empty when $n = 0$.

The paper's right-hand sum runs over all $k \le r$; its term $k = n$ vanishes there because
$1 - O_{-1} = 0$, so it is dropped here.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 7 (`integers-2026-A109-prop-7`). -/
public theorem_wanted sum_alternating_inv_centralBinom_oddHarmonic_sub_eq_stirling (n r : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℚ) * 4 ^ k / (k.centralBinom : ℚ) *
        (k : ℚ) ^ r * (oddHarmonic n - oddHarmonic k) =
      1 / (n.centralBinom : ℚ) * ∑ k ∈ range (min (r + 1) n),
        (-1) ^ k / (2 * ((n - k : ℕ) : ℚ) - 1) * k.factorial * (Nat.stirlingSecond r k : ℚ) *
          4 ^ k * ((n - k).centralBinom : ℚ) * (1 - oddHarmonic (n - k - 1))

/-- **Power sums of $\binom{n-t}{n-k}(H_{k-t} - H_{n-t})$ in Stirling form.** Let $t$ be a
complex number that is not an integer. For complex $x$ write
$\binom{x}{k} = x(x-1)\cdots(x-k+1)/k!$, and write $H_x = \psi(x+1) + \gamma$, where $\psi$ is
the digamma function and $\gamma$ is the Euler–Mascheroni constant (only differences
$H_x - H_y = \psi(x+1) - \psi(y+1)$ occur below). Let ${r \brace k}$ denote the Stirling numbers
of the second kind. For all natural numbers $n$ and $r$ (with $0^0 = 1$),
$$\sum_{k=0}^{n} (-1)^{n-k} \binom{n-t}{n-k} k^r (H_{k-t} - H_{n-t}) =
\sum_{k=0}^{\min(r,n)} k! {r \brace k} \binom{t}{n-k} (H_t - H_{t-n+k}).$$

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 6 (`integers-2026-A109-thm-6`). -/
public theorem_wanted sum_choose_sub_harmonic_diff_stirling_dual (n r : ℕ) (t : ℂ)
    (ht : ∀ m : ℤ, t ≠ m) :
    ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ (n - k) * Ring.choose ((n : ℂ) - t) (n - k) * (k : ℂ) ^ r *
          (Complex.digamma (k - t + 1) - Complex.digamma (n - t + 1)) =
      ∑ k ∈ range (min r n + 1),
        (k.factorial : ℂ) * (Nat.stirlingSecond r k : ℂ) * Ring.choose t (n - k) *
          (Complex.digamma (t + 1) - Complex.digamma (t - n + k + 1))

end

end MetaMathlibExt
