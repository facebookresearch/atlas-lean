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
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsBernoulliDerivatives
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsBernoulliSum
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsEvenBinomialSum
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsFubiniIdentity
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsHypergeometricSum
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsIdentities
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsReciprocalSum
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsSabarIdentity
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsSignedStirlingSum
public import MathlibExt.Combinatorics.Enumerative.AlzerRichardsVanishingStirlingSum
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
    ∑ k ∈ range n, (n.choose k : ℚ) *
        ((if k % 2 = 1 then 0 else chapter5EulerEven (k / 2) : ℤ) : ℚ) *
        ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℚ) * T ν (n - k) +
      (2 ^ (n + 1) - 1) * ((if n % 2 = 1 then 0 else chapter5EulerEven (n / 2) : ℤ) : ℚ) =
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℚ) * T k n

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

end

end MetaMathlibExt
