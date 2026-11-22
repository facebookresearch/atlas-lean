/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.RingTheory.Binomial
public import MathlibExt.Combinatorics.Enumerative.RStirlingSecond
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

/-- The weighted central binomial sum `∑_{k=0}^n 2^{-2k} k^r C(2k,k) a_k`. With `a = 1`,
`oddHarmonic`, `harmonic` and `k ↦ harmonic (2k)` it is the paper's `S_r(n)`,
`S_r^O(n)`, `S_r^H(n)` and `S_r^{2H}(n)` (at `r = 0`, `0^0 = 1` gives the paper's `S_0`).

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
equations (1), (8), (9), (10). -/
public def centralBinomPowSum (a : ℕ → ℚ) (r n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), (k.centralBinom : ℚ) / 4 ^ k * (k : ℚ) ^ r * a k

/-- The `n = 0` value: `centralBinomPowSum a r 0 = 0^r a_0`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
equations (1), (8)-(10). -/
public theorem centralBinomPowSum_zero (a : ℕ → ℚ) (r : ℕ) :
    centralBinomPowSum a r 0 = (0 : ℚ) ^ r * a 0 := by
  simp [centralBinomPowSum]

/-- The partial-sum step: adding the term `k = n + 1`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
equations (1), (8)-(10). -/
public theorem centralBinomPowSum_succ (a : ℕ → ℚ) (r n : ℕ) :
    centralBinomPowSum a r (n + 1) =
      centralBinomPowSum a r n +
        ((n + 1).centralBinom : ℚ) / 4 ^ (n + 1) * ((n + 1 : ℕ) : ℚ) ^ r * a (n + 1) := by
  rw [centralBinomPowSum, sum_range_succ]
  rfl

/-- Theorem 1: `S_0^O(n) = 2^{-2n} C(2n,n) ((2n+1) O_n - 2n)`, and for `r ≥ 1`
`(2r+1) S_r^O(n) = n^r 2^{-2n} C(2n,n) ((2n+1) O_n + 1) - S_r(n)
+ 2 ∑_{j=1}^{r-1} C(r, j+1) (-1)^{j+1} S_{r-j}^O(n)`.

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

/-- Theorem 2: `S_0^H(n) = (2n+1) 2^{-2n} C(2n,n) (H_n - 2) + 2`, and for `r ≥ 1`
`(2r+1) S_r^H(n) = n^r (2n+1) 2^{-2n} C(2n,n) (H_n + 1) + 2(-1)^r - S_r(n)
+ 2 ∑_{j=1}^{r-1} C(r,j+1) (-1)^{j+1} S_{r-j}^H(n) - 2 ∑_{j=0}^{r} C(r+1,j) (-1)^{r-j} S_j(n)`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 2 (`integers-2026-A109-thm-2`). -/
public theorem_wanted centralBinomPowSum_harmonic_recursion (n : ℕ) :
    centralBinomPowSum harmonic 0 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (harmonic n - 2) + 2 ∧
      ∀ r : ℕ, 1 ≤ r →
        (2 * r + 1) * centralBinomPowSum harmonic r n =
          (n : ℚ) ^ r * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (harmonic n + 1) +
              2 * (-1) ^ r - centralBinomPowSum 1 r n +
            2 * ∑ j ∈ Icc 1 (r - 1),
              ((r.choose (j + 1) : ℕ) : ℚ) * (-1) ^ (j + 1) * centralBinomPowSum harmonic (r - j) n -
            2 * ∑ j ∈ range (r + 1),
              (((r + 1).choose j : ℕ) : ℚ) * (-1) ^ (r - j) * centralBinomPowSum 1 j n

/-- Theorem 3: `S_0^{2H}(n) = 2^{-2n} C(2n,n) ((2n+1) H_{2n} - (4n+1)) + 1`; for `r ≥ 1`
`(2r+1) S_r^{2H}(n) = n^r 2^{-2n} C(2n,n) ((2n+1) H_{2n} + n + 3/2) + (-1)^r - (3/2) S_r(n)
+ 2 ∑_{j=1}^{r-1} C(r,j+1) (-1)^{j+1} S_{r-j}^{2H}(n) - ∑_{j=0}^{r} C(r+1,j) (-1)^{r-j} S_j(n)`;
and `S_1^{2H}(n) = (1/9) 2^{-2n} C(2n,n) (3n(2n+1) H_{2n} - 4n^2 + 7n + 3) - 1/3`.

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

/-- Corollary 1: closed forms of `S_r^O(n)` for `r = 1, 2, 3` in terms of `O_{n+1}`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Corollary 1 (`integers-2026-A109-cor-1`). -/
public theorem_wanted centralBinomPowSum_oddHarmonic_one_two_three (n : ℕ) :
    centralBinomPowSum oddHarmonic 1 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (n / 3) * (oddHarmonic (n + 1) - 1 / 3) ∧
      centralBinomPowSum oddHarmonic 2 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (n / 15) *
          ((3 * n + 2) * oddHarmonic (n + 1) - (9 * n + 16) / 15) ∧
      centralBinomPowSum oddHarmonic 3 n =
        (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) * (n / 105) *
          ((15 * n ^ 2 + 18 * n + 2) * oddHarmonic (n + 1) -
            (225 * n ^ 2 + 648 * n + 352) / 105)

/-- Corollary 2: closed forms of `S_r^H(n)` for `r = 1, 2, 3`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Corollary 2 (`integers-2026-A109-cor-2`). -/
public theorem_wanted centralBinomPowSum_harmonic_one_two_three (n : ℕ) :
    centralBinomPowSum harmonic 1 n =
        1 / 3 * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) *
            (n * harmonic n - 2 * n / 3 + 2) - 2 / 3 ∧
      centralBinomPowSum harmonic 2 n =
        1 / 5 * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) *
            (n / 3 * (3 * n + 2) * harmonic n - 2 / 45 * (9 * n ^ 2 - 14 * n + 15)) + 2 / 15 ∧
      centralBinomPowSum harmonic 3 n =
        1 / 7 * (2 * n + 1) * ((n.centralBinom : ℚ) / 4 ^ n) *
            (n / 15 * (15 * n ^ 2 + 18 * n + 2) * harmonic n -
              2 / 1575 * (225 * n ^ 3 - 297 * n ^ 2 + 37 * n + 105)) + 2 / 105

/-- Lemma 1: for natural `k`, `r`, `v`,
`d^r/dx^r (1 - e^x)^k |_{x=0} = ∑_{p=0}^k (-1)^p C(k,p) p^r = (-1)^k k! {r \brace k}` and
`d^r/dx^r (1 - e^x)^k e^{vx} |_{x=0} = ∑_{p=0}^k (-1)^p C(k,p) (v+p)^r
= (-1)^k k! {r+v \brace k+v}_v`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Lemma 1 (`integers-2026-A109-lem-1`). -/
public theorem_wanted iteratedDeriv_one_sub_exp_pow (k r v : ℕ) :
    (iteratedDeriv r (fun x : ℝ => (1 - Real.exp x) ^ k) 0 =
        ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * (p : ℝ) ^ r ∧
      ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * (p : ℝ) ^ r =
        (-1) ^ k * k.factorial * (Nat.stirlingSecond r k : ℝ)) ∧
    (iteratedDeriv r (fun x : ℝ => (1 - Real.exp x) ^ k * Real.exp (v * x)) 0 =
        ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * ((v + p : ℕ) : ℝ) ^ r ∧
      ∑ p ∈ range (k + 1), (-1 : ℝ) ^ p * (k.choose p : ℝ) * ((v + p : ℕ) : ℝ) ^ r =
        (-1) ^ k * k.factorial * (rStirlingSecond (r + v) (k + v) v : ℝ))

/-- Theorem 4: for natural `n`, `r` and non-integer `t`,
`∑_{k=0}^n (-1)^k k^r C(t,k) (H_t - H_{t-k})
= ∑_{k=0}^{r} (-1)^k k! {r+n-k \brace n}_{n-k} C(n-t, n-k) (H_{k-t} - H_{n-t})`,
with the right sum over `k ≤ min(r, n)`.

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

/-- Proposition 1: the cases `r = 0, 1, 2, 3` of Theorem 4, for non-integer `t`. The term
`A j = C(n-t, n-j) (H_{j-t} - H_{n-t})` is `0` for `j > n`, matching Theorem 4's sum over
`k ≤ min(r, n)`.

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

/-- Proposition 2: for natural `n`, `r`,
`S_r^O(n) = 2^{-2n} ∑_{k=0}^r (-1)^k k! {r+n-k \brace n}_{n-k} 2^{2k} C(2n+1,2k+1)
C(2(n-k),n-k) C(n,k)^{-1} (O_{n+1} - O_{k+1})` (sum over `k ≤ min(r,n)`); in particular
`S_0^O(n) = (2n+1) C(2n,n) 2^{-2n} (O_{n+1} - 1)` and
`S_1^O(n) = n(2n+1)/3 C(2n,n) 2^{-2n} (O_{n+1} - 1/3)`.

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

/-- Proposition 3: for natural `n`, `r`,
`∑_{k=1}^n 2^{-2k}/(2k-1) k^r C(2k,k) (1 - O_{k-1})
= 2^{-2n} C(2n,n) ∑_{k=0}^r (-1)^k k! {r+n-k \brace n}_{n-k} C(n,k) 2^{2k} C(2k,k)^{-1}
(O_n - O_k)` (sum over `k ≤ min(r,n)`); in particular
`∑_{k=1}^n 2^{-2k}/(2k-1) C(2k,k) (1 - O_{k-1}) = 2^{-2n} C(2n,n) O_n`.

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

/-- Proposition 4: for natural `n`, `r`,
`∑_{k=0}^n 2^{2k} C(2(n-k),n-k) k^r O_{n-k}
= (2n+1) C(2n,n) ∑_{k=0}^r 2^{2k}/(2k+1) k! {r \brace k} C(n,k) C(2k,k)^{-1} (O_{n+1} - O_{k+1})`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 4 (`integers-2026-A109-prop-4`). -/
public theorem_wanted sum_four_pow_centralBinom_oddHarmonic_eq_stirling (n r : ℕ) :
    ∑ k ∈ range (n + 1), 4 ^ k * ((n - k).centralBinom : ℚ) * (k : ℚ) ^ r * oddHarmonic (n - k) =
      (2 * n + 1) * (n.centralBinom : ℚ) * ∑ k ∈ range (r + 1),
        4 ^ k / (2 * k + 1) * k.factorial * (Nat.stirlingSecond r k : ℚ) * (n.choose k : ℚ) /
          (k.centralBinom : ℚ) * (oddHarmonic (n + 1) - oddHarmonic (k + 1))

/-- Proposition 5: for natural `n`, `r`,
`∑_{k=0}^{n-1} 2^{2k}/(2(n-k)-1) C(2(n-k),n-k) k^r (1 - O_{n-k-1})
= C(2n,n) ∑_{k=0}^r 2^{2k} C(2k,k)^{-1} k! {r \brace k} C(n,k) (O_n - O_k)`.

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 5 (`integers-2026-A109-prop-5`). -/
public theorem_wanted sum_four_pow_centralBinom_one_sub_oddHarmonic_eq_stirling (n r : ℕ) :
    ∑ k ∈ range n, 4 ^ k / (2 * ((n - k : ℕ) : ℚ) - 1) * ((n - k).centralBinom : ℚ) *
        (k : ℚ) ^ r * (1 - oddHarmonic (n - k - 1)) =
      (n.centralBinom : ℚ) * ∑ k ∈ range (r + 1),
        4 ^ k / (k.centralBinom : ℚ) * k.factorial * (Nat.stirlingSecond r k : ℚ) *
          (n.choose k : ℚ) * (oddHarmonic n - oddHarmonic k)

/-- Proposition 6: for natural `n`, `r`,
`∑_{k=0}^n (-1)^k/(2k+1) C(n,k) 2^{2k} C(2k,k)^{-1} k^r (O_{n+1} - O_{k+1})
= 1/(2n+1) C(2n,n)^{-1} ∑_{k=0}^r (-1)^k k! {r \brace k} 2^{2k} C(2(n-k),n-k) O_{n-k}`
(right sum over `k ≤ min(r,n)`).

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 6 (`integers-2026-A109-prop-6`). -/
public theorem_wanted sum_alternating_inv_centralBinom_oddHarmonic_eq_stirling (n r : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k / (2 * (k : ℚ) + 1) * (n.choose k : ℚ) * 4 ^ k /
        (k.centralBinom : ℚ) * (k : ℚ) ^ r * (oddHarmonic (n + 1) - oddHarmonic (k + 1)) =
      1 / ((2 * n + 1) * (n.centralBinom : ℚ)) * ∑ k ∈ range (min r n + 1),
        (-1) ^ k * k.factorial * (Nat.stirlingSecond r k : ℚ) * 4 ^ k *
          ((n - k).centralBinom : ℚ) * oddHarmonic (n - k)

/-- Proposition 7: for natural `n`, `r`,
`∑_{k=0}^n (-1)^k C(n,k) 2^{2k} C(2k,k)^{-1} k^r (O_n - O_k)
= C(2n,n)^{-1} ∑_{k=0}^r (-1)^k/(2(n-k)-1) k! {r \brace k} 2^{2k} C(2(n-k),n-k)
(1 - O_{n-k-1})`, with the right sum over `k ≤ r`, `k < n` (the `k = n` term, where the
paper's derivation gives `1 - O_{-1} = 0`, is dropped).

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Proposition 7 (`integers-2026-A109-prop-7`). -/
public theorem_wanted sum_alternating_inv_centralBinom_oddHarmonic_sub_eq_stirling (n r : ℕ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℚ) * 4 ^ k / (k.centralBinom : ℚ) *
        (k : ℚ) ^ r * (oddHarmonic n - oddHarmonic k) =
      1 / (n.centralBinom : ℚ) * ∑ k ∈ range (min (r + 1) n),
        (-1) ^ k / (2 * ((n - k : ℕ) : ℚ) - 1) * k.factorial * (Nat.stirlingSecond r k : ℚ) *
          4 ^ k * ((n - k).centralBinom : ℚ) * (1 - oddHarmonic (n - k - 1))

/-- Theorem 5: for natural `n`, `r` and non-integer `t`,
`∑_{k=0}^n (-1)^k C(t, n-k) k^r (H_t - H_{t-n+k})
= (-1)^n ∑_{k=0}^r k! {r \brace k} C(n-t, n-k) (H_{k-t} - H_{n-t})`
(right sum over `k ≤ min(r,n)`).

Source: Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving
Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109,
Theorem 5 (`integers-2026-A109-thm-5`). -/
public theorem_wanted sum_choose_sub_harmonic_diff_stirling (n r : ℕ) (t : ℂ)
    (ht : ∀ m : ℤ, t ≠ m) :
    ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ k * Ring.choose t (n - k) * (k : ℂ) ^ r *
          (Complex.digamma (t + 1) - Complex.digamma (t - n + k + 1)) =
      (-1) ^ n * ∑ k ∈ range (min r n + 1),
        (k.factorial : ℂ) * (Nat.stirlingSecond r k : ℂ) * Ring.choose ((n : ℂ) - t) (n - k) *
          (Complex.digamma (k - t + 1) - Complex.digamma (n - t + 1))

/-- Theorem 6: for natural `n`, `r` and non-integer `t`,
`∑_{k=0}^n (-1)^{n-k} C(n-t, n-k) k^r (H_{k-t} - H_{n-t})
= ∑_{k=0}^r k! {r \brace k} C(t, n-k) (H_t - H_{t-n+k})` (right sum over `k ≤ min(r,n)`).

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
