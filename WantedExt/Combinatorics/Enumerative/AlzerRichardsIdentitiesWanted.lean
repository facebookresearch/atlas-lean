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

/-- For `j, n, r ≥ 0` and an `r`-times continuously differentiable `f`:
`∑_{k=0}^{n} (-1)^{k+1} C(n+1, k+1) (f^{k+1+j})^{(r)} = ∑_{k=0}^{r} C(r, k) (f^j)^{(k)}
((1 - f)^{n+1} - 1)^{(r-k)}`.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 1, Equation (2). -/
theorem_wanted sum_iteratedDeriv_pow_one_sub {f : ℝ → ℝ} {r : ℕ} (hf : ContDiff ℝ r f)
    (j n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), (-1 : ℝ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv r (fun y => f y ^ (k + 1 + j)) x =
      ∑ k ∈ range (r + 1), (r.choose k : ℝ) * iteratedDeriv k (fun y => f y ^ j) x *
        iteratedDeriv (r - k) (fun y => (1 - f y) ^ (n + 1) - 1) x

/-- For `j, n, r ≥ 0` and an `r`-times continuously differentiable `f` without zeros:
`∑_{k=0}^{n} C(n+1, k+1) (f^{k+1-j})^{(r)} = ∑_{k=0}^{r} C(r, k) (1 / f^j)^{(k)}
((1 + f)^{n+1} - 1)^{(r-k)}`.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 1, Equation (3). -/
theorem_wanted sum_iteratedDeriv_zpow_one_add {f : ℝ → ℝ} {r : ℕ} (hf : ContDiff ℝ r f)
    (hf0 : ∀ y, f y ≠ 0) (j n : ℕ) (x : ℝ) :
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
        iteratedDeriv r (fun y => f y ^ ((k : ℤ) + 1 - j)) x =
      ∑ k ∈ range (r + 1), (r.choose k : ℝ) * iteratedDeriv k (fun y => 1 / f y ^ j) x *
        iteratedDeriv (r - k) (fun y => (1 + f y) ^ (n + 1) - 1) x

/-- For `n ≥ 0`: `∑_{k=0}^{n} (-1)^k C(n+1, k+1) / C(r+k, k) · S(r+k, k)` is `B_r` for
`0 ≤ r ≤ n` and `B_{n+1} - (-1/2)^{n+1} (n+1)!` for `r = n + 1` (the case `r = n` is
Muthumalai's formula (1)).

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

/-- For `m ≥ 1` and `r ≥ 0`: `∑_{k=0}^{r+m} (-1)^k C(r+m, k) / C(r+k, k) · S(r+k, k) = 0`.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 3, Equation (5). -/
theorem_wanted sum_choose_div_choose_mul_stirlingSecond_eq_zero {m : ℕ} (hm : 1 ≤ m)
    (r : ℕ) :
    ∑ k ∈ range (r + m + 1), (-1 : ℚ) ^ k *
        (((r + m).choose k : ℚ) / ((r + k).choose k : ℚ)) *
          (Nat.stirlingSecond (r + k) k : ℚ) = 0

/-- For `n ≥ 1`: `∑_{k=0}^{n-1} (-1)^k C(n+1, k+2) / C(r+k, k) · S(r+k, k)` is
`r B_{r-1} + (n + r) B_r` for `1 ≤ r ≤ n` and
`(-1/2)^{n+1} (n+1)! + (n+1) B_n + (2n+1) B_{n+1}` for `r = n + 1`.

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

/-- For `j, n ≥ 0`: `∑_{k=0}^{n+1} (-1)^k C(n+1, k) / C(k+j+r, r) · s(k+j+r, k+j)` is `0` for
`0 ≤ r ≤ n` and `(n+1)! / 2^{n+1}` for `r = n + 1`.

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

/-- For `n ≥ 1`, with `T(k, n) = 2^{-k} ∑_{j=0}^{k} C(k, j) (k - 2j)^n` and the Euler numbers
`E_k` (`1 / cosh x = ∑ E_k x^k / k!`) written inline as `0` at odd `k` and MathlibExt's even
secant Euler number `chapter5EulerEven (k / 2)` at even `k`:
`∑_{k=0}^{n-1} C(n, k) E_k ∑_{ν=0}^{n+1} C(n+1, ν) T(ν, n-k) + (2^{n+1} - 1) E_n
= ∑_{k=0}^{n} C(n+1, k+1) T(k, n)`.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 6. -/
theorem_wanted sum_eulerNumber_mul_sum_centralPowerSum {n : ℕ} (hn : 1 ≤ n)
    (T : ℕ → ℕ → ℚ)
    (hT : ∀ k n, T k n = (∑ j ∈ range (k + 1), (k.choose j : ℚ) * ((k : ℚ) - 2 * j) ^ n) / 2 ^ k) :
    ∑ k ∈ range n, (n.choose k : ℚ) * ((if k % 2 = 1 then 0 else chapter5EulerEven (k / 2) : ℤ) : ℚ) *
        ∑ ν ∈ range (n + 2), ((n + 1).choose ν : ℚ) * T ν (n - k) +
      (2 ^ (n + 1) - 1) * ((if n % 2 = 1 then 0 else chapter5EulerEven (n / 2) : ℤ) : ℚ) =
    ∑ k ∈ range (n + 1), ((n + 1).choose (k + 1) : ℚ) * T k n

/-- For `n ≥ 1`, with `A(r, k) = ∑_{j=0}^{k} (-1)^j C(k, j) j! S(r, j)`:
`∑_{k=0}^{n-1} C(n, k) a(k) ∑_{ν=0}^{n+1} C(n+1, ν) A(n-k, ν) + (2^{n+1} - 1) a(n)
= ∑_{k=0}^{n} C(n+1, k+1) A(n, k)`.

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

/-- For `p ≥ 1` and complex `z`: `z^p - z^{\underline{p}} = ∑_{k=0}^{p-1} (-1)^{p-k-1} k^p C(z, k)
C(z-k-1, p-k-1)` (Sabar's formula for `z = n ≥ p`, extended to complex `z`).

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 8, Equation (9). -/
theorem_wanted pow_sub_descPochhammer_eq_sum_choose {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    z ^ p - (descPochhammer ℂ p).eval z =
      ∑ k ∈ range p, (-1 : ℂ) ^ (p - k - 1) * (k : ℂ) ^ p * Ring.choose z k *
        Ring.choose (z - k - 1) (p - k - 1)

/-- For `p ≥ 1` and complex `z ∉ {0, 1, ..., p - 1}`:
`p z^{p-1} - z^p ∑_{k=0}^{p-1} 1/(z-k) = ∑_{k=0}^{p-1} (-1)^{p-k} k^p/(z-k) C(z, k) C(z-k-1, p-k-1)`.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Corollary 1, Equation (10). -/
theorem_wanted mul_pow_pred_sub_pow_mul_sum_inv_eq_sum_choose {p : ℕ} (hp : 1 ≤ p) {z : ℂ}
    (hz : ∀ k < p, z ≠ k) :
    p * z ^ (p - 1) - z ^ p * ∑ k ∈ range p, 1 / (z - k) =
      ∑ k ∈ range p, (-1 : ℂ) ^ (p - k) * (k : ℂ) ^ p / (z - k) * Ring.choose z k *
        Ring.choose (z - k - 1) (p - k - 1)

/-- For `m ≥ 1` and complex `p, x ∉ {-1, ..., -⌊m/2⌋}`:
`∑_{k=0}^{⌊m/2⌋} 2^{-2k} C(m-k, k) C(m+x, m-k) / C(k+p, k)
= (x+1)^{\overline{m}} / m! · ₃F₂(-m/2, (1-m)/2, 1; p+1, x+1; 1)`, where the terminating
hypergeometric series is written out as its finite sum over `0 ≤ n ≤ ⌊m/2⌋` (its terms vanish
beyond).

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

/-- For `m ≥ 1`, complex `p ∉ {-1, ..., -⌊m/2⌋}` and `ν ∈ {1, ..., ⌊m/2⌋}`:
`∑_{k=0}^{⌊m/2⌋} 2^{-2k} C(m-k, k) C(m-ν, m-k) / C(k+p, k)
= 2^{-2ν} (m-ν)!/m! · (-m)^{\overline{2ν}} / (p+1)^{\overline{ν}}
· ₂F₁(ν - m/2, ν - (m-1)/2; ν+p+1; 1)`, where the terminating hypergeometric series is written
out as its finite sum over `0 ≤ n ≤ ⌊m/2⌋ - ν` (its terms vanish beyond).

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

/-- For even `m ≥ 2` and complex `x`: `∑_{k=0}^{m/2} 2^{-2k} C(m-k, k) C(m+x, m-k) /
C(k - m/2 - 1/2, k)` is `x/(x+m/2) C(x+m, m)` for `x ≠ -m/2` and
`2^{-m} (-1)^{m/2} / C((m-1)/2, m/2)` for `x = -m/2`.

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

/-- For odd `m ≥ 1` and complex `x`: `∑_{k=0}^{(m-1)/2} 2^{-2k} C(m-k, k) C(m+x, m-k) /
C(k - m/2 - 1, k)` is `x/(x+(m-1)/2) C(x+m, m)` for `x ≠ (1-m)/2` and
`2^{-m} (-1)^{(m-1)/2} (m+1) / C(m/2, (m-1)/2)` for `x = (1-m)/2`. The upper summation index
`(m-1)/2` is written `m / 2` (natural division, equal for odd `m`).

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

/-- For `m ≥ 1` and complex `x` with every denominator `C(k - m + 1/2 - x, k)`
(`0 ≤ k ≤ ⌊m/2⌋`) nonzero: `∑_{k=0}^{⌊m/2⌋} 2^{-2k} C(m-k, k) C(m+x, m-k) / C(k - m + 1/2 - x, k)`
is `x (x+m-1/2) / ((x+m/2)(x+(m-1)/2)) C(x+m, m)` for `x ≠ -m/2, (1-m)/2`,
`2^{-m} (-1)^{m/2} / C((m-3)/2, m/2)` for even `m` and `x = -m/2`, and
`2^{-m} (-1)^{(m-1)/2} (m+1) / C(m/2 - 1, (m-1)/2)` for odd `m` and `x = (1-m)/2`.

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

/-- With `f(x) = (1 - e^x)/x` for `x ≠ 0` and `f(0) = -1` (passed with its defining equations):
for `k, r ≥ 0`, `(f^k)^{(r)}(0) = (-1)^k S(r+k, k) / C(r+k, k)` (Gradshteyn and Ryzhik,
p. 1047).

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 1. -/
theorem_wanted iteratedDeriv_pow_one_sub_exp_div_self_zero {f : ℝ → ℝ} (hf0 : f 0 = -1)
    (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (k r : ℕ) :
    iteratedDeriv r (fun x => f x ^ k) 0 =
      (-1 : ℝ) ^ k * (Nat.stirlingSecond (r + k) k : ℝ) / ((r + k).choose k : ℝ)

/-- With `f(x) = (1 - e^x)/x` for `x ≠ 0` and `f(0) = -1` (passed with its defining equations):
for `k ≥ 0`, `(1/f)^{(k)}(0) = -B_k`.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 2. -/
theorem_wanted iteratedDeriv_inv_one_sub_exp_div_self_zero {f : ℝ → ℝ} (hf0 : f 0 = -1)
    (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (k : ℕ) :
    iteratedDeriv k (fun x => 1 / f x) 0 = -(bernoulli k : ℝ)

/-- With `f(x) = (1 - e^x)/x` for `x ≠ 0` and `f(0) = -1` (passed with its defining equations)
and `n ≥ 0`: `((1 + f)^{n+1})^{(r)}(0)` is `0` for `0 ≤ r ≤ n` and `(-1/2)^{n+1} (n+1)!` for
`r = n + 1`.

Source: Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and
Various Related Results*, INTEGERS 25 (2025), Article A61, Lemma 3, Equation (26). -/
theorem_wanted iteratedDeriv_one_add_one_sub_exp_div_self_pow_zero {f : ℝ → ℝ}
    (hf0 : f 0 = -1) (hf : ∀ x ≠ 0, f x = (1 - Real.exp x) / x) (n : ℕ) :
    (∀ r ≤ n, iteratedDeriv r (fun x => (1 + f x) ^ (n + 1)) 0 = 0) ∧
      iteratedDeriv (n + 1) (fun x => (1 + f x) ^ (n + 1)) 0 =
        (-1 / 2 : ℝ) ^ (n + 1) * ((n + 1).factorial : ℝ)

end

end MetaMathlibExt
