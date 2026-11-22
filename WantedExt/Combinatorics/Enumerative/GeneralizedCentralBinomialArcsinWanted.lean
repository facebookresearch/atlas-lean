/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Central

/-!
# Power series with reciprocals of central binomial coefficients via `arcsin`

Statements from Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central
Binomial Coefficients*, INTEGERS 26 (2026), Article A2.

The paper's rational polynomials `S_n`, `T_{n-2}`, `M_{n-1}`, `N_{n-2}` and constants `c_n`, `d_n`
(Definitions 1-4) are defined here through their coefficient recursions. The antiderivative
lemmas are stated as derivative identities and the corollaries (the case `m = 1` of the main
theorems) as identities of real functions, both on `0 < x < 1`, where every square root, power
and `arcsin` is the real one.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- The coefficients `s_k` of `S_n(x) = ∑_{k=0}^n s_k x^k`: `s_0 = 1/(1/2 - n)` and
`s_k = (k - 1 - n)/(k - n + 1/2) · s_{k-1}` for `1 ≤ k ≤ n`.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 1. -/
def zuritaSCoeff (n : ℕ) : ℕ → ℚ
  | 0 => 1 / (1 / 2 - n)
  | k + 1 => ((k : ℚ) - n) / ((k : ℚ) + 1 - n + 1 / 2) * zuritaSCoeff n k

/-- The constant `c_n = s_n/2 - 1` (the paper's convention `c_1 = 1` agrees with this formula).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaC (n : ℕ) : ℚ :=
  zuritaSCoeff n n / 2 - 1

/-- The coefficients of `T_{n-2}` in reverse order: `zuritaTCoeffRev n i = t_{n-2-i}`, with
`t_{n-2} = -s_{n-1}/2 - c_n` and `t_{k-1} = ((k + 1 - n) t_k + s_k/2)/(k - n)` for
`k = n-2, …, 1`.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaTCoeffRev (n : ℕ) : ℕ → ℚ
  | 0 => -zuritaSCoeff n (n - 1) / 2 - zuritaC n
  | i + 1 => ((((n - 2 - i : ℕ) : ℚ) + 1 - n) * zuritaTCoeffRev n i +
      zuritaSCoeff n (n - 2 - i) / 2) / (((n - 2 - i : ℕ) : ℚ) - n)

/-- The coefficient `t_k` of `T_{n-2}(x) = ∑_{k=0}^{n-2} t_k x^k` (`T_{-1} = 0` for `n = 1`).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
def zuritaTCoeff (n k : ℕ) : ℚ :=
  zuritaTCoeffRev n (n - 2 - k)

/-- The coefficients `m_k` of `M_{n-1}(x) = ∑_{k=0}^{n-1} m_k x^k`: `m_0 = 2/(2n - 1)` and
`m_k = 2(k - n)/(2k - 2n + 1) · m_{k-1}` for `1 ≤ k ≤ n - 1`.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 3. -/
def zuritaMCoeff (n : ℕ) : ℕ → ℚ
  | 0 => 2 / (2 * n - 1)
  | k + 1 => 2 * ((k : ℚ) + 1 - n) / (2 * ((k : ℚ) + 1) - 2 * n + 1) * zuritaMCoeff n k

/-- The constant `d_n = m_{n-1}/2` (the paper's convention `d_1 = 1` agrees with this formula).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
def zuritaD (n : ℕ) : ℚ :=
  zuritaMCoeff n (n - 1) / 2

/-- The coefficient `m_k / (2(k - n + 1))` of `N_{n-2}(x) = (1/2) ∑_{k=0}^{n-2} m_k x^k/(k - n + 1)`.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
def zuritaNCoeff (n k : ℕ) : ℚ :=
  zuritaMCoeff n k / 2 / ((k : ℚ) - n + 1)

/-- Rows of the paper's Tables 1-4: `S_2 = -2/3 - (8/3)x + (16/3)x^2`, `c_2 = 5/3`,
`c_4 = 93/35`, `T_1 = -1/10 - (3/5)x` (`n = 3`), `M_2 = 2/5 + (8/15)x + (16/15)x^2`,
`d_3 = 8/15`, and `N_1 = -(8x + 3)/30` (`n = 3`).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Tables 1-4. -/
theorem zurita_table_values :
    (List.range 3).map (zuritaSCoeff 2) = [-2 / 3, -8 / 3, 16 / 3] ∧ zuritaC 2 = 5 / 3 ∧
      zuritaC 4 = 93 / 35 ∧ (List.range 2).map (zuritaTCoeff 3) = [-1 / 10, -3 / 5] ∧
      (List.range 3).map (zuritaMCoeff 3) = [2 / 5, 8 / 15, 16 / 15] ∧ zuritaD 3 = 8 / 15 ∧
      (List.range 2).map (zuritaNCoeff 3) = [-3 / 30, -8 / 30] := by
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, zuritaC, zuritaD, zuritaTCoeff, zuritaNCoeff]
  norm_num [zuritaSCoeff, zuritaTCoeffRev, zuritaMCoeff, zuritaC]

/-- `S_n(x) = ∑_{k=0}^n s_k x^k` as a real function.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 1. -/
noncomputable def zuritaS (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), (zuritaSCoeff n k : ℝ) * x ^ k

/-- `T_{n-2}(x) = ∑_{k=0}^{n-2} t_k x^k` as a real function (`0` for `n = 1`).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2. -/
noncomputable def zuritaT (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n - 1), (zuritaTCoeff n k : ℝ) * x ^ k

/-- `M_{n-1}(x) = ∑_{k=0}^{n-1} m_k x^k` as a real function.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 3. -/
noncomputable def zuritaM (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range n, (zuritaMCoeff n k : ℝ) * x ^ k

/-- `N_{n-2}(x)` as a real function (`0` for `n = 1`).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Definition 4. -/
noncomputable def zuritaN (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n - 1), (zuritaNCoeff n k : ℝ) * x ^ k

/-- For `n ≥ 1`, an antiderivative of `x^{-n-1/2} arcsin(√x)/(1 - x)^{3/2}` is
`log(x - 1) + c_n log x + T_{n-2}(x)/x^{n-1} + arcsin(√x) S_n(x)/(x^{n-1/2} √(1 - x))`, stated as
a derivative identity on `0 < x < 1` (`Real.log` of the negative number `x - 1` is
`log |x - 1|`).

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Lemma 1 (`integers-2026-A2-lem-1`). -/
public theorem_wanted hasDerivAt_zurita_antiderivative_one {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => Real.log (y - 1) + (zuritaC n : ℝ) * Real.log y +
        zuritaT n y / y ^ (n - 1) +
        Real.arcsin (Real.sqrt y) * zuritaS n y / (y ^ ((n : ℝ) - 1 / 2) * Real.sqrt (1 - y)))
      (x ^ (-(n : ℝ) - 1 / 2) * Real.arcsin (Real.sqrt x) / (1 - x) ^ ((3 : ℝ) / 2)) x

/-- For `n ≥ 1`, an antiderivative of `x^{-n-1/2} arcsin(√x)/√(1 - x)` is
`d_n log x - arcsin(√x) √(x(1 - x)) M_{n-1}(x)/x^n + N_{n-2}(x)/x^{n-1}`, stated as a derivative
identity on `0 < x < 1`.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Lemma 2 (`integers-2026-A2-lem-2`). -/
public theorem_wanted hasDerivAt_zurita_antiderivative_two {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun y => (zuritaD n : ℝ) * Real.log y -
        Real.arcsin (Real.sqrt y) * Real.sqrt (y * (1 - y)) * zuritaM n y / y ^ n +
        zuritaN n y / y ^ (n - 1))
      (x ^ (-(n : ℝ) - 1 / 2) * Real.arcsin (Real.sqrt x) / Real.sqrt (1 - x)) x

/-- For `n ≥ 1` and `0 < x < 1`,
`∑_{k > n} 4^k x^k/((k - n) binom(2k, k)) = x T_{n-2}(x) + √(x/(1 - x)) arcsin(√x) S_n(x)
+ ∑_{k=0}^{n-1} (1 - 4^k/binom(2k, k)) x^k/(k - n)
- ((1/2) ∑_{k=1}^n 4^k s_{n-k}/(k binom(2k, k))) x^n`.
The printed range `|x| < 4` is corrected to `|x| < 1` (Theorem 1's `|x| < 4^{m-1}` at `m = 1`):
since `binom(2k, k) ≤ 4^k` the series diverges for `x ≥ 1`.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Corollary 1 (`integers-2026-A2-cor-1`). -/
public theorem_wanted tsum_four_pow_div_sub_mul_centralBinom {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) * Nat.centralBinom (k + n + 1)) =
      x * zuritaT n x + Real.sqrt (x / (1 - x)) * Real.arcsin (Real.sqrt x) * zuritaS n x +
        ∑ k ∈ range n, (1 - (4 : ℝ) ^ k / Nat.centralBinom k) * x ^ k / ((k : ℝ) - n) -
        (1 / 2 * ∑ k ∈ Icc 1 n, (4 : ℝ) ^ k * (zuritaSCoeff n (n - k) : ℝ) /
          ((k : ℝ) * Nat.centralBinom k)) * x ^ n

/-- For `n ≥ 1` and `0 < x < 1`,
`∑_{k > n} 4^k x^k/((k - n)^2 binom(2k, k)) = (2^{2n+1} x^n/binom(2n, n)) arcsin(√x)^2
- arcsin(√x) √(x(1 - x)) ∑_{k=0}^{n-1} s^{(n)}_k M_{n-k-1}(x) x^k + ∑_{k=1}^{n-1} r_k x^k + q x^n`
with `r_k = t^{(n-2)}_{k-1}/(k - n) + (1/2) ∑_{l<k} s^{(n)}_l m^{(n-l-1)}_{k-l-1}/(k - n)
+ 4^k (4^{-k} - 1/binom(2k, k))/(k - n)^2` and
`q = -2^{2n+1}/binom(2n, n) + ∑_{l=0}^{n-2} s^{(n)}_l (4^{n-l}/((n - l) binom(2(n-l), n-l))
- (1/2) ∑_{p=1}^{n-l-1} 4^p m^{(n-l-1)}_{n-l-1-p}/(p(2p + 1) binom(2p, p)))`. Here
`M_{n-k-1}` and its coefficients `m^{(n-l-1)}` are those of Definition 3 with parameter `n - k`,
resp. `n - l`.

Source: Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial
Coefficients*, INTEGERS 26 (2026), Article A2, Corollary 2 (`integers-2026-A2-cor-2`). -/
public theorem_wanted tsum_four_pow_div_sub_sq_mul_centralBinom {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    let r : ℕ → ℝ := fun k =>
      ((zuritaTCoeff n (k - 1) : ℝ) / ((k : ℝ) - n) +
          1 / 2 * ∑ l ∈ range k, (zuritaSCoeff n l * zuritaMCoeff (n - l) (k - l - 1) : ℝ) /
            ((k : ℝ) - n)) +
        (4 : ℝ) ^ k / ((k : ℝ) - n) ^ 2 * (1 / (4 : ℝ) ^ k - 1 / Nat.centralBinom k)
    let q : ℝ := -(2 : ℝ) ^ (2 * n + 1) / Nat.centralBinom n +
      ∑ l ∈ range (n - 1), (zuritaSCoeff n l : ℝ) *
        ((4 : ℝ) ^ (n - l) / (((n - l : ℕ) : ℝ) * Nat.centralBinom (n - l)) -
          1 / 2 * ∑ p ∈ Icc 1 (n - l - 1), (4 : ℝ) ^ p * (zuritaMCoeff (n - l) (n - l - 1 - p) : ℝ) /
            ((p : ℝ) * (2 * p + 1) * Nat.centralBinom p))
    ∑' k : ℕ, (4 : ℝ) ^ (k + n + 1) * x ^ (k + n + 1) /
        (((k : ℝ) + 1) ^ 2 * Nat.centralBinom (k + n + 1)) =
      (2 : ℝ) ^ (2 * n + 1) * x ^ n / Nat.centralBinom n * Real.arcsin (Real.sqrt x) ^ 2 -
        Real.arcsin (Real.sqrt x) * Real.sqrt (x * (1 - x)) *
          ∑ k ∈ range n, (zuritaSCoeff n k : ℝ) * zuritaM (n - k) x * x ^ k +
        ∑ k ∈ Icc 1 (n - 1), r k * x ^ k + q * x ^ n

end

end MetaMathlibExt
