/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The equation `Σ_{j=1}^k j U_j^p = U_n^q` for Lucas sequences

Statements from Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun,
*Extension of the Equation `Σ_{j=1}^k j F_j^p = F_n^q` to a Family of Lucas Sequences*, The
Fibonacci Quarterly 62 (2024), no. 3 (primary text: arXiv:2607.09105).

`U_n(x, y)` and `V_n(x, y)` are `lucasU P n` and `lucasV P n` with `x = P.p`, `y = P.q` (so
`y ≠ 0`); `D = x² - 4y` and `α = (x + √D)/2`.
-/
module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Lemma 2.1 (i), (ii): every root `α` of `t² - xt + y` (in particular both roots `α, β`) satisfies
`α^n = α U_n - y U_{n-1}` for `n ≥ 1`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (i), (ii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasU_root_pow (P : LucasSequenceParams) {α : ℂ}
    (hα : α ^ 2 - P.p * α + P.q = 0) {n : ℕ} (hn : 1 ≤ n) :
    α ^ n = α * lucasU P n - P.q * lucasU P (n - 1)

/-- Lemma 2.1 (iii): `V_n = U_{n+1} - y U_{n-1}` for `n ≥ 1`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (iii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasV_eq_lucasU_succ_sub (P : LucasSequenceParams) {n : ℕ} (hn : 1 ≤ n) :
    lucasV P n = lucasU P (n + 1) - P.q * lucasU P (n - 1)

/-- Lemma 2.1 (iv): `U_{m+n} = U_m V_n - y^n U_{m-n}` for `n ≤ m`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (iv) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasU_add_eq_mul_lucasV_sub (P : LucasSequenceParams) {m n : ℕ}
    (hnm : n ≤ m) :
    lucasU P (m + n) = lucasU P m * lucasV P n - P.q ^ n * lucasU P (m - n)

/-- Lemma 2.1 (vi): `V_n² = D U_n² + 4y^n`, `D = x² - 4y`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (vi) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasV_sq_eq (P : LucasSequenceParams) (n : ℕ) :
    lucasV P n ^ 2 = (P.p ^ 2 - 4 * P.q) * lucasU P n ^ 2 + 4 * P.q ^ n

/-- Lemma 2.1 (vii): `U_r = Σ_{i=0}^{⌊(r-1)/2⌋} (-y)^i C(r-i-1, i) x^{r-2i-1}` for `r ≥ 1`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.1 (vii) (`fq-2024-earplynch07182024-lem-2.1`). -/
public theorem_wanted lucasU_eq_sum_choose (P : LucasSequenceParams) {r : ℕ} (hr : 1 ≤ r) :
    lucasU P r = ∑ i ∈ Finset.range ((r - 1) / 2 + 1),
      (-P.q) ^ i * ((r - i - 1).choose i : ℤ) * P.p ^ (r - 2 * i - 1)

/-- Lemma 2.2: for `x ≥ 1`, `|y + 1| ≤ x`, `D = x² - 4y > 0` and `α = (x + √D)/2`, for `n ≥ 2`:
`x α^{n-2} ≤ U_n`; `U_n ≤ α^{n-1}` if `y ≤ 0` and `U_n ≤ α^n/√D` if `y ≥ 0`;
`x α^{n-1} ≤ V_n ≤ α^{n+1}/x` if `y ≤ 0`; `α^n ≤ V_n ≤ α^{n+1}/√D` if `y ≥ 0`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.2 (`fq-2024-earplynch07182024-lem-2.2`). -/
public theorem_wanted lucasU_lucasV_alpha_bounds (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n : ℕ} (hn : 2 ≤ n) :
    let α : ℝ := (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2
    (P.p : ℝ) * α ^ (n - 2) ≤ lucasU P n ∧
      (P.q ≤ 0 → (lucasU P n : ℝ) ≤ α ^ (n - 1)) ∧
      (0 ≤ P.q → (lucasU P n : ℝ) ≤ α ^ n / Real.sqrt (P.p ^ 2 - 4 * P.q)) ∧
      (P.q ≤ 0 → (P.p : ℝ) * α ^ (n - 1) ≤ lucasV P n ∧ (lucasV P n : ℝ) ≤ α ^ (n + 1) / P.p) ∧
      (0 ≤ P.q → α ^ n ≤ (lucasV P n : ℝ) ∧
        (lucasV P n : ℝ) ≤ α ^ (n + 1) / Real.sqrt (P.p ^ 2 - 4 * P.q))

/-- Lemma 2.3: for `x ≥ 1` and `|y + 1| ≤ x` (`y ≠ 0`): if `y < 0` then
`U_n / U_{n-1} ≥ x - xy/(x² - y)` for `n > 2`; if `y > 0` then `U_n / U_{n-1} ≥ α` for `n ≥ 2`,
`α = (x + √(x² - 4y))/2`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.3 (`fq-2024-earplynch07182024-lem-2.3`). -/
public theorem_wanted lucasU_ratio_lower_bound (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) :
    (P.q < 0 → ∀ n : ℕ, 2 < n →
      (P.p : ℝ) - P.p * P.q / (P.p ^ 2 - P.q) ≤ (lucasU P n : ℝ) / lucasU P (n - 1)) ∧
    (0 < P.q → ∀ n : ℕ, 2 ≤ n →
      (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2 ≤ (lucasU P n : ℝ) / lucasU P (n - 1))

/-- Lemma 2.4: let `y < 0`, `|y + 1| ≤ x`, `x ≥ 1`, and let positive `n, k, p, q` satisfy
`Σ_{j=1}^k j U_j^p = U_n^q`. With `α = (x + √D)/2`:
`log_α k + p log_α x + (k - 2)p < (n - 1)q` if `k ≥ 2`, and
`q log_α x + (n - 2)q < (k - 1)p + log_α k + log_α(1 + (x² - 2y)/(x^{p-1}(x³ - x² - 2xy + y)))`
if `k ≥ 3`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.4 (`fq-2024-earplynch07182024-lem-2.4`). -/
public theorem_wanted weighted_power_sum_log_bounds_of_neg (P : LucasSequenceParams)
    (hx : 1 ≤ P.p) (hyneg : P.q < 0) (hy : |P.q + 1| ≤ P.p) {n k p q : ℕ} (hn : 0 < n)
    (hp : 0 < p) (hq : 0 < q)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let α : ℝ := (P.p + Real.sqrt (P.p ^ 2 - 4 * P.q)) / 2
    (2 ≤ k → Real.logb α k + p * Real.logb α P.p + ((k : ℝ) - 2) * p < ((n : ℝ) - 1) * q) ∧
    (3 ≤ k → q * Real.logb α P.p + ((n : ℝ) - 2) * q <
      ((k : ℝ) - 1) * p + Real.logb α k + Real.logb α (1 + ((P.p : ℝ) ^ 2 - 2 * P.q) /
        ((P.p : ℝ) ^ (p - 1) * ((P.p : ℝ) ^ 3 - P.p ^ 2 - 2 * P.p * P.q + P.q))))

/-- Lemma 2.5: let `y > 0`, `|y + 1| ≤ x`, `D = x² - 4y > 0`, and let positive `n, k, p, q`
satisfy `Σ_{j=1}^k j U_j^p = U_n^q`. With `α = (x + √D)/2`:
`log_α k + p log_α x + (k - 2)p < q(n - log_α √D)` if `k ≥ 2`, and
`q log_α x + (n - 2)q < log_α k + p(k + 1 - log_α √D) - log_α(α^p - 1)` if `k ≥ 3`. The
hypothesis `D > 0` is added (for `x = 2, y = 1`, `α = 1` and `log_α` is undefined).

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.5 (`fq-2024-earplynch07182024-lem-2.5`). -/
public theorem_wanted weighted_power_sum_log_bounds_of_pos (P : LucasSequenceParams)
    (hypos : 0 < P.q) (hy : |P.q + 1| ≤ P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n k p q : ℕ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    (2 ≤ k → Real.logb α k + p * Real.logb α P.p + ((k : ℝ) - 2) * p <
      q * (n - Real.logb α (Real.sqrt D))) ∧
    (3 ≤ k → q * Real.logb α P.p + ((n : ℝ) - 2) * q <
      Real.logb α k + p * ((k : ℝ) + 1 - Real.logb α (Real.sqrt D)) - Real.logb α (α ^ p - 1))

/-- Lemma 2.6 (Sanna): let `x ≥ 1`, `|y + 1| ≤ x`, `x, y` coprime, and `ℓ` a prime dividing
`D = x² - 4y`. For `n ≥ 1`, `ν_ℓ(U_n) = ν_ℓ(n) + ν_ℓ(U_ℓ) - 1` if `ℓ ∣ n` and `ν_ℓ(U_n) = 0`
otherwise; moreover `ν_ℓ(U_ℓ) = 1` if `ℓ ≥ 5`. CORRECTED READING: coprimality of `x, y` (Sanna's
standing hypothesis) is added; without it `x = 6, y = 3`, `ℓ = 3 ∣ D = 24` has
`ν₃(U_2) = ν₃(6) = 1 ≠ 0`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.6 (`fq-2024-earplynch07182024-lem-2.6`). -/
public theorem_wanted padicValInt_lucasU_of_dvd_discr (P : LucasSequenceParams) (hx : 1 ≤ P.p)
    (hy : |P.q + 1| ≤ P.p) (hcop : IsCoprime P.p P.q) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓD : (ℓ : ℤ) ∣ P.p ^ 2 - 4 * P.q) {n : ℕ} (hn : 1 ≤ n) :
    (ℓ ∣ n → padicValInt ℓ (lucasU P n) = padicValNat ℓ n + padicValInt ℓ (lucasU P ℓ) - 1) ∧
    (¬ ℓ ∣ n → padicValInt ℓ (lucasU P n) = 0) ∧
    (5 ≤ ℓ → padicValInt ℓ (lucasU P ℓ) = 1)

/-- Lemma 2.7: for `y = -1` (`D = x² + 4`) and positive `p, q, k, x` with `p` odd, if
`V_p(x) k² + (V_p(x) - 2)k - 1 = ±D^{p-q} V_p(x)²` (in `ℚ`, `D^{p-q}` an integer power), then
`(p, q, k, x) ∈ {(1, 1, 1, 1), (1, 1, 2, 1), (1, 1, 2, 5)}`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 2.7 (`fq-2024-earplynch07182024-lem-2.7`). -/
public theorem_wanted lucasV_quadratic_eq_pm_discr_zpow (P : LucasSequenceParams)
    (hyP : P.q = -1) {p q k : ℕ} (hx : 0 < P.p) (hp : Odd p) (hq : 0 < q) (hk : 0 < k)
    (h : let V : ℚ := lucasV P p
      let D : ℚ := (P.p : ℚ) ^ 2 + 4
      V * k ^ 2 + (V - 2) * k - 1 = D ^ ((p : ℤ) - q) * V ^ 2 ∨
        V * k ^ 2 + (V - 2) * k - 1 = -(D ^ ((p : ℤ) - q) * V ^ 2)) :
    (p = 1 ∧ q = 1 ∧ k = 1 ∧ P.p = 1) ∨ (p = 1 ∧ q = 1 ∧ k = 2 ∧ P.p = 1) ∨
      (p = 1 ∧ q = 1 ∧ k = 2 ∧ P.p = 5)

/-- Theorem 1.1, first part (= Proposition 3.1, the case `k = 2`): for `y = ±1` and positive
`n, p, q, x`, `1 + 2x^p = U_n(x, y)^q` holds exactly for
`(n, p, q, x, y) = (4, p, 1, 1, -1), (1 + 2^{p+1}, p, 1, 2, 1), (3, 2, 2, 2, 1), (3, 1, 1, 2, -1),
(5, 3, 1, 3, 1)`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Theorem 1.1 (`fq-2024-earplynch07182024-thm-1.1`) and Proposition 3.1
(`fq-2024-earplynch07182024-prop-3.1`). -/
public theorem_wanted one_add_two_mul_pow_eq_lucasU_pow_iff (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) {n p q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hq : 0 < q) :
    1 + 2 * P.p ^ p = lucasU P n ^ q ↔
      (n = 4 ∧ q = 1 ∧ P.p = 1 ∧ P.q = -1) ∨ (n = 1 + 2 ^ (p + 1) ∧ q = 1 ∧ P.p = 2 ∧ P.q = 1) ∨
        (n = 3 ∧ p = 2 ∧ q = 2 ∧ P.p = 2 ∧ P.q = 1) ∨
        (n = 3 ∧ p = 1 ∧ q = 1 ∧ P.p = 2 ∧ P.q = -1) ∨
        (n = 5 ∧ p = 3 ∧ q = 1 ∧ P.p = 3 ∧ P.q = 1)

/-- Theorem 1.1, second part: for `y = ±1` with `x ≥ 2` when `y = -1` and `x ≥ 3` when `y = 1`,
and positive `n, p, q` with `max(p, q) ≤ 11` and `k ≥ 3`, `Σ_{j=1}^k j U_j^p ≠ U_n^q`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Theorem 1.1 (`fq-2024-earplynch07182024-thm-1.1`), second part. -/
public theorem_wanted weighted_power_sum_ne_lucasU_pow (P : LucasSequenceParams)
    (hy : (P.q = -1 ∧ 2 ≤ P.p) ∨ (P.q = 1 ∧ 3 ≤ P.p)) {n k p q : ℕ} (hn : 0 < n)
    (hp : 0 < p) (hq : 0 < q) (hp11 : p ≤ 11) (hq11 : q ≤ 11) (hk : 3 ≤ k) :
    ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p ≠ lucasU P n ^ q

/-- Proposition 4.1 (existential reading of "where `|R₁| < …`, `|R₂| < …`"): let `y = ±1`,
`D = x² - 4y > 0`, `α = (x + √D)/2`, and let positive `n, p, q, x` and `k ≥ 3` satisfy
`Σ_{j=1}^k j U_j^p = U_n^q`. Then there are reals `R₁, R₂` with `|R₁| < k² α^{k(p-2)}`,
`|R₂| < α^{n(q-2)}` and
`D^{(q-p)/2}(kα^p - (k+1)) α^{p(k+1)}/(α^p - 1)² - α^{qn}
  = D^{q/2} R₂ - D^{q/2} R₁ - D^{(q-p)/2} α^p/(α^p - 1)²`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Proposition 4.1 (`fq-2024-earplynch07182024-prop-4.1`). -/
public theorem_wanted exists_remainders_weighted_power_sum (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) (hD : 0 < P.p ^ 2 - 4 * P.q) {n k p q : ℕ}
    (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    ∃ R₁ R₂ : ℝ, |R₁| < (k : ℝ) ^ 2 * α ^ ((k : ℝ) * ((p : ℝ) - 2)) ∧
      |R₂| < α ^ ((n : ℝ) * ((q : ℝ) - 2)) ∧
      D ^ (((q : ℝ) - p) / 2) * (k * α ^ p - (k + 1)) / (α ^ p - 1) ^ 2 * α ^ (p * (k + 1)) -
          α ^ (q * n) =
        D ^ ((q : ℝ) / 2) * R₂ - D ^ ((q : ℝ) / 2) * R₁ -
          D ^ (((q : ℝ) - p) / 2) * α ^ p / (α ^ p - 1) ^ 2

/-- Lemma 4.4: for `y = ±1`, positive `n, p, q, x` and `k ≥ 3` with `Σ_{j=1}^k j U_j^p = U_n^q`,
`x ≤ (k + 1)²/4 + 1`. The standing assumption `k ≥ 3` of Section 4 is kept explicit (for `k = 1`,
`(n, p, q, x) = (1, 1, 1, 5)` with `y = -1` is a solution and `5 > 2`).

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.4 (`fq-2024-earplynch07182024-lem-4.4`). -/
public theorem_wanted le_of_weighted_power_sum_eq (P : LucasSequenceParams)
    (hy : P.q = 1 ∨ P.q = -1) (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    (P.p : ℚ) ≤ ((k : ℚ) + 1) ^ 2 / 4 + 1

/-- Lemma 4.2: for `y = -1` (`D = x² + 4`), positive `n, p, q, x` and `k ≥ 3` with
`Σ_{j=1}^k j U_j^p = U_n^q`, the remainder `R₂ = U_n^q - α^{nq}/D^{q/2}` of Proposition 4.1
(its definition in that proof) satisfies `D^{q/2} |R₂| < k (D + 1/x)^{q+1} α^{kp - 2k/q + 1}`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.2 (`fq-2024-earplynch07182024-lem-4.2`). -/
public theorem_wanted remainder_bound_of_neg (P : LucasSequenceParams) (hyP : P.q = -1)
    (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    D ^ ((q : ℝ) / 2) * |(lucasU P n : ℝ) ^ q - α ^ (n * q) / D ^ ((q : ℝ) / 2)| <
      k * (D + 1 / P.p) ^ (q + 1) * α ^ ((k : ℝ) * p - 2 * k / q + 1)

/-- Lemma 4.3: for `y = 1` with `D = x² - 4 > 0`, positive `n, p, q` and `k ≥ 3` with
`Σ_{j=1}^k j U_j^p = U_n^q`, the remainder `R₂ = U_n^q - α^{nq}/D^{q/2}` of Proposition 4.1
satisfies `D^{q/2} |R₂| < k (V₂ + 1/x)^{q+1} α^{kp - 2k/q + 1/2}`, where `V₂ = x² - 2`.

Source: Benjamin Earp-Lynch, Simon Earp-Lynch, Omar Kihel and Puntani Pongsumpun, *Extension of the
Equation ∑ j F_j^p = F_n^q to a Family of Lucas Sequences*, The Fibonacci Quarterly 62 (2024),
no. 3, Lemma 4.3 (`fq-2024-earplynch07182024-lem-4.3`). -/
public theorem_wanted remainder_bound_of_pos (P : LucasSequenceParams) (hyP : P.q = 1)
    (hD : 0 < P.p ^ 2 - 4 * P.q) (hx : 0 < P.p) {n k p q : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hq : 0 < q) (hk : 3 ≤ k)
    (hsol : ∑ j ∈ Finset.Icc 1 k, (j : ℤ) * lucasU P j ^ p = lucasU P n ^ q) :
    let D : ℝ := P.p ^ 2 - 4 * P.q
    let α : ℝ := (P.p + Real.sqrt D) / 2
    D ^ ((q : ℝ) / 2) * |(lucasU P n : ℝ) ^ q - α ^ (n * q) / D ^ ((q : ℝ) / 2)| <
      k * ((lucasV P 2 : ℝ) + 1 / P.p) ^ (q + 1) * α ^ ((k : ℝ) * p - 2 * k / q + 1 / 2)

end

end MetaMathlibExt
