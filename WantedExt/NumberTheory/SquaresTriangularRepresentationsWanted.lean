/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Congruences for representations as sums of squares and triangular numbers

Statements from Alegri and Christopher, *On Formulas, Recurrences, and
Congruences for Representations of Integers as Sums of Squares and Triangular
Numbers*, INTEGERS 26 (2026), Article A93. With `θ(q) = ∑_{m ∈ ℤ} q^{m²}` and
`ψ(q) = ∑_{m ≥ 0} q^{m(m+1)/2}`, `r_k(n)` and `t_k(n)` are the coefficients of
`q^n` in `θ(q)^k` and `ψ(q)^k`: for `k ≥ 1` the numbers of representations of `n`
as an ordered sum of `k` squares of integers and of `k` triangular numbers. The
source treats them as polynomials in `k` (`n! r_k(n), n! t_k(n) ∈ ℤ[k]`) and
evaluates at arbitrary integers `k` (e.g. `k + r p` with `r ∈ ℤ`); here `k ∈ ℤ`
through the integer powers of the units `θ` and `ψ` of `ℤ⟦q⟧`, which agree with
those polynomial values.
-/

namespace MetaMathlibExt

@[expose] public section

/-- `θ(q) = ∑_{m ∈ ℤ} q^{m²}`: the coefficient of `q^n` is the number of integers
`m` with `m² = n`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def squareThetaSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (((Finset.Icc (-(n : ℤ)) n).filter fun m : ℤ => m ^ 2 = (n : ℤ)).card : ℤ)

/-- `ψ(q) = ∑_{m ≥ 0} q^{m(m+1)/2}`: the coefficient of `q^n` is the number of `m ≥ 0`
with `m(m+1)/2 = n`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def triangularThetaSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (((Finset.range (n + 1)).filter fun m => m * (m + 1) / 2 = n).card : ℤ)

/-- The first coefficients of `θ`: `1, 2, 0, 0, 2`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem coeff_squareThetaSeries_small :
    PowerSeries.coeff 0 squareThetaSeries = 1 ∧ PowerSeries.coeff 1 squareThetaSeries = 2 ∧
      PowerSeries.coeff 2 squareThetaSeries = 0 ∧ PowerSeries.coeff 4 squareThetaSeries = 2 := by
  simp only [squareThetaSeries, PowerSeries.coeff_mk]
  decide

/-- The first coefficients of `ψ`: `1, 1, 0, 1`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem coeff_triangularThetaSeries_small :
    PowerSeries.coeff 0 triangularThetaSeries = 1 ∧ PowerSeries.coeff 1 triangularThetaSeries = 1 ∧
      PowerSeries.coeff 2 triangularThetaSeries = 0 ∧
        PowerSeries.coeff 3 triangularThetaSeries = 1 := by
  simp only [triangularThetaSeries, PowerSeries.coeff_mk]
  decide

/-- `θ` is a unit of `ℤ⟦q⟧` (constant coefficient `1`).

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem isUnit_squareThetaSeries : IsUnit squareThetaSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_squareThetaSeries_small.1]
  exact isUnit_one

/-- `ψ` is a unit of `ℤ⟦q⟧` (constant coefficient `1`).

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem isUnit_triangularThetaSeries : IsUnit triangularThetaSeries := by
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_triangularThetaSeries_small.1]
  exact isUnit_one

/-- `r_k(n)`: the coefficient of `q^n` in `θ(q)^k`, for `k ∈ ℤ`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def sumOfSquaresRepCount (k : ℤ) (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((isUnit_squareThetaSeries.unit ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)

/-- `t_k(n)`: the coefficient of `q^n` in `ψ(q)^k`, for `k ∈ ℤ`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public noncomputable def sumOfTriangularRepCount (k : ℤ) (n : ℕ) : ℤ :=
  PowerSeries.coeff n ((isUnit_triangularThetaSeries.unit ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)

/-- `r_1(n)` is the coefficient of `θ`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem sumOfSquaresRepCount_one (n : ℕ) :
    sumOfSquaresRepCount 1 n = PowerSeries.coeff n squareThetaSeries := by
  simp [sumOfSquaresRepCount]

/-- `t_1(n)` is the coefficient of `ψ`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Section 1. -/
public theorem sumOfTriangularRepCount_one (n : ℕ) :
    sumOfTriangularRepCount 1 n = PowerSeries.coeff n triangularThetaSeries := by
  simp [sumOfTriangularRepCount]

/-- For positive `n, k` and a prime `p ≥ n + 1`: if `p ∣ r_k(n)` then `p ∣ r_{k+rp}(n)`
for every `r ∈ ℤ`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 3 (`integers-2026-A93-thm-3`). -/
public theorem_wanted sumOfSquaresRepCount_add_mul_prime {n k p : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hp : p.Prime) (hpn : n + 1 ≤ p) (h : (p : ℤ) ∣ sumOfSquaresRepCount k n) (r : ℤ) :
    (p : ℤ) ∣ sumOfSquaresRepCount (k + r * p) n

/-- For positive `n, k` and a prime `p ≥ n + 1`: if `p ∣ t_k(n)` then `p ∣ t_{k+rp}(n)`
for every `r ∈ ℤ`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 4 (`integers-2026-A93-thm-4`). -/
public theorem_wanted sumOfTriangularRepCount_add_mul_prime {n k p : ℕ} (hn : 1 ≤ n)
    (hk : 1 ≤ k) (hp : p.Prime) (hpn : n + 1 ≤ p)
    (h : (p : ℤ) ∣ sumOfTriangularRepCount k n) (r : ℤ) :
    (p : ℤ) ∣ sumOfTriangularRepCount (k + r * p) n

/-- For `n ≥ 1`, an odd prime `p` with `p - 1 ≥ n + 1`, and every integer `s ≥ p`:
`∑_{i=0}^{p-1} r_{s-i}(n) ≡ 0 (mod p)`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 5 (`integers-2026-A93-thm-5`). -/
public theorem_wanted sum_sumOfSquaresRepCount_window {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) {s : ℤ} (hs : (p : ℤ) ≤ s) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, sumOfSquaresRepCount (s - i) n

/-- For `n ≥ 1`, an odd prime `p` with `p - 1 ≥ n + 1`, and every integer `s ≥ p`:
`∑_{i=0}^{p-1} t_{s-i}(n) ≡ 0 (mod p)`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 6 (`integers-2026-A93-thm-6`). -/
public theorem_wanted sum_sumOfTriangularRepCount_window {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) {s : ℤ} (hs : (p : ℤ) ≤ s) :
    (p : ℤ) ∣ ∑ i ∈ Finset.range p, sumOfTriangularRepCount (s - i) n

/-- Representability criterion: for `n ≥ 1` and an odd prime `p` with `p - 1 ≥ n + 1`,
if `r_{s-(p-1)}(n) + ⋯ + r_{s-1}(n) ≢ 0 (mod p)` then `r_s(n) ≠ 0`, and the same for
`t_s(n)`. The source places no condition on `s`; it is stated for every `s ∈ ℤ`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 7 (`integers-2026-A93-thm-7`). -/
public theorem_wanted repCount_ne_zero_of_window {n p : ℕ} (hn : 1 ≤ n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) (s : ℤ) :
    (¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfSquaresRepCount (s - i) n →
      sumOfSquaresRepCount s n ≠ 0) ∧
    (¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfTriangularRepCount (s - i) n →
      sumOfTriangularRepCount s n ≠ 0)

/-- Representability criterion for triangular numbers: for `n ≥ 1` and an odd prime
`p` with `p - 1 ≥ n + 1`, if `t_{s-(p-1)}(n) + ⋯ + t_{s-1}(n) ≢ 0 (mod p)` then
`t_s(n) ≠ 0` (every `s ∈ ℤ`).

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 8 (`integers-2026-A93-thm-8`). -/
public theorem_wanted sumOfTriangularRepCount_ne_zero_of_window {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : n + 1 ≤ p - 1) (s : ℤ)
    (h : ¬ (p : ℤ) ∣ ∑ i ∈ Finset.Icc 1 (p - 1), sumOfTriangularRepCount (s - i) n) :
    sumOfTriangularRepCount s n ≠ 0

/-- For an odd prime `p` and a prime `q` with `p/2 < q < p`: `r_q(p) ≡ 0 (mod q)` and
`t_q(p) ≡ 0 (mod q)`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 11 (`integers-2026-A93-thm-11`). -/
public theorem_wanted prime_dvd_repCount_of_half_lt {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : q.Prime) (hpq : p < 2 * q) (hqp : q < p) :
    (q : ℤ) ∣ sumOfSquaresRepCount q p ∧ (q : ℤ) ∣ sumOfTriangularRepCount q p

/-- The coefficient `b_n` of `q^n` in `log ψ(q)`, from the expansion
`log ψ(q) = ∑_m log(1 - q^{2m}) - ∑_m log(1 - q^{2m-1})` in the proof of Theorem 2:
`b_n = ∑_{d ∣ n, n/d odd} 1/d - ∑_{d ∣ n, n/d even} 1/d`. The printed formula of Theorem 2 has the
parity condition on `d` instead of `n/d`, which gives `b_2 = 1/2` instead of `-1/2`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 2 and its proof. -/
public def triangularLogCoeff (n : ℕ) : ℚ :=
  ∑ d ∈ n.divisors, if Odd (n / d) then (1 : ℚ) / d else -((1 : ℚ) / d)

/-- `b_1 = 1`, `b_2 = -1/2`, `b_3 = 4/3`, matching `log(1 + q + q³ + ⋯) = q - q²/2 + 4q³/3 + ⋯`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 2 and its proof. -/
public theorem triangularLogCoeff_small :
    triangularLogCoeff 1 = 1 ∧ triangularLogCoeff 2 = -1 / 2 ∧ triangularLogCoeff 3 = 4 / 3 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [triangularLogCoeff]
    decide +kernel

/-- Composition-sum formula: `t_k(n) = ∑_{l=1}^n (k^l / l!) ∑_{(w_1, …, w_l) ∈ C(n)} b_{w_1} ⋯ b_{w_l}`,
with `b_n = triangularLogCoeff n` (the corrected coefficient; the printed `b_n` is false:
`t_1(2) = 0` but the printed formula gives `1`). The sum runs over all compositions of `n`,
grouped by length `l`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 2 (`integers-2026-A93-thm-2`). -/
public theorem_wanted sumOfTriangularRepCount_eq_sum_compositions (k : ℤ) (n : ℕ) :
    (sumOfTriangularRepCount k n : ℚ) =
      ∑ c : Composition n, (k : ℚ) ^ c.length / (c.length.factorial : ℚ) *
        (c.blocks.map triangularLogCoeff).prod

/-- Recurrence `t_k(n + 1) = ∑_{j=0}^n k (j + 1) b_{j+1} / (n + 1) · t_k(n - j)` for `n ≥ 0`, with
`b_n = triangularLogCoeff n`.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Corollary 1, second recurrence (`integers-2026-A93-cor-1`). -/
public theorem_wanted sumOfTriangularRepCount_succ (k : ℤ) (n : ℕ) :
    (sumOfTriangularRepCount k (n + 1) : ℚ) =
      ∑ j ∈ Finset.range (n + 1),
        (k : ℚ) * (j + 1) * triangularLogCoeff (j + 1) / (n + 1) * sumOfTriangularRepCount k (n - j)

/-- `n! r_z(n)` is an integer polynomial `r_{n,0} + r_{n,1} z + ⋯ + r_{n,n} z^n`, and every nonzero
integer `k` with `r_k(n) = 0` divides `r_{n,1}` and satisfies `|k| < 2 R_n`,
`R_n = max_{0 ≤ i ≤ n-1} |r_{n,i}|^{1/(n-i)}` (written as `|k| < 2 |r_{n,i}|^{1/(n-i)}` for some
`i < n`).

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 9 (`integers-2026-A93-thm-9`). -/
public theorem_wanted sumOfSquaresRepCount_integer_root (n : ℕ) :
    ∃ P : Polynomial ℤ, (∀ z : ℤ, P.eval z = n.factorial * sumOfSquaresRepCount z n) ∧
      ∀ k : ℤ, k ≠ 0 → sumOfSquaresRepCount k n = 0 →
        k ∣ P.coeff 1 ∧
          ∃ i < n, (|k| : ℝ) < 2 * (|P.coeff i| : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - i))

/-- `n! t_z(n)` is an integer polynomial `t_{n,0} + t_{n,1} z + ⋯ + t_{n,n} z^n`, and every nonzero
integer `k` with `t_k(n) = 0` divides `t_{n,1}` and satisfies `|k| < 2 T_n`,
`T_n = max_{0 ≤ i ≤ n-1} |t_{n,i}|^{1/(n-i)}` (written as `|k| < 2 |t_{n,i}|^{1/(n-i)}` for some
`i < n`).

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 10 (`integers-2026-A93-thm-10`). -/
public theorem_wanted sumOfTriangularRepCount_integer_root (n : ℕ) :
    ∃ P : Polynomial ℤ, (∀ z : ℤ, P.eval z = n.factorial * sumOfTriangularRepCount z n) ∧
      ∀ k : ℤ, k ≠ 0 → sumOfTriangularRepCount k n = 0 →
        k ∣ P.coeff 1 ∧
          ∃ i < n, (|k| : ℝ) < 2 * (|P.coeff i| : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - i))

end

end MetaMathlibExt
