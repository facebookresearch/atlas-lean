/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs

namespace MetaMathlibExt

@[expose] public section

open Filter Asymptotics Real

/-- The base-`q` digit sum `s_q(n)` (sum of the digits of `n` in base `q`) as an arithmetic
function, so that its Dirichlet powers `digitSumArith q ^ k` are the `k`-fold Dirichlet
convolutions `s_q^{(k)} = s_q * s_q^{(k-1)}` of the paper.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Section 1 (definition of `s_q` and of `s_q^{(k)}`). -/
def digitSumArith (q : ℕ) : ArithmeticFunction ℕ :=
  ⟨fun n => (Nat.digits q n).sum, by simp⟩

/-- `digitSumArith q n` is the base-`q` digit sum of `n`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Section 1. -/
theorem digitSumArith_apply (q n : ℕ) : digitSumArith q n = (Nat.digits q n).sum := rfl

/-- The second Dirichlet convolution `s_q^{(2)}(n) = ∑_{d ∣ n} s_q(d) s_q(n/d)`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Section 1 (definition of `s_q^{(2)}`). -/
theorem digitSumArith_sq_apply (q n : ℕ) :
    (digitSumArith q ^ 2) n =
      ∑ x ∈ n.divisorsAntidiagonal, (Nat.digits q x.1).sum * (Nat.digits q x.2).sum := by
  rw [sq, ArithmeticFunction.mul_apply]
  rfl

/-- Delange's function `g(x) = ∫_0^x (⌊q t⌋ - q ⌊t⌋ - (q - 1)/2) dt`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `g`). -/
noncomputable def trollopeDelangeIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, ((⌊(q : ℝ) * t⌋ : ℝ) - q * ⌊t⌋ - ((q : ℝ) - 1) / 2)

/-- `g(0) = 0`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1. -/
theorem trollopeDelangeIntegral_zero (q : ℕ) : trollopeDelangeIntegral q 0 = 0 :=
  intervalIntegral.integral_same

/-- Delange's series `h(x) = ∑_{r ≥ 0} g(q^r x) / q^r`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `h`). -/
noncomputable def trollopeDelangeSeries (q : ℕ) (x : ℝ) : ℝ :=
  ∑' r : ℕ, trollopeDelangeIntegral q ((q : ℝ) ^ r * x) / (q : ℝ) ^ r

/-- `h(0) = 0`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1. -/
theorem trollopeDelangeSeries_zero (q : ℕ) : trollopeDelangeSeries q 0 = 0 := by
  simp [trollopeDelangeSeries, trollopeDelangeIntegral_zero]

/-- The Trollope-Delange fluctuation
`F(x) = (q - 1)/2 · (1 + ⌊x⌋ - x) + q^{1 + ⌊x⌋ - x} h(q^{x - ⌊x⌋ - 1})`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (definition of `F`). -/
noncomputable def trollopeDelangeFluctuation (q : ℕ) (x : ℝ) : ℝ :=
  ((q : ℝ) - 1) / 2 * (1 + ⌊x⌋ - x) +
    (q : ℝ) ^ (1 + ⌊x⌋ - x) * trollopeDelangeSeries q ((q : ℝ) ^ (x - ⌊x⌋ - 1))

/-- `F` is `1`-periodic.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (`F` is `1`-periodic). -/
theorem trollopeDelangeFluctuation_add_one (q : ℕ) (x : ℝ) :
    trollopeDelangeFluctuation q (x + 1) = trollopeDelangeFluctuation q x := by
  have h1 : (1 + ((⌊x + 1⌋ : ℤ) : ℝ) - (x + 1)) = 1 + ⌊x⌋ - x := by
    rw [Int.floor_add_one]; push_cast; ring
  have h2 : (x + 1 - ((⌊x + 1⌋ : ℤ) : ℝ) - 1) = x - ⌊x⌋ - 1 := by
    rw [Int.floor_add_one]; push_cast; ring
  simp only [trollopeDelangeFluctuation, h1, h2]

/-- The remainder `J(x) = (1 + ⌊x⌋ - x) s_q(⌊x⌋) - h(x)` of the Trollope-Delange formula.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `J`). -/
noncomputable def digitSumRemainder (q : ℕ) (x : ℝ) : ℝ :=
  (1 + ⌊x⌋₊ - x) * ((Nat.digits q ⌊x⌋₊).sum : ℝ) - trollopeDelangeSeries q x

/-- `J(0) = 0`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumRemainder_zero (q : ℕ) : digitSumRemainder q 0 = 0 := by
  simp [digitSumRemainder, trollopeDelangeSeries_zero]

/-- `G(x) = ∫_1^x F(log u / log q) du / u`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `G`). -/
noncomputable def digitSumFluctuationIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, trollopeDelangeFluctuation q (log u / log q) / u

/-- `G(1) = 0`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumFluctuationIntegral_one (q : ℕ) : digitSumFluctuationIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- `H(x) = ∫_1^x ∫_1^u F(log v / log q) dv / v du / u`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `H`). -/
noncomputable def digitSumFluctuationDoubleIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, (∫ v in (1 : ℝ)..u, trollopeDelangeFluctuation q (log v / log q) / v) / u

/-- `H(1) = 0`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumFluctuationDoubleIntegral_one (q : ℕ) :
    digitSumFluctuationDoubleIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- `K(x) = ∫_1^x J(u) du / u²`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `K`). -/
noncomputable def digitSumRemainderIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, digitSumRemainder q u / u ^ 2

/-- `K(1) = 0`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumRemainderIntegral_one (q : ℕ) : digitSumRemainderIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- `L(x) = ∫_1^x ∫_1^u J(v) dv / v² du / u`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (definition of `L`). -/
noncomputable def digitSumRemainderDoubleIntegral (q : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (1 : ℝ)..x, (∫ v in (1 : ℝ)..u, digitSumRemainder q v / v ^ 2) / u

/-- `L(1) = 0`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1. -/
theorem digitSumRemainderDoubleIntegral_one (q : ℕ) :
    digitSumRemainderDoubleIntegral q 1 = 0 :=
  intervalIntegral.integral_same

/-- The leading coefficients of Theorem 3: `a(2) = (q - 1)² / (24 log² q)` and, for `k ≥ 3`,
`a(k) = a(k - 1) (q - 1)/(2 log q) ∑_{j=0}^{2k-3} C(2k-3, j) (-1)^j / (j + 2)`.
The values at `k = 0, 1` are junk (`0`); the theorem uses `k ≥ 2` only.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3 (definition of `a(k)`). -/
noncomputable def digitConvolutionCoeff (q : ℕ) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | 2 => ((q : ℝ) - 1) ^ 2 / (24 * log q ^ 2)
  | k + 3 =>
    digitConvolutionCoeff q (k + 2) * (((q : ℝ) - 1) / (2 * log q)) *
      ∑ j ∈ Finset.range (2 * (k + 3) - 3 + 1),
        ((2 * (k + 3) - 3).choose j : ℝ) * (-1) ^ j / ((j : ℝ) + 2)

/-- `a(2) = (q - 1)² / (24 log² q)`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3. -/
theorem digitConvolutionCoeff_two (q : ℕ) :
    digitConvolutionCoeff q 2 = ((q : ℝ) - 1) ^ 2 / (24 * log q ^ 2) := rfl

/-- The recurrence of `a(k)` for `k ≥ 3`, written for `k + 1` with `k ≥ 2`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3. -/
theorem digitConvolutionCoeff_succ (q : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    digitConvolutionCoeff q (k + 1) =
      digitConvolutionCoeff q k * (((q : ℝ) - 1) / (2 * log q)) *
        ∑ j ∈ Finset.range (2 * (k + 1) - 3 + 1),
          ((2 * (k + 1) - 3).choose j : ℝ) * (-1) ^ j / ((j : ℝ) + 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  rfl

/-- The Trollope-Delange formula in base `q`, for real `x ≥ 1`:
`∑_{n ≤ x} s_q(n) = (q - 1)/(2 log q) · x log x + x F(log x / log q) - h(x)
  + (1 + ⌊x⌋ - x) s_q(⌊x⌋)`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (`integers-2026-A43-thm-1`), equation (1). -/
public theorem_wanted digitSum_partialSum_trollopeDelange (q : ℕ) (hq : 2 ≤ q) (x : ℝ)
    (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) =
      ((q : ℝ) - 1) / (2 * log q) * x * log x +
        x * trollopeDelangeFluctuation q (log x / log q) - trollopeDelangeSeries q x +
          (1 + ⌊x⌋₊ - x) * ((Nat.digits q ⌊x⌋₊).sum : ℝ)

/-- `g(x) = O(1)` as `x → ∞`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 2 (`integers-2026-A43-lem-2`). -/
public theorem_wanted trollopeDelangeIntegral_isBigO_one (q : ℕ) (hq : 2 ≤ q) :
    trollopeDelangeIntegral q =O[atTop] (fun _ => (1 : ℝ))

/-- The reciprocal digit sums, for real `x ≥ 1`:
`∑_{n ≤ x} s_q(n)/n = (q-1) log² x/(4 log q) + (q-1) log x/(2 log q) + F(log x/log q)
  + G(x) + J(x)/x + K(x)` and
`∑_{n ≤ x} s_q(n) log n/n = (q-1) log³ x/(6 log q) + (q-1) log² x/(4 log q)
  + log x · F(log x/log q) + (log x - 1) G(x) - H(x) + J(x) log x/x + (log x - 1) K(x) - L(x)`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 1 (`integers-2026-A43-lem-1`), equations (4) and (5). -/
public theorem_wanted digitSum_reciprocal_sums_eq (q : ℕ) (hq : 2 ≤ q) (x : ℝ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) / n =
        ((q : ℝ) - 1) * log x ^ 2 / (4 * log q) + ((q : ℝ) - 1) * log x / (2 * log q) +
          trollopeDelangeFluctuation q (log x / log q) + digitSumFluctuationIntegral q x +
          digitSumRemainder q x / x + digitSumRemainderIntegral q x ∧
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) * log n / n =
        ((q : ℝ) - 1) * log x ^ 3 / (6 * log q) + ((q : ℝ) - 1) * log x ^ 2 / (4 * log q) +
          log x * trollopeDelangeFluctuation q (log x / log q) +
          (log x - 1) * digitSumFluctuationIntegral q x -
          digitSumFluctuationDoubleIntegral q x + digitSumRemainder q x * log x / x +
          (log x - 1) * digitSumRemainderIntegral q x - digitSumRemainderDoubleIntegral q x

/-- The size bounds `h(x) = O(1)`, `F` bounded, `J(x) = O(log x)`, `G(x) = O(log x)`,
`H(x) = O(log² x)`, `K(x) = O(1)` and `L(x) = O(log x)` as `x → ∞`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 3 (`integers-2026-A43-lem-3`). -/
public theorem_wanted digitSum_auxiliary_isBigO (q : ℕ) (hq : 2 ≤ q) :
    trollopeDelangeSeries q =O[atTop] (fun _ => (1 : ℝ)) ∧
      (∃ C : ℝ, ∀ x : ℝ, |trollopeDelangeFluctuation q x| ≤ C) ∧
      digitSumRemainder q =O[atTop] log ∧
      digitSumFluctuationIntegral q =O[atTop] log ∧
      digitSumFluctuationDoubleIntegral q =O[atTop] (fun x => log x ^ 2) ∧
      digitSumRemainderIntegral q =O[atTop] (fun _ => (1 : ℝ)) ∧
      digitSumRemainderDoubleIntegral q =O[atTop] log

/-- For real `x > 0` and `y`,
`∑_{n ≤ y} s_q(n)/n · F(log(x/n)/log q) ≤ F_M ∑_{n ≤ y} s_q(n)/n`, where
`F_M = sup_t |F(t)|`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 4 (`integers-2026-A43-lem-4`). -/
public theorem_wanted digitSum_reciprocal_fluctuation_sum_le (q : ℕ) (hq : 2 ≤ q) (x y : ℝ)
    (hx : 0 < x) :
    ∑ n ∈ Finset.Icc 1 ⌊y⌋₊,
        ((Nat.digits q n).sum : ℝ) / n * trollopeDelangeFluctuation q (log (x / n) / log q) ≤
      (⨆ t : ℝ, |trollopeDelangeFluctuation q t|) *
        ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ((Nat.digits q n).sum : ℝ) / n

/-- For every positive integer `j`,
`∑_{n ≤ x} s_q(n)/n · log^j n = (q - 1) log^{j+2} x / (2 (j + 2) log q) + O(log^{j+1} x)`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 5 (`integers-2026-A43-lem-5`). -/
public theorem_wanted digitSum_reciprocal_log_pow_sum_isBigO (q : ℕ) (hq : 2 ≤ q) (j : ℕ)
    (hj : 1 ≤ j) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) / n * log n ^ j -
        ((q : ℝ) - 1) * log x ^ (j + 2) / (2 * (j + 2) * log q)) =O[atTop]
      (fun x => log x ^ (j + 1))

/-- `∑_{n ≤ x} s_q^{(2)}(n) = (q - 1)² x log³ x / (24 log² q) + O(x log² x)` as `x → ∞`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 2 (`integers-2026-A43-thm-2`). -/
public theorem_wanted digitSumArith_sq_partialSum_isBigO (q : ℕ) (hq : 2 ≤ q) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ 2) n : ℝ) -
        ((q : ℝ) - 1) ^ 2 * x * log x ^ 3 / (24 * log q ^ 2)) =O[atTop]
      (fun x => x * log x ^ 2)

/-- For every integer `k ≥ 2`,
`∑_{n ≤ x} s_q^{(k)}(n) = a(k) x log^{2k-1} x + O(x log^{2k-2} x)` as `x → ∞`.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 3 (`integers-2026-A43-thm-3`), equation (2). -/
public theorem_wanted digitSumArith_pow_partialSum_isBigO (q : ℕ) (hq : 2 ≤ q) (k : ℕ)
    (hk : 2 ≤ k) :
    (fun x : ℝ => ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((digitSumArith q ^ k) n : ℝ) -
        digitConvolutionCoeff q k * x * log x ^ (2 * k - 1)) =O[atTop]
      (fun x => x * log x ^ (2 * k - 2))

end

end MetaMathlibExt
