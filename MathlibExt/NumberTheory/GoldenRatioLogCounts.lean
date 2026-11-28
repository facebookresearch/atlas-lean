/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Set.Card
public import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula

/-!
# Counting integers by their golden-ratio logarithm

For each integer `m ≥ 1`, the number of positive integers `n` with
`⌊log_φ n⌋ = m` is the `m`-th term of the alternating-sign Fibonacci sequence.
The count is the difference of the ceilings of two successive powers of the golden ratio.
The conjugate term in the Lucas-number Binet formula determines each ceiling.

## References

* Aleksandar Petojević, Marjana Gorjanac Ranitović, Dragan Rastovac, and Milinko Mandić,
  *The Golden Ratio, Factorials, and the Lambert W Function*, Journal of Integer Sequences
  27 (2024), Article 24.5.7, pp. 1–11, Section 2.2, Lemma 3 and Example 5. The authors
  credit J. Shallit for the counting proof and G. C. Greubel for the Lucas-number formula
  in Equation (5), recorded in OEIS A181716.
* The Lucas-number Binet formula is obtained from `lucas_binet_formulas_of_field` in
  `MathlibExt.NumberTheory.Recurrences.LucasBinetFormula` and `lucasV_fibonacciLucasParams` in
  `MathlibExt.NumberTheory.LucasSequence`.
-/

namespace MetaMathlibExt

open Real
open scoped goldenRatio

@[expose] public section

/-- **Alternating-sign Fibonacci sequence.** The alternating-sign Fibonacci sequence
(OEIS A181716) is the integer sequence $(d_m)_{m \ge 0}$ defined by $d_0 = 0$, $d_1 = 1$ and
$d_{m+2} = d_{m+1} + d_m + (-1)^{m+2}$ for every natural number $m$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2 (definition before Lemma 3). -/
public def alternatingSignFibonacci : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | m + 2 => alternatingSignFibonacci (m + 1) + alternatingSignFibonacci m + (-1) ^ (m + 2)

/-- **Recurrence of the alternating-sign Fibonacci sequence.** For every natural number $m$,
the alternating-sign Fibonacci sequence $d$ satisfies $d_{m+2} = d_{m+1} + d_m + (-1)^{m+2}$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Section 2.2. -/
public theorem alternatingSignFibonacci_add_two (m : ℕ) :
    alternatingSignFibonacci (m + 2) =
      alternatingSignFibonacci (m + 1) + alternatingSignFibonacci m + (-1) ^ (m + 2) :=
  rfl

/-- **First values of the alternating-sign Fibonacci sequence.** The alternating-sign Fibonacci
sequence $d$ satisfies $d_0 = 0$, $d_1 = 1$, $d_2 = 2$, $d_3 = 2$ and $d_4 = 5$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Example 5. -/
public theorem alternatingSignFibonacci_small_values :
    alternatingSignFibonacci 0 = 0 ∧ alternatingSignFibonacci 1 = 1 ∧
      alternatingSignFibonacci 2 = 2 ∧ alternatingSignFibonacci 3 = 2 ∧
      alternatingSignFibonacci 4 = 5 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> norm_num [alternatingSignFibonacci]

end

-- Use real casts so that the ceiling correction is linear in `(-1)^m`.
private theorem cast_ceil_goldenRatio_pow {m : ℕ} (hm : 1 ≤ m) :
    (⌈φ ^ m⌉ : ℝ) = φ ^ m + ψ ^ m + (1 - (-1 : ℝ) ^ m) / 2 := by
  have hsum : φ + ψ = (fibonacciLucasParams.p : ℝ) := by
    rw [show fibonacciLucasParams.p = 1 by decide, Int.cast_one]
    exact goldenRatio_add_goldenConj
  have hprod : φ * ψ = (fibonacciLucasParams.q : ℝ) := by
    rw [show fibonacciLucasParams.q = -1 by decide, Int.cast_neg, Int.cast_one]
    exact goldenRatio_mul_goldenConj
  have hne : φ ≠ ψ := ne_of_gt (goldenConj_neg.trans goldenRatio_pos)
  have hLucas := ((lucas_binet_formulas_of_field fibonacciLucasParams φ ψ hsum hprod).1 hne m).2
  rw [lucasV_fibonacciLucasParams, Int.cast_natCast] at hLucas
  have hbound : |ψ ^ m| < 1 := by
    rw [abs_pow, abs_of_neg goldenConj_neg]
    exact pow_lt_one₀ (neg_nonneg.mpr goldenConj_neg.le)
      (by linarith only [neg_one_lt_goldenConj]) (by omega)
  obtain ⟨hl, hu⟩ := abs_lt.mp hbound
  obtain he | ho := Nat.even_or_odd m
  · have hc : ⌈φ ^ m⌉ = (lucasNumber m : ℤ) := by
      rw [Int.ceil_eq_iff, Int.cast_natCast]
      have hpos := he.pow_nonneg ψ
      constructor <;> linarith only [hLucas, hu, hpos]
    rw [hc, Int.cast_natCast, hLucas, he.neg_one_pow]
    ring
  · have hc : ⌈φ ^ m⌉ = (lucasNumber m : ℤ) + 1 := by
      rw [Int.ceil_eq_iff, Int.cast_add, Int.cast_natCast, Int.cast_one]
      have hneg := ho.pow_neg goldenConj_neg
      constructor <;> linarith only [hLucas, hl, hneg]
    rw [hc, Int.cast_add, Int.cast_natCast, Int.cast_one, hLucas, ho.neg_one_pow]
    ring

private theorem goldenPowers_add_two (k : ℕ) :
    φ ^ (k + 2) + ψ ^ (k + 2) = (φ ^ (k + 1) + ψ ^ (k + 1)) + (φ ^ k + ψ ^ k) := by
  rw [pow_add φ k 2, pow_add ψ k 2, goldenRatio_sq, goldenConj_sq, pow_succ φ k, pow_succ ψ k]
  ring

private theorem cast_alternatingSignFibonacci_succ (k : ℕ) :
    (alternatingSignFibonacci (k + 1) : ℝ) = φ ^ k + ψ ^ k + (-1 : ℝ) ^ (k + 1) := by
  induction k using Nat.twoStepInduction with
  | zero => norm_num [alternatingSignFibonacci]
  | one => norm_num [alternatingSignFibonacci, goldenRatio_add_goldenConj]
  | more k ih₀ ih₁ =>
    rw [show k + 2 + 1 = (k + 1) + 2 by omega, alternatingSignFibonacci_add_two]
    push_cast
    rw [ih₀, ih₁, goldenPowers_add_two, pow_succ (-1 : ℝ) (k + 1)]
    ring

private theorem floor_logb_goldenRatio_set (m : ℕ) :
    {n : ℕ | 1 ≤ n ∧ ⌊Real.logb φ n⌋₊ = m} =
      (↑(Finset.Ico ⌈φ ^ m⌉₊ ⌈φ ^ (m + 1)⌉₊) : Set ℕ) := by
  ext n
  rw [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_Ico, Nat.ceil_le, Nat.lt_ceil]
  have hfloor (hn : 1 ≤ n) : ⌊Real.logb φ n⌋₊ = m ↔ φ ^ m ≤ (n : ℝ) ∧ (n : ℝ) < φ ^ (m + 1) := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn₀ := zero_lt_one.trans_le hn'
    rw [Nat.floor_eq_iff (logb_nonneg one_lt_goldenRatio hn'), ← Nat.cast_succ,
      le_logb_iff_rpow_le one_lt_goldenRatio hn₀, logb_lt_iff_lt_rpow one_lt_goldenRatio hn₀,
      rpow_natCast, rpow_natCast]
  refine ⟨fun ⟨hn, h⟩ => (hfloor hn).mp h, fun h => ?_⟩
  have hn' := (one_le_pow₀ one_lt_goldenRatio.le (n := m)).trans h.1
  have hn : 1 ≤ n := by exact_mod_cast hn'
  exact ⟨hn, (hfloor hn).mpr h⟩

/-- **Counting integers by their golden-ratio logarithm.** Let $d$ be the integer sequence with
$d(0) = 0$, $d(1) = 1$ and $d(m) = d(m-1) + d(m-2) + (-1)^m$ for $m \ge 2$, and let $\varphi$ be
the golden ratio. For every integer $m \ge 1$, the number of positive integers $n$ with
$\lfloor \log_\varphi n \rfloor = m$ equals $d(m)$.

Source: Petojević, Gorjanac Ranitović, Rastovac and Mandić, *The Golden Ratio,
Factorials, and the Lambert W Function*, Journal of Integer Sequences 27 (2024),
Article 24.5.7, Lemma 3 (`jis-2024-24.5.7-lem-3`). -/
public theorem ncard_floor_logb_goldenRatio_eq_alternatingSignFibonacci (m : ℕ)
    (hm : 1 ≤ m) :
    (({n : ℕ | 1 ≤ n ∧ ⌊Real.logb goldenRatio n⌋₊ = m}.ncard : ℕ) : ℤ) =
      alternatingSignFibonacci m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  have hmono : φ ^ (k + 1) ≤ φ ^ (k + 2) :=
    pow_le_pow_right₀ one_lt_goldenRatio.le (by omega)
  rw [floor_logb_goldenRatio_set, Set.ncard_coe_finset, Nat.card_Ico,
    Nat.cast_sub (Nat.ceil_mono hmono),
    Int.natCast_ceil_eq_ceil (pow_nonneg goldenRatio_pos.le _),
    Int.natCast_ceil_eq_ceil (pow_nonneg goldenRatio_pos.le _)]
  apply (Int.cast_inj (α := ℝ)).mp
  rw [Int.cast_sub, cast_ceil_goldenRatio_pow (by omega), cast_ceil_goldenRatio_pow (by omega),
    cast_alternatingSignFibonacci_succ, goldenPowers_add_two, pow_succ (-1 : ℝ) (k + 1)]
  ring

end MetaMathlibExt
