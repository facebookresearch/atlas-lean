/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.PellSilverRatio
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import MathlibExt.NumberTheory.OlympicGamesNumerationExistsPellHalfCompanionRepresentation
import Mathlib.Tactic.LinearCombination

/-!
# Floor of greedy Pell sums times the silver ratio

For natural-number digits in the alternating Pell and half-companion Pell basis, assume every
prefix prior to place $m$ is smaller than the weight at $m$, for $1 \le m \le n+1$. Multiplying
the sum through place $n$ by $1+\sqrt 2$ and taking the floor shifts the digits to the next terms
of their respective sequences. The prefix inequalities make the source's greediness assumption
explicit and also allow leading zeros and the empty sum ($n=0$).

The two alternating recurrences for the weights are also satisfied by the single-digit errors.
Tracking a stronger bound when the prefix has room for one more copy of its last weight keeps
the total error below one.

## References

* Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial Games with
  Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, pp. 1–38, Theorem 5, Proposition 2 (1),
  (2), and Theorem 6 (1).
* The two prefix bounds parallel the proof of `floor_greedy_odd_fib_sum_mul_goldenRatio` in
  `MathlibExt.NumberTheory.GreedyOddFibonacciFloor`.
-/

namespace MetaMathlibExt

open Finset

local notation "q" => (Real.sqrt 2 - 1)

private noncomputable def pellDigitError (j : ℕ) : ℝ :=
  if j % 2 = 1 then q ^ j else Real.sqrt 2 * q ^ j

/-- **Floor of greedy Pell sums times $1 + \sqrt 2$.** Let $P_n$ be the Pell numbers ($P_0 = 0$,
$P_1 = 1$, $P_{n+2} = 2P_{n+1} + P_n$) and $H_n$ the half-companion Pell numbers
($H_0 = H_1 = 1$, $H_{n+2} = 2H_{n+1} + H_n$). Let $R_k = P_k$ and $R'_k = H_k$ for odd $k$, and
$R_k = H_k$ and $R'_k = P_k$ for even $k$. Let $n$ be a natural number and $a_1, a_2, \dots$
natural numbers such that $\sum_{k=1}^{m-1} a_k R_k < R_m$ for every $1 \le m \le n + 1$, and let
$t = \sum_{k=1}^{n} a_k R_k$. Then $\lfloor t (1 + \sqrt 2) \rfloor = \sum_{k=1}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 5;
$n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 6 (1). -/
public theorem floor_greedy_pell_halfCompanion_sum_mul_one_add_sqrt_two (R R' : ℕ → ℕ)
    (hR : ∀ k, R k = if k % 2 = 1 then pellNumber k else pellLucasSequence k)
    (hR' : ∀ k, R' k = if k % 2 = 1 then pellLucasSequence k else pellNumber k)
    (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m, 1 ≤ m → m ≤ n + 1 → ∑ k ∈ Ico 1 m, a k * R k < R m) :
    ⌊((∑ k ∈ Icc 1 n, a k * R k : ℕ) : ℝ) * (1 + Real.sqrt 2)⌋₊ =
      ∑ k ∈ Icc 1 n, a k * R' (k + 1) := by
  have hs₁ : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hs₂ := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hq : 0 < q := sub_pos.mpr hs₁
  have hq₁ : Real.sqrt 2 * q < 1 := by nlinarith only [hs₁, hs₂]
  have hpos (j : ℕ) : 0 < pellDigitError j := by
    unfold pellDigitError
    split
    · exact pow_pos hq _
    · exact mul_pos (zero_lt_one.trans hs₁) (pow_pos hq _)
  have hdecr (j : ℕ) : pellDigitError (j + 1) < pellDigitError j := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · simp [pellDigitError, Nat.add_mod, pow_add]
      linarith only [mul_lt_mul_of_pos_right (sub_lt_self (Real.sqrt 2) zero_lt_one)
        (pow_pos hq (2 * k))]
    · have h := mul_lt_mul_of_pos_right hq₁ (pow_pos hq (2 * k + 1))
      simp only [pow_add, pow_one, one_mul] at h
      simp [pellDigitError, Nat.add_mod, pow_add]
      linarith only [h]
  have hstep (j : ℕ) : ∃ b : ℕ, R (j + 2) + R j = b * R (j + 1) ∧
      pellDigitError (j + 2) + pellDigitError j = (b : ℝ) * pellDigitError (j + 1) := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · refine ⟨4, pell_halfCompanion_place_even_step hR k, ?_⟩
      simp [pellDigitError, Nat.add_mod, pow_add]
      linear_combination q ^ (2 * k) * (Real.sqrt 2 - 2) * hs₂
    · refine ⟨2, ?_, ?_⟩
      · simpa only [Nat.add_assoc, Nat.reduceAdd] using pell_halfCompanion_place_odd_step hR k
      · simp [pellDigitError, Nat.add_mod, pow_add]
        linear_combination -q ^ (2 * k + 1) * hs₂
  let S (j : ℕ) := ∑ k ∈ Icc 1 j, a k * R k
  let E (j : ℕ) := ∑ k ∈ Icc 1 j, (a k : ℝ) * pellDigitError k
  have hS (j : ℕ) (hj : j ≤ n) : S j < R (j + 1) := by
    simpa only [Finset.Ico_add_one_right_eq_Icc] using ha (j + 1) (by omega) (by omega)
  have hbounds (j : ℕ) (hj : j ≤ n) : E j ≤ 1 - pellDigitError j + pellDigitError (j + 1) ∧
      (S j + R j < R (j + 1) → E j ≤ 1 - pellDigitError j) := by
    induction j with
    | zero =>
      have hzero : R 0 = 1 := by rw [hR]; decide
      have hone : R 1 = 1 := by rw [hR]; decide
      constructor
      · norm_num [E, pellDigitError]
      · simp [S, hzero, hone]
    | succ j ih =>
      obtain ⟨hprev, hsmall⟩ := ih (by omega)
      obtain ⟨b, hw, he⟩ := hstep j
      have hSj : S (j + 1) = S j + a (j + 1) * R (j + 1) := sum_Icc_succ_top (by omega) _
      have hEj : E (j + 1) = E j + (a (j + 1) : ℝ) * pellDigitError (j + 1) :=
        sum_Icc_succ_top (by omega) _
      -- This also bounds a prefix with one extra copy of the last weight, if it still fits.
      have hfit (c : ℕ) (hc : S j + c * R (j + 1) < R (j + 2)) :
          E j + (c : ℝ) * pellDigitError (j + 1) ≤
            1 - pellDigitError (j + 1) + pellDigitError (j + 2) := by
        have hcb : c < b := by
          by_contra! h
          have hmul := Nat.mul_le_mul_right (R (j + 1)) h
          omega
        by_cases h : c + 2 ≤ b
        · have hcast : (c : ℝ) + 2 ≤ (b : ℝ) := by exact_mod_cast h
          have hmul := mul_le_mul_of_nonneg_right hcast (hpos (j + 1)).le
          linarith only [hprev, hmul, he]
        · have hmax : b = c + 1 := by omega
          have hlow : S j + R j < R (j + 1) := by
            rw [hmax, Nat.add_mul, one_mul] at hw
            omega
          have hcast : (b : ℝ) = (c : ℝ) + 1 := by exact_mod_cast hmax
          rw [hcast, add_mul, one_mul] at he
          linarith only [hsmall hlow, he]
      rw [hEj]
      constructor
      · exact hfit _ (hSj ▸ hS (j + 1) hj)
      · intro hs
        rw [hSj] at hs
        have haug : S j + (a (j + 1) + 1) * R (j + 1) < R (j + 2) := by
          simpa only [Nat.add_mul, one_mul, ← add_assoc] using hs
        have h := hfit _ haug
        push_cast at h
        linarith only [h, hdecr (j + 1)]
  have hnonneg : 0 ≤ E n := sum_nonneg fun j _ ↦
    mul_nonneg (Nat.cast_nonneg _) (hpos j).le
  have hlt : E n < 1 := by
    have h := (hbounds n le_rfl).1
    linarith only [h, hdecr n]
  have hcoeff (j : ℕ) : (R j : ℝ) * (1 + Real.sqrt 2) = R' (j + 1) + pellDigitError j := by
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' j
    · simpa [hR, hR', pellDigitError, Nat.add_mod] using
        (pellNumber_odd_mul_one_add_sqrt_two k).2
    · simpa [hR, hR', pellDigitError, Nat.add_mod, Nat.add_assoc] using
        (pellNumber_odd_mul_one_add_sqrt_two k).1
  have hsum : (S n : ℝ) * (1 + Real.sqrt 2) =
      ((∑ k ∈ Icc 1 n, a k * R' (k + 1) : ℕ) : ℝ) + E n := by
    simp only [S, E, Nat.cast_sum, Nat.cast_mul, sum_mul]
    simp_rw [mul_assoc, hcoeff, mul_add, sum_add_distrib]
  change ⌊(S n : ℝ) * (1 + Real.sqrt 2)⌋₊ = _
  rw [hsum, Nat.floor_eq_iff (by positivity)]
  exact ⟨le_add_of_nonneg_right hnonneg, add_lt_add_right hlt _⟩

end MetaMathlibExt
