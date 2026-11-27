/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp

/-!
# Girstmair's cotangent power coefficients

For `1 ≤ j ≤ r`, the coefficient at `(r, j)` vanishes when `r` and `j` have opposite parity.
We derive this from the recurrence for unsigned Stirling numbers of the first kind and
Pascal's identity.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Girstmair's cotangent power coefficients.** For natural numbers $r$ and $j$, the rational
number $c_{r,j}$ is
$$c_{r,j} = (-1)^{r-1} \sum_{k=j}^{r} \frac{(-2)^{k-j}}{(k-1)!} \binom{r}{k} S(k, j),$$
where $S(k, j)$ is the unsigned Stirling number of the first kind, the number of permutations
of $k$ elements with exactly $j$ cycles. Subtraction of natural numbers is truncated at $0$: for
$r = 0$ the exponent $r - 1$ is read as $0$, and for $j = 0$ the factor $(k-1)!$ of the term
$k = 0$ is read as $0! = 1$.

These coefficients express $(i \cot)^r$ in terms of the derivatives $i^j \cot^{(j-1)}$.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Equation (8). The equation is not in the journal record; it is read from the arXiv
version, arXiv:2504.08330, Section 3, where it also follows from the displayed derivation. -/
def cotangentPowerCoeff (r j : ℕ) : ℚ :=
  (-1) ^ (r - 1) * ∑ k ∈ Finset.Icc j r,
    (-2) ^ (k - j) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) * (Nat.stirlingFirst k j : ℚ)

/-- **Girstmair's coefficient at index (1, 1).** Girstmair's cotangent power coefficient
$c_{1,1}$ equals $1$, matching the identity $i \cot = i \cot$.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, characteristic value of Equation (8). -/
theorem cotangentPowerCoeff_one_one : cotangentPowerCoeff 1 1 = 1 := by
  simp [cotangentPowerCoeff, Nat.stirlingFirst]

/-- **Girstmair's coefficient at index (2, 2).** Girstmair's cotangent power coefficient
$c_{2,2}$ equals $-1$, matching the identity $(i \cot)^2 = 1 - i^2 \cot'$ with
$\cot' = -1 - \cot^2$.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, characteristic value of Equation (8). -/
theorem cotangentPowerCoeff_two_two : cotangentPowerCoeff 2 2 = -1 := by
  simp [cotangentPowerCoeff, Nat.stirlingFirst]

end

namespace cotangentPowerCoeff

open Finset

-- Multiplying column j by (-2)^j removes the truncated exponent from the Stirling sum.
-- The defining sum for positive j omits row zero.
private def scaledTerm (j : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => (-2) ^ (k + 1) / (k.factorial : ℚ) * Nat.stirlingFirst (k + 1) j

private lemma scaledTerm_step (k j : ℕ) :
    k * (scaledTerm (j + 1) (k + 1) + 2 * scaledTerm (j + 1) k) =
      -2 * scaledTerm j k := by
  cases k with
  | zero => simp [scaledTerm]
  | succ k =>
    simp only [scaledTerm, Nat.stirlingFirst_succ_succ (k + 1) j, Nat.factorial_succ,
      Nat.cast_add, Nat.cast_mul, Nat.cast_one, pow_succ]
    field_simp
    ring

private def binomialSum (r : ℕ) (f : ℕ → ℚ) : ℚ :=
  ∑ k ∈ range (r + 1), (r.choose k : ℚ) * f k

private lemma binomialSum_succ (r : ℕ) (f : ℕ → ℚ) :
    binomialSum (r + 1) f = binomialSum r f + binomialSum r (fun k ↦ f (k + 1)) :=
  sum_choose_succ_mul (fun k _ ↦ f k) r

private lemma binomialSum_mul_index (r : ℕ) (f : ℕ → ℚ) :
    binomialSum (r + 1) (fun k ↦ k * f k) =
      (r + 1 : ℚ) * binomialSum r (fun k ↦ f (k + 1)) := by
  rw [binomialSum, sum_range_succ', binomialSum, mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [← mul_assoc, ← Nat.cast_mul, ← Nat.add_one_mul_choose_eq, Nat.cast_mul, Nat.cast_succ,
    mul_assoc]

-- Two applications of Pascal's identity turn a two-row difference into an index-weighted sum.
private lemma binomialSum_step (r : ℕ) (f : ℕ → ℚ) :
    (r + 1 : ℚ) * (binomialSum (r + 2) f - binomialSum r f) =
      binomialSum (r + 1) (fun k ↦ k * (f (k + 1) + 2 * f k)) := by
  rw [binomialSum_mul_index, binomialSum_succ (r + 1), binomialSum_succ r, binomialSum_succ r]
  simp only [binomialSum, mul_add, mul_left_comm _ (2 : ℚ), sum_add_distrib, ← mul_sum]
  ring

private lemma binomialSum_eq_zero (r j : ℕ) (hp : r % 2 ≠ j % 2) :
    binomialSum r (scaledTerm j) = 0 := by
  induction r using Nat.twoStepInduction generalizing j with
  | zero => simp [binomialSum, scaledTerm]
  | one =>
    cases j with
    | zero => simp [binomialSum, sum_range_succ, scaledTerm]
    | succ j =>
      have h : 1 < j + 1 := by omega
      simp [binomialSum, sum_range_succ, scaledTerm, Nat.stirlingFirst_eq_zero_of_lt h]
  | more r ih₀ ih₁ =>
    cases j with
    | zero =>
      have hz (k : ℕ) : scaledTerm 0 k = 0 := by cases k <;> simp [scaledTerm]
      simp [binomialSum, hz]
    | succ j =>
      have h := binomialSum_step r (scaledTerm (j + 1))
      simp_rw [scaledTerm_step] at h
      have hscale : binomialSum (r + 1) (fun k ↦ -2 * scaledTerm j k) =
          -2 * binomialSum (r + 1) (scaledTerm j) := by
        simp only [binomialSum, mul_left_comm _ (-2 : ℚ), mul_sum]
      rw [hscale, ih₁ j (by omega), ih₀ (j + 1) (by omega), mul_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (by positivity)

end cotangentPowerCoeff

open Finset cotangentPowerCoeff in
/-- **Parity of Girstmair's cotangent power coefficients.** For natural numbers $j$ and $r$ with
$1 \le j \le r$ and $r \not\equiv j \pmod 2$, Girstmair's cotangent power coefficient $c_{r,j}$
is $0$.

The source deduces this from the $\mathbb{Q}$-linear independence of the functions
$i^j \cot^{(j-1)}$.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Proposition 1, the sentence that follows it (`integers-2025-A63-prop-1`). -/
public theorem cotangentPowerCoeff_eq_zero_of_mod_two_ne {r j : ℕ} (hj : 1 ≤ j)
    (hjr : j ≤ r) (hpar : r % 2 ≠ j % 2) : cotangentPowerCoeff r j = 0 := by
  let f (k : ℕ) : ℚ := (r.choose k : ℚ) * scaledTerm j k
  have hlow : ∑ k ∈ range j, f k = 0 := by
    refine sum_eq_zero fun k hk ↦ ?_
    have hkj := mem_range.mp hk
    cases k <;> simp [f, scaledTerm, Nat.stirlingFirst_eq_zero_of_lt hkj]
  have hsum := sum_range_add_sum_Ico f (show j ≤ r + 1 by omega)
  rw [hlow, zero_add, Ico_add_one_right_eq_Icc] at hsum
  have hzero : ∑ k ∈ Icc j r, f k = 0 := hsum.trans (binomialSum_eq_zero r j hpar)
  unfold cotangentPowerCoeff
  apply mul_eq_zero_of_right
  apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero j (by norm_num : (-2 : ℚ) ≠ 0))
  rw [mul_sum, ← hzero]
  refine sum_congr rfl fun k hk ↦ ?_
  obtain ⟨hjk, _⟩ := mem_Icc.mp hk
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  have hpow : (-2 : ℚ) ^ j * (-2) ^ (k + 1 - j) = (-2) ^ (k + 1) := by
    rw [← pow_add, Nat.add_sub_of_le hjk]
  simp only [f, scaledTerm, Nat.succ_eq_add_one, Nat.add_sub_cancel]
  rw [← hpow]
  ring

end MetaMathlibExt
