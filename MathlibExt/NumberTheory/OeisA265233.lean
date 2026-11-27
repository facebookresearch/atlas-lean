/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Franel number formula for A265233

At positive indices, `a265233_eq_sum_franel` expresses `a265233` as one sixth of a weighted
binomial sum of Franel numbers. A telescoping sum proves the Franel recurrence. Translating
the monomials by four then gives the recurrence for the weighted sum.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.OeisA265233Wanted

/-- **The sequence A265233.** The sequence $(a_n)_{n \ge 0}$ of rational numbers is given by
$a_0 = 1$, $a_1 = 1$, $a_2 = 7$, $a_3 = 56$ and, for every integer $N \ge 4$,

$$N^2 a_N = (19N^2 - 19N + 6)\, a_{N-1} - 96 (N-1)^2 a_{N-2} + 144 (N-1)(N-2)\, a_{N-3}.$$

Source: Juntao Jin, "An Explicit Formula and a Recurrence for OEIS A265233", Theorem 1(2). -/
def a265233 : ℕ → ℚ
  | 0 => 1
  | 1 => 1
  | 2 => 7
  | 3 => 56
  | n + 4 =>
      ((19 * ((n : ℚ) + 4) ^ 2 - 19 * ((n : ℚ) + 4) + 6) *
          a265233 (n + 3)
        - 96 * ((n : ℚ) + 3) ^ 2 * a265233 (n + 2)
        + 144 * ((n : ℚ) + 3) * ((n : ℚ) + 2) *
          a265233 (n + 1))
        / ((n : ℚ) + 4) ^ 2

private abbrev franel (n : ℕ) : ℚ := MetaMathlibExt.binomialPowerSeq 3 0 n

private def cube (n k : ℕ) : ℚ := (n.choose k : ℚ) ^ 3

private theorem franel_eq_sum (n b : ℕ) (hn : n < b) :
    franel n = ∑ k ∈ Finset.range b, cube n k := by
  simp only [franel, MetaMathlibExt.binomialPowerSeq, pow_zero, mul_one, Nat.cast_sum,
    Nat.cast_pow, cube]
  refine Finset.sum_subset (Finset.range_mono hn) ?_
  intro k _ hk
  simp [Nat.choose_eq_zero_of_lt (by simpa using hk : n < k)]

private theorem cube_row (n k : ℕ) :
    (n + 1 : ℚ) ^ 3 * cube n k = (n + 1 - k : ℚ) ^ 3 * cube (n + 1) k := by
  by_cases hk : k ≤ n + 1
  · have h := congrArg (fun a : ℕ => (a : ℚ)) (Nat.choose_mul_succ_eq n k)
    push_cast [Nat.cast_sub hk] at h
    simp only [cube, ← mul_pow]
    rw [mul_comm, h, mul_comm]
  · have h₁ : n < k := by omega
    simp [cube, Nat.choose_eq_zero_of_lt h₁, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]

private theorem cube_col (n k : ℕ) (hk : k ≤ n) :
    (k + 1 : ℚ) ^ 3 * cube n (k + 1) = (n - k : ℚ) ^ 3 * cube n k := by
  have h := congrArg (fun a : ℕ => (a : ℚ)) (Nat.choose_succ_right_eq n k)
  push_cast [Nat.cast_sub hk] at h
  simp only [cube, ← mul_pow]
  rw [mul_comm, h, mul_comm]

-- Multiplying this polynomial by k³ times the cubed binomial coefficient gives the
-- boundary term in the telescoping sum for the Franel recurrence.
private def certificate (n k : ℚ) : ℚ :=
  6 * k ^ 2 - 15 * n * k + 10 * n ^ 2 + 4 * k ^ 3 - 18 * n * k ^ 2 +
    27 * n ^ 2 * k - 14 * n ^ 3

private theorem franel_recurrence (n : ℕ) :
    (n + 2 : ℚ) ^ 2 * franel (n + 2) - (7 * (n + 2 : ℚ) * (n + 1) + 2) * franel (n + 1) -
      8 * (n + 1 : ℚ) ^ 2 * franel n = 0 := by
  let N : ℚ := n + 2
  let G (k : ℕ) := certificate N k * k ^ 3 * cube (n + 2) k
  have step (k : ℕ) (hk : k ∈ Finset.range (n + 3)) :
      N ^ 3 * (n + 1) * (N ^ 2 * cube (n + 2) k -
        (7 * N * (n + 1) + 2) * cube (n + 1) k - 8 * (n + 1) ^ 2 * cube n k) =
        G (k + 1) - G k := by
    have h₀ := cube_row n k
    have h₁ := cube_row (n + 1) k
    have h₂ := cube_col (n + 2) k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    dsimp [G, N]
    push_cast at h₁ h₂ ⊢
    linear_combination (norm := (simp only [certificate]; ring))
      -((7 * (n + 2 : ℚ) * (n + 1) + 2) * (n + 1) + 8 * (n + 1 - k) ^ 3) * h₁ -
      8 * (n + 2 : ℚ) ^ 3 * h₀ - certificate (n + 2) (k + 1) * h₂
  have total := Finset.sum_congr rfl step
  rw [Finset.sum_range_sub] at total
  simp only [← Finset.mul_sum, Finset.sum_sub_distrib] at total
  rw [← franel_eq_sum (n + 2) _ (by omega), ← franel_eq_sum (n + 1) _ (by omega),
    ← franel_eq_sum n _ (by omega)] at total
  have hG : G (n + 3) - G 0 = 0 := by
    simp [G, cube]
  rw [hG] at total
  exact (mul_eq_zero.mp total).resolve_left (by dsimp [N]; positivity)

open Polynomial

-- Regard the Franel numbers as the values of a linear functional on the monomials.
private noncomputable def moment : ℚ[X] →ₗ[ℚ] ℚ :=
  lsum fun n => LinearMap.mulRight ℚ (franel n)

private theorem moment_X_pow (n : ℕ) : moment (X ^ n) = franel n := by
  simp [moment, LinearMap.mulRight_apply, ← monomial_one_right_eq_X_pow]

private theorem moment_C_mul (c : ℚ) (p : ℚ[X]) : moment (C c * p) = c * moment p := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

private noncomputable def cubic : ℚ[X] := X * (X + 1) * (X - 8)

-- Applying the moment functional to this differential operator on Xⁿ gives the Franel
-- recurrence. Linearity extends that vanishing to every polynomial.
private noncomputable def ode (p : ℚ[X]) : ℚ[X] :=
  cubic * derivative (derivative p) + derivative cubic * derivative p + (X - 2) * p

-- In the coordinate Y = X + c, write the cubic as Y³ + aY² + bY + d.
-- The four coefficients below give the recurrence on powers of Y.
private theorem ode_pow (Y : ℚ[X]) (a b d e : ℚ) (m : ℕ) (hY : derivative Y = 1)
    (hA : cubic = Y ^ 3 + C a * Y ^ 2 + C b * Y + C d) (he : X - 2 = Y + C e) :
    ode (Y ^ (m + 2)) =
      C ((m + 3 : ℚ) ^ 2) * Y ^ (m + 3) +
      C (a * (m + 2) * (m + 3) + e) * Y ^ (m + 2) +
      C (b * (m + 2) ^ 2) * Y ^ (m + 1) +
      C (d * (m + 1) * (m + 2)) * Y ^ m := by
  rw [ode, hA, he]
  simp only [derivative_add, derivative_pow_succ, derivative_mul, derivative_C, hY,
    zero_mul, zero_add, add_zero, mul_one]
  push_cast
  simp only [pow_succ, pow_zero, map_add, map_mul, C_ofNat, C_1, C_eq_natCast]
  ring

private theorem moment_ode_X_pow (n : ℕ) : moment (ode (X ^ n)) = 0 := by
  match n with
  | 0 =>
    have h : ode 1 = C 1 * X ^ 1 - C 2 * X ^ 0 := by simp [ode, C_ofNat]
    rw [pow_zero, h, map_sub]
    simp only [moment_C_mul, moment_X_pow]
    norm_num [franel, MetaMathlibExt.binomialPowerSeq, Finset.sum_range_succ, Nat.choose]
  | 1 =>
    have h : ode X = C 4 * X ^ 2 - C 16 * X ^ 1 - C 8 * X ^ 0 := by
      simp [ode, cubic, derivative_mul, C_ofNat]
      ring
    rw [pow_one, h]
    simp only [map_sub moment, moment_C_mul, moment_X_pow]
    norm_num [franel, MetaMathlibExt.binomialPowerSeq, Finset.sum_range_succ, Nat.choose]
  | n + 2 =>
    rw [ode_pow X (-7) (-8) 0 (-2) n derivative_X (by simp [cubic, C_ofNat]; ring)
      (by simp [C_ofNat]; ring)]
    simp only [map_add moment, moment_C_mul, moment_X_pow]
    have h := franel_recurrence (n + 1)
    push_cast at h
    linear_combination h

private theorem moment_ode (p : ℚ[X]) : moment (ode p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa [ode, mul_add, map_add, add_add_add_comm, add_assoc, add_comm, add_left_comm]
      using congrArg₂ (· + ·) hp hq
  | monomial n r =>
    rw [← C_mul_X_pow_eq_monomial]
    have h : ode (C r * X ^ n) = C r * ode (X ^ n) := by
      simp [ode, derivative_mul]
      ring
    rw [h, moment_C_mul, moment_ode_X_pow, mul_zero]

private noncomputable def weighted (n : ℕ) : ℚ := moment ((X + C 4) ^ n)

private theorem weighted_eq_sum (n : ℕ) :
    weighted n = ∑ m ∈ Finset.range (n + 1), (n.choose m : ℚ) * 4 ^ (n - m) * franel m := by
  rw [weighted, add_pow, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  have h : X ^ m * C (4 : ℚ) ^ (n - m) * (n.choose m : ℚ[X]) =
      C ((n.choose m : ℚ) * 4 ^ (n - m)) * X ^ m := by
    rw [map_mul, map_pow, C_eq_natCast]
    ring
  rw [h, moment_C_mul, moment_X_pow]

private theorem weighted_recurrence (n : ℕ) :
    (n + 3 : ℚ) ^ 2 * weighted (n + 3) =
      (19 * (n + 3 : ℚ) ^ 2 - 19 * (n + 3) + 6) * weighted (n + 2) -
      96 * (n + 2 : ℚ) ^ 2 * weighted (n + 1) + 144 * (n + 2 : ℚ) * (n + 1) * weighted n := by
  have h := moment_ode ((X + C 4) ^ (n + 2))
  rw [ode_pow _ (-19) 96 (-144) (-6) n (derivative_X_add_C 4)
    (by simp [cubic, C_ofNat]; ring) (by simp [C_ofNat]; ring)] at h
  simp only [map_add moment, moment_C_mul] at h
  unfold weighted
  linear_combination h

/-- **Explicit formula for A265233 in terms of Franel numbers.** Let $(a_n)_{n \ge 0}$ be the
sequence A265233 and let $f_m = \sum_{k=0}^{m} \binom{m}{k}^3$ be the $m$-th Franel number. For
every integer $n \ge 1$,

$$a_n = \frac{1}{6} \sum_{m=0}^{n} \binom{n}{m} 4^{n-m} f_m.$$

Source: Juntao Jin, "An Explicit Formula and a
Recurrence for OEIS A265233", Theorem 1. -/
theorem a265233_eq_sum_franel (n : ℕ) (hn : 1 ≤ n) :
    a265233 n = (1 / 6) * ∑ m ∈ Finset.range (n + 1),
      (Nat.choose n m : ℚ) * 4 ^ (n - m) *
        (MetaMathlibExt.binomialPowerSeq 3 0 m : ℚ) := by
  rw [← weighted_eq_sum]
  induction n using a265233.induct with
  | case1 => omega
  | case2 | case3 | case4 =>
    norm_num [a265233, weighted_eq_sum, franel, MetaMathlibExt.binomialPowerSeq,
      Finset.sum_range_succ, Nat.choose]
  | case5 n ih₃ ih₂ ih₁ =>
    rw [a265233, ih₃ (by omega), ih₂ (by omega), ih₁ (by omega)]
    apply (div_eq_iff (by positivity)).2
    have h := weighted_recurrence (n + 1)
    push_cast at h
    linear_combination -(1 / 6 : ℚ) * h

end MathlibExt.NumberTheory.OeisA265233Wanted
