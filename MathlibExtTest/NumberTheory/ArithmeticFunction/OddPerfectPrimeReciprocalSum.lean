/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

/-! # Tests for `MathlibExt.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum` -/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum

open MathlibExt.NumberTheory.PrimitiveNondeficientWanted MetaMathlibExt

-- With exponent 5 the disjunct `e = 1` is impossible, so the fifth-power bound holds.
example (n q m : ℕ) (h : EulerianForm n q 5 m) : q ^ 5 < 2 * m ^ 2 := by
  simpa using eulerianForm_exponent_eq_one_or_pow_five_lt n q 5 m h

-- Corollary: an exponent different from 1 forces the fifth-power bound.
example (n q e m : ℕ) (h : EulerianForm n q e m) (he : e ≠ 1) : q ^ 5 < 2 * m ^ 2 := by
  simpa [he] using eulerianForm_exponent_eq_one_or_pow_five_lt n q e m h

-- For least prime factor 3, the bound is 2 + 9 / 36 = 9 / 4.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) (h3 : n.minFac = 3) :
    abundancySup n ≤ 9 / 4 := by
  have h := oddPerfect_abundancySup_le n hodd hperf
  rw [h3] at h
  norm_num at h
  exact h

-- Every odd perfect number satisfies the uniform bound 9 / 4.
example (n : ℕ) (hodd : Odd n) (hperf : n.Perfect) : abundancySup n ≤ 9 / 4 := by
  have h := oddPerfect_abundancySup_le n hodd hperf
  have hn1 : n ≠ 1 := fun h1 => by simp [h1, Nat.Perfect] at hperf
  have hp : n.minFac.Prime := Nat.minFac_prime hn1
  have hpdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hp2 : n.minFac ≠ 2 := fun h2 => hodd.not_two_dvd_nat (h2 ▸ hpdvd)
  have hpge : 3 ≤ n.minFac := by
    have h2 := hp.two_le
    omega
  have h3 : (3 : ℚ) ≤ n.minFac := by exact_mod_cast hpge
  have hpos : (0 : ℚ) < n.minFac := by exact_mod_cast Nat.minFac_pos n
  have hsq : (9 : ℚ) ≤ (n.minFac : ℚ) ^ 2 := by nlinarith [h3, hpos]
  have hle : (2 : ℚ) + 9 / (4 * (n.minFac : ℚ) ^ 2) ≤ 9 / 4 := by
    have hx0 : (n.minFac : ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hpos)
    have hxpos : (0 : ℚ) < (n.minFac : ℚ) ^ 2 := pow_pos hpos 2
    field_simp
    linarith
  calc abundancySup n ≤ 2 + 9 / (4 * (n.minFac : ℚ) ^ 2) := h
    _ ≤ 9 / 4 := hle

-- At `n = 6`, which is primitive non-deficient with `H(6) = 3` and least prime
-- factor `2`, any constant `C` in the bound satisfies `2 ≤ C`.
example (C : ℝ) (hC : ∀ n : ℕ, IsPrimitiveNondeficient n →
    (abundancySup n : ℝ) ≤ 2 + C / n.minFac) : 2 ≤ C := by
  have h6 : IsPrimitiveNondeficient 6 := by
    unfold IsPrimitiveNondeficient IsNondeficient
    decide +kernel
  have hHQ : abundancySup 6 = 3 := by
    unfold abundancySup
    decide +kernel
  have hHR : (abundancySup 6 : ℝ) = 3 := by exact_mod_cast hHQ
  have hmin : (6 : ℕ).minFac = 2 := by decide
  have hbound := hC 6 h6
  rw [hHR, hmin] at hbound
  norm_num at hbound
  linarith

-- At `n = 20`, the existential bound specializes to an inequality with `C / 2`.
example : ∃ C : ℝ, (abundancySup 20 : ℝ) ≤ 2 + C / 2 := by
  obtain ⟨C, hC⟩ := exists_abundancySup_le_two_add_div_minFac
  refine ⟨C, ?_⟩
  have h20 : IsPrimitiveNondeficient 20 := by
    unfold IsPrimitiveNondeficient IsNondeficient
    decide +kernel
  have hmin : (20 : ℕ).minFac = 2 := by decide
  have hbound := hC 20 h20
  rw [hmin] at hbound
  simpa using hbound

-- Below the crossing threshold, the lifted product stays at most two.
example (q : ℕ) (hq : q.Prime) (hodd : Odd q)
    (h : abundancySup (ordCompl[2] (q + 1)) < 2) :
    abundancySup (q * ordCompl[2] (q + 1)) ≤ 2 := by
  by_contra hcon
  exact not_abundancySup_oddPart_succ_lt_two_and_two_lt q hq hodd
    ⟨h, not_le.mp hcon⟩

-- At `q = 3` the odd part of `q + 1` is `1`.
example : ordCompl[2] (3 + 1) = 1 := by
  have h : (3 : ℕ) + 1 = 2 ^ 2 := by decide
  rw [h, Nat.ordCompl_self_pow Nat.prime_two]

-- The crossing is impossible at the concrete prime `q = 3`.
example : ¬ (abundancySup (ordCompl[2] (3 + 1)) < 2 ∧
    2 < abundancySup (3 * ordCompl[2] (3 + 1))) :=
  not_abundancySup_oddPart_succ_lt_two_and_two_lt 3 (by decide) (by decide)

end MathlibExtTest.NumberTheory.ArithmeticFunction.OddPerfectPrimeReciprocalSum
