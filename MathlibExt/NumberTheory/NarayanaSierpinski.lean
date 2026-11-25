/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.NarayanaSequence
public import MathlibExt.NumberTheory.SierpinskiRieselRepdigits
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Preorder.Finite

/-!
# Sierpiński numbers in Narayana's cows sequence

Infinitely many distinct Narayana numbers are Sierpiński numbers. At indices congruent to
229972 modulo 718391520, the terms have a common residue modulo twice the product of the
six covering primes 3, 5, 7, 13, 17 and 241.
-/

namespace MetaMathlibExt

namespace infinite_setOf_isSierpinskiNumber_narayanaCowsSequence

open Matrix

private abbrev R := ZMod 11184810

private def step : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 0, 0, 1; 1, 0, 1]

private def state (n : ℕ) : Fin 3 → R :=
  ![narayanaCowsSequence n, narayanaCowsSequence (n + 1), narayanaCowsSequence (n + 2)]

private theorem state_eq (n : ℕ) : state n = (step ^ n) *ᵥ ![0, 1, 1] := by
  induction n with
  | zero => rw [pow_zero, one_mulVec]; rfl
  | succ n ih =>
    rw [pow_succ', ← mulVec_mulVec, ← ih]
    funext i
    fin_cases i <;> simp [state, step, mulVec, dotProduct, Fin.sum_univ_succ,
      narayanaCowsSequence]
    ac_rfl

private theorem binPow_eq_pow {M : Type*} [Monoid M] (x : M) (n : ℕ) :
    npowBinRec n x = x ^ n := by
  induction n with
  | zero => simp [npowBinRec_zero]
  | succ n ih => rw [npowBinRec_succ, ih, pow_succ]

private theorem residue (q : ℕ) :
    narayanaCowsSequence (229972 + 718391520 * q) ≡ 603713 [MOD 11184810] := by
  -- Repeated squaring verifies the period and the residue at the initial index.
  have hperiod : step ^ 718391520 = 1 := by
    rw [← binPow_eq_pow]
    decide +kernel
  have hvalue : ((step ^ 229972) *ᵥ ![0, 1, 1]) 0 = 603713 := by
    rw [← binPow_eq_pow]
    decide +kernel
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  change state (229972 + 718391520 * q) 0 = 603713
  rw [state_eq, pow_add, pow_mul, hperiod, one_pow, mul_one]
  exact hvalue

private theorem sierpinski_of_residue {k : ℕ} (hk : k ≡ 603713 [MOD 11184810]) :
    IsSierpinskiNumber k := by
  refine ⟨Nat.odd_iff.mpr (hk.of_dvd (by decide : 2 ∣ 11184810)), ?_⟩
  intro n _
  -- For each exponent modulo 24, choose a divisor that works on the entire class.
  have hcover : ∀ r : Fin 24, ∃ p ∈ [3, 5, 7, 13, 17, 241],
      2 ≤ p ∧ p ≤ 241 ∧ p ∣ 11184810 ∧ 2 ^ 24 ≡ 1 [MOD p] ∧
      p ∣ 603713 * 2 ^ (r : ℕ) + 1 := by decide
  obtain ⟨p, _, hp, hple, hmod, hperiod, hr⟩ := hcover ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hpow : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.mod_add_div n 24, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using (hperiod.pow (n / 24)).mul_left (2 ^ (n % 24))
  have hfactor := ((((hk.of_dvd hmod).mul hpow).add_right 1).dvd_iff dvd_rfl).2 hr
  have hk_le : 603713 ≤ k := calc
    603713 = k % 11184810 := hk.symm
    _ ≤ k := Nat.mod_le _ _
  have := Nat.le_mul_of_pos_right k (by positivity : 0 < 2 ^ n)
  exact Nat.not_prime_of_dvd_of_lt hfactor hp (by omega)

private theorem lower_bound : ∀ n, n + 1 ≤ narayanaCowsSequence (n + 3)
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | n + 3 => by
    change n + 3 + 1 ≤ narayanaCowsSequence (n + 2 + 3) + narayanaCowsSequence (n + 3)
    have := lower_bound (n + 2)
    have := lower_bound n
    omega

end infinite_setOf_isSierpinskiNumber_narayanaCowsSequence

open infinite_setOf_isSierpinskiNumber_narayanaCowsSequence in
/-- **Infinitely many Narayana numbers are Sierpiński numbers.** There are infinitely many
natural numbers $k$ that are Sierpiński numbers and terms of Narayana's cows sequence $(N_t)$,
that is, $k = N_t$ for some $t$; here a Sierpiński number is an odd $k$ such that
$k \cdot 2^n + 1$ is not prime for every $n \ge 1$.

Source: Katherine Franzone and Joshua Harrington, *Sierpiński and Riesel Numbers in Narayana's
Cow Sequence*, INTEGERS 24 (2024), Article A10, Theorem 3 (`integers-2024-A10-thm-3`). -/
public theorem infinite_setOf_isSierpinskiNumber_narayanaCowsSequence :
    {k : ℕ | IsSierpinskiNumber k ∧ ∃ t, narayanaCowsSequence t = k}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro b
  refine ⟨_, ⟨sierpinski_of_residue (residue b), _, rfl⟩, ?_⟩
  have h := lower_bound (229969 + 718391520 * b)
  rw [show 229969 + 718391520 * b + 3 = 229972 + 718391520 * b by omega] at h
  omega

end MetaMathlibExt
