/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.JacobiTwoSquareCount
public import MathlibExt.NumberTheory.X2Y2Count
public import MathlibExt.NumberTheory.ZsqrtdNormFactorization
public import Mathlib.Tactic.NormNum

/-!
# Tests for quadratic representation-count APIs

These examples exercise the public instances, canonical quadratic characters, prime behavior,
and the two representation-count formulas used by downstream developments.
-/

open SumSquares
open GaussianInt (gaussianInt_isUnit_iff gaussianInt_prime_of_natAbs_norm_prime
  gaussianInt_prime_one_add_I gaussianInt_two_eq gaussianInt_split_prime gaussianInt_split_conj
  gaussianInt_split_nonassociated gaussianIntReprFintype gaussianInt_card_repr_prime_pow)
open Zsqrtd.NegTwo (norm_nonneg' norm_eq_zero' norm_pos' abs_natCast_norm' div_def' mod_def'
  round_error norm_key norm_mod_lt' natAbs_norm_mod_lt' norm_le_norm_mul_left'
  zsqrtd_neg_two_isUnit_iff zsqrtd_neg_two_prime_of_natAbs_norm_prime zsqrtd_neg_two_prime_sqrtd
  zsqrtd_neg_two_two_eq zsqrtd_neg_two_mod8_obstruction zsqrtd_neg_two_inert zsqrtd_neg_two_split
  zsqrtd_neg_two_split_conj)

local notation "ℤ[i]" => GaussianInt

-- Euclidean division in `ℤ[√-2]`: `x = y * (x / y) + x % y` and the remainder has smaller norm.
example (x y : Zsqrtd (-2 : ℤ)) : y * (x / y) + x % y = x := by
  rw [mod_def']
  ring

example (x : Zsqrtd (-2 : ℤ)) {y : Zsqrtd (-2 : ℤ)} (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs :=
  natAbs_norm_mod_lt' x hy

-- The `EuclideanDomain` instance uses these `/` and `%`.
example (x y : Zsqrtd (-2 : ℤ)) : x % y = x - y * (x / y) :=
  EuclideanDomain.mod_eq_sub_mul_div x y

-- Gaussian primes: `5 = 2^2 + 1^2` splits, `3` stays prime.
example : Zsqrtd.norm (⟨2, 1⟩ : ℤ[i]) = ((5 : ℕ) : ℤ) ∧ Prime (⟨2, 1⟩ : ℤ[i]) :=
  ⟨by decide, gaussianInt_prime_of_natAbs_norm_prime (by norm_num [Zsqrtd.norm_def]; decide)⟩

example : Prime ((3 : ℕ) : ℤ[i]) :=
  (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3).mpr (by decide)

-- `ℤ[√-2]`: `3 = 1^2 + 2 * 1^2` splits into nonassociated conjugate primes.
example : ¬ Associated (star (⟨1, 1⟩ : Zsqrtd (-2 : ℤ))) ⟨1, 1⟩ := by
  let _ : Fact (3 : ℕ).Prime := ⟨by decide⟩
  exact (zsqrtd_neg_two_split_conj (p := 3) (by decide) (by decide)).2.2

-- The ring-independent norm API, at `d = -2`.
example : Zsqrtd.norm ((⟨1, 1⟩ : Zsqrtd (-2 : ℤ)) ^ 3) = 27 := by
  rw [Zsqrtd.norm_pow]
  decide

example {π : Zsqrtd (-2 : ℤ)} (hπ : Prime π) :
    ∃ ℓ s : ℕ, ℓ.Prime ∧ s ≠ 0 ∧ (Zsqrtd.norm π).natAbs = ℓ ^ s ∧ π ∣ (ℓ : Zsqrtd (-2 : ℤ)) :=
  Zsqrtd.prime_pow_norm_of_prime (by norm_num) hπ

example : EuclideanDomain (Zsqrtd (-2 : ℤ)) := inferInstance

example (x y : Zsqrtd (-2 : ℤ)) : x % y = x - y * (x / y) :=
  mod_def' x y

example : (⟨3, 0⟩ : Zsqrtd (-2 : ℤ)) / ⟨2, 0⟩ = ⟨2, 0⟩ := by
  rw [div_def']
  norm_num [Zsqrtd.norm_def]

example : (⟨-3, 0⟩ : Zsqrtd (-2 : ℤ)) / ⟨2, 0⟩ = ⟨-1, 0⟩ := by
  rw [div_def']
  norm_num [Zsqrtd.norm_def]

example : (⟨3, 0⟩ : Zsqrtd (-2 : ℤ)) % ⟨2, 0⟩ = ⟨-1, 0⟩ := by
  apply Zsqrtd.ext <;> norm_num [mod_def', div_def', Zsqrtd.norm_def]

example : ZMod.χ₄ (3 : ℕ) = -1 :=
  ZMod.χ₄_nat_three_mod_four (by decide)

example : ZMod.χ₈' (3 : ℕ) = 1 := by
  norm_num [ZMod.χ₈'_nat_eq_if_mod_eight]

example : Prime (⟨1, 1⟩ : ℤ[i]) :=
  gaussianInt_prime_one_add_I

example : Prime ((5 : ℕ) : Zsqrtd (-2 : ℤ)) := by
  let _ : Fact (5 : ℕ).Prime := ⟨by decide⟩
  exact zsqrtd_neg_two_inert (Or.inl (by decide))

example : (representationNumber 2 5 : ℤ) = 4 * divChiSum 5 :=
  representationNumber_two_jacobi_count 5 (by norm_num)

example : (repX2Y2Count 3 : ℤ) = 2 * divChiNeg2Sum 3 :=
  x2y2_count (by decide)

example : repX2Y2Count 3 = 4 := by
  let _ : Fact (3 : ℕ).Prime := ⟨by decide⟩
  simpa using repX2Y2Count_split_pow (p := 3) (e := 1)
    (Or.inr (by decide)) (π := (⟨1, 1⟩ : Zsqrtd (-2 : ℤ)))
    (by norm_num [Zsqrtd.norm_def])
    (zsqrtd_neg_two_prime_of_natAbs_norm_prime (by
      norm_num [Zsqrtd.norm_def]
      decide))

#print axioms SumSquares.representationNumber_two_jacobi_count
#print axioms SumSquares.x2y2_count
