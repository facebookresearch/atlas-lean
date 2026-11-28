/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TruncatedLogDiscriminantFinitePrimesIsSquareDiscrTruncatedLog
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.ComputeDegree
import MathlibExt.NumberTheory.TruncatedLogResultantPos

namespace MathlibExtTest.NumberTheory.TruncatedLogDiscriminantFinitePrimesIsSquareDiscrTruncatedLog

open MetaMathlibExt

-- For `m = 3`, only finitely many primes `q` with `3 * q ≡ 1 [MOD 4]` give a square discriminant.
example : {q : ℕ | q.Prime ∧ 3 * q % 4 = 1 ∧
    IsSquare (truncatedLogPolynomial (3 * q)).discr}.Finite :=
  finite_primes_isSquare_discr_truncatedLog (m := 3) (by decide)

-- Hence those primes are bounded.
example : BddAbove {q : ℕ | q.Prime ∧ 3 * q % 4 = 1 ∧
    IsSquare (truncatedLogPolynomial (3 * q)).discr} :=
  (finite_primes_isSquare_discr_truncatedLog (m := 3) (by decide)).bddAbove

-- For `m = 5`, only finitely many primes `q` with `5 * q ≡ 1 [MOD 4]` give a square discriminant.
example : {q : ℕ | q.Prime ∧ 5 * q % 4 = 1 ∧
    IsSquare (truncatedLogPolynomial (5 * q)).discr}.Finite :=
  finite_primes_isSquare_discr_truncatedLog (m := 5) (by decide)

open Polynomial

-- Independently compute the paper's auxiliary product at m = 3 by reducing the second
-- polynomial modulo 1 + X + X² and evaluating the resulting linear resultant.
private lemma auxProduct_three : truncatedLogAuxProduct 3 = 13 / 36 := by
  let f : ℚ[X] := 1 + X + X ^ 2
  let g : ℚ[X] := C (1 / 3) + X + C (1 / 2) * X ^ 2
  have hf' : (∑ j ∈ Finset.range 3, (X : ℚ[X]) ^ j) = f := by
    simp [f, Finset.sum_range_succ]
  have hg' : (C ((3 : ℕ) : ℚ)⁻¹ + ∑ j ∈ Finset.Icc (1 : ℕ) (3 - 1),
      C ((j : ℚ)⁻¹) * X ^ j) = g := by
    norm_num [g, show (3 : ℕ) - 1 = 2 by decide,
      show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide, add_assoc]
  have haux : truncatedLogAuxProduct 3 = resultant f g := by
    calc
      truncatedLogAuxProduct 3 = _ := rfl
      _ = resultant f g := congrArg₂ (fun a b : ℚ[X] => resultant a b) hf' hg'
  have hf : f.natDegree = 2 := by dsimp [f]; compute_degree!
  have hg : g.natDegree = 2 := by dsimp [g]; compute_degree!
  have hrem : g = C (1 / 2) * (X - C (1 / 3)) + f * C (1 / 2) := by
    dsimp [f, g]
    calc
      _ = (C (1 / 2 : ℚ) - C (1 / 2) * C (1 / 3)) +
          (C (1 / 2) * X + X * C (1 / 2)) + C (1 / 2) * X ^ 2 := by
        rw [← C_mul, ← C_sub, mul_comm X, ← add_mul, ← C_add]
        norm_num
      _ = _ := by ring
  rw [haux, hf, hg, hrem,
    resultant_add_mul_right _ _ _ _ _ (by simp) hf.le, resultant_C_mul_right]
  rw [show 2 = 1 + 1 by decide, resultant_add_right_deg _ _ _ 1 1 (by simp),
    resultant_X_sub_C_right _ _ _ hf.le]
  norm_num [f, coeff_add, coeff_one, coeff_X, coeff_X_pow, eval_add, eval_pow]

private lemma valuation_nat_of_not_dvd {q a : ℕ} (h : ¬ q ∣ a) :
    padicValRat q (a : ℚ) = 0 := by
  rw [← Int.cast_natCast, padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd (by exact_mod_cast h), Nat.cast_zero]

private lemma valuation_fraction_of_not_dvd {q a b : ℕ} [Fact q.Prime]
    (ha : ¬ q ∣ a) (hb : ¬ q ∣ b) : padicValRat q ((a : ℚ) / b) = 0 := by
  have ha' : a ≠ 0 := fun h => ha (h ▸ dvd_zero q)
  have hb' : b ≠ 0 := fun h => hb (h ▸ dvd_zero q)
  rw [padicValRat.div (by exact_mod_cast ha') (by exact_mod_cast hb'),
    valuation_nat_of_not_dvd ha, valuation_nat_of_not_dvd hb, sub_zero]

-- The harmonic branch puts 11 in E₃; the auxiliary numerator's prime 13 is
-- filtered out by the congruence. Neither numerator is divisible by 7.
private lemma seven_not_exceptional_three : 7 ∉ truncatedLogExceptionalPrimes 3 := by
  have hH : harmonic 3 = 11 / 6 := by norm_num [harmonic_succ]
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hX : padicValRat 7 (13 / 36) = 0 :=
    valuation_fraction_of_not_dvd (q := 7) (a := 13) (b := 36) (by decide) (by decide)
  have hY : padicValRat 7 (11 / 6) = 0 :=
    valuation_fraction_of_not_dvd (q := 7) (a := 11) (b := 6) (by decide) (by decide)
  norm_num [truncatedLogExceptionalPrimes, auxProduct_three, hH, hX, hY]

example : 11 ∈ truncatedLogExceptionalPrimes 3 := by
  have hH : harmonic 3 = 11 / 6 := by norm_num [harmonic_succ]
  have hp : Nat.Prime 11 := by decide
  have : Fact (Nat.Prime 11) := ⟨hp⟩
  have h11 : padicValRat 11 (11 : ℚ) = 1 := padicValRat.self (by decide : 1 < 11)
  have h6 : padicValRat 11 (6 : ℚ) = 0 := valuation_nat_of_not_dvd (by decide : ¬ 11 ∣ 6)
  have hY : padicValRat 11 (11 / 6) = 1 := by
    rw [padicValRat.div (by norm_num) (by norm_num), h11, h6, sub_zero]
  norm_num [truncatedLogExceptionalPrimes, hp, hH, hY]

example : 13 ∉ truncatedLogExceptionalPrimes 3 := by
  norm_num [truncatedLogExceptionalPrimes]

-- Table 1's auxiliary-only witness. Clear denominators by 60 and show that the resulting
-- integer resultant is divisible by 101 (common root 87) but is nonzero (odd).
private lemma auxiliary_valuation_five : 0 < padicValRat 101 (truncatedLogAuxProduct 5) := by
  have : Fact (Nat.Prime 101) := ⟨by decide⟩
  let f : ℤ[X] := ∑ j ∈ Finset.range 5, X ^ j
  let g : ℤ[X] := C 12 + C 60 * X + C 30 * X ^ 2 + C 20 * X ^ 3 + C 15 * X ^ 4
  let z : ℤ := resultant f g 4 4
  have hf_map (K : Type) [CommRing K] : f.map (Int.castRingHom K) =
      ∑ j ∈ Finset.range 5, (X : K[X]) ^ j := by
    simp [f, Polynomial.map_sum]
  have hg_map (K : Type) [CommRing K] : g.map (Int.castRingHom K) =
      C 12 + C 60 * X + C 30 * X ^ 2 + C 20 * X ^ 3 + C 15 * X ^ 4 := by
    simp only [g, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, map_X,
      Int.coe_castRingHom, Int.cast_ofNat]
  have hf_le (K : Type) [CommRing K] : (f.map (Int.castRingHom K)).natDegree ≤ 4 := by
    rw [hf_map]
    apply natDegree_sum_le_of_forall_le
    intro j hj
    exact (natDegree_X_pow_le j).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  have hz₂ : (z : ZMod 2) = 1 := by
    have hf₀ : (f.map (Int.castRingHom (ZMod 2))).coeff 0 = 1 := by
      rw [hf_map]
      simp [Finset.sum_range_succ, coeff_X_pow]
    have hg₂ : g.map (Int.castRingHom (ZMod 2)) = X ^ 4 := by
      rw [hg_map]
      simp [show (12 : ZMod 2) = 0 by decide, show (60 : ZMod 2) = 0 by decide,
        show (30 : ZMod 2) = 0 by decide, show (20 : ZMod 2) = 0 by decide,
        show (15 : ZMod 2) = 1 by decide]
    change Int.castRingHom (ZMod 2) (resultant f g 4 4) = 1
    rw [← resultant_map_map, hg₂, resultant_X_pow_right _ 4 4 (hf_le _), hf₀]
    decide
  have hz_ne : z ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero] at hz₂
    exact (by decide : (0 : ZMod 2) ≠ 1) hz₂
  have hz_dvd : (101 : ℤ) ∣ z := by
    let f₁ := f.map (Int.castRingHom (ZMod 101))
    let g₁ := g.map (Int.castRingHom (ZMod 101))
    have hf₁ : f₁.eval 87 = 0 := by
      rw [show f₁ = f.map (Int.castRingHom (ZMod 101)) from rfl, hf_map]
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, eval_add,
        eval_zero, eval_pow, eval_X]
      decide
    have hg₁ : g₁.eval 87 = 0 := by
      rw [show g₁ = g.map (Int.castRingHom (ZMod 101)) from rfl, hg_map]
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
      decide
    have hg_le : g₁.natDegree ≤ 4 := by
      rw [show g₁ = g.map (Int.castRingHom (ZMod 101)) from rfl, hg_map]
      compute_degree!
    obtain ⟨u, v, -, -, he⟩ := exists_mul_add_mul_eq_C_resultant f₁ g₁
      (hf_le _) hg_le (Or.inl (by decide : 4 ≠ 0))
    have hz₁ : resultant f₁ g₁ 4 4 = 0 := by
      simpa [eval_add, eval_mul, hf₁, hg₁] using (congrArg (eval 87) he).symm
    have hcast : (z : ZMod 101) = 0 := by
      change Int.castRingHom (ZMod 101) (resultant f g 4 4) = 0
      rw [← resultant_map_map]
      exact hz₁
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 101).mp hcast
  let a : ℚ[X] := C ((5 : ℕ) : ℚ)⁻¹ + ∑ j ∈ Finset.Icc (1 : ℕ) (5 - 1), C ((j : ℚ)⁻¹) * X ^ j
  have ha : a = C (1 / 5) + X + C (1 / 2) * X ^ 2 + C (1 / 3) * X ^ 3 + C (1 / 4) * X ^ 4 := by
    norm_num [a, show (5 : ℕ) - 1 = 4 by decide,
      show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide, add_assoc]
  have ha_deg : a.natDegree = 4 := by rw [ha]; compute_degree!
  have hf_deg : (f.map (Int.castRingHom ℚ)).natDegree = 4 := by
    rw [hf_map]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
    compute_degree!
  have hgQ : g.map (Int.castRingHom ℚ) = C 60 * a := by
    rw [hg_map, ha]
    simp only [mul_add, ← mul_assoc, ← C_mul]
    norm_num
  have haux : truncatedLogAuxProduct 5 = resultant (f.map (Int.castRingHom ℚ)) a := by
    calc
      truncatedLogAuxProduct 5 = _ := rfl
      _ = _ := congrArg (fun p : ℚ[X] => resultant p a) (hf_map ℚ).symm
  have hzQ : (z : ℚ) = 60 ^ 4 * truncatedLogAuxProduct 5 := by
    change Int.castRingHom ℚ (resultant f g 4 4) = _
    rw [← resultant_map_map, hgQ, resultant_C_mul_right, haux, hf_deg, ha_deg]
  have haux_eq : truncatedLogAuxProduct 5 = (z : ℚ) / 60 ^ 4 :=
    (eq_div_iff (by norm_num)).2 (by rw [hzQ, mul_comm])
  have h60 : padicValRat 101 (60 : ℚ) = 0 := valuation_nat_of_not_dvd (by decide : ¬ 101 ∣ 60)
  have hpos : 0 < padicValInt 101 z :=
    ((padicValInt_dvd_iff 1 z).mp (by simpa using hz_dvd)).resolve_left hz_ne
  rw [haux_eq, padicValRat.div (by exact_mod_cast hz_ne) (by norm_num), padicValRat.pow,
    h60, mul_zero, sub_zero, padicValRat.of_int]
  exact_mod_cast hpos

example : 0 < padicValRat 101 (truncatedLogAuxProduct 5) ∧
    padicValRat 101 (harmonic 5) = 0 ∧ 101 ∈ truncatedLogExceptionalPrimes 5 := by
  have hp : Nat.Prime 101 := by decide
  have : Fact (Nat.Prime 101) := ⟨hp⟩
  have hH : harmonic 5 = 137 / 60 := by norm_num [harmonic_succ]
  have hY : padicValRat 101 (harmonic 5) = 0 := by
    rw [hH]
    exact valuation_fraction_of_not_dvd (q := 101) (a := 137) (b := 60) (by decide) (by decide)
  refine ⟨auxiliary_valuation_five, hY, ?_⟩
  norm_num [truncatedLogExceptionalPrimes, hp, auxiliary_valuation_five, hY]

-- The m = 1 auxiliary product is empty. Compute the residue for q = 5 independently
-- of the exceptional-prime criterion and use it to certify nonsquareness.
example : truncatedLogAuxProduct 1 = 1 := by norm_num [truncatedLogAuxProduct]

example : ¬ IsSquare (truncatedLogPolynomial 5).discr := by
  refine not_isSquare_discr_truncatedLog_mul_prime_of_resultant_ne_zero (m := 1) (q := 5)
    (by decide) (by decide) (by decide) ?_
  have : Fact (1 < (5 : ℕ)) := ⟨by decide⟩
  let f : (ZMod 5)[X] := ∑ j ∈ Finset.range 5, X ^ j
  have hlog : (∑ j ∈ Finset.Icc (1 : ℕ) 1, C ((j : ZMod 5)⁻¹) * X ^ j) = X := by simp
  have hf : f.natDegree = 4 := by
    simp only [f, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero, pow_one,
      zero_add]
    compute_degree!
  have h₀ : f.coeff 0 = 1 := by simp [f, Finset.sum_range_succ, coeff_X_pow]
  change resultant f (∑ j ∈ Finset.Icc (1 : ℕ) 1, C ((j : ZMod 5)⁻¹) * X ^ j) ≠ 0
  have hr : resultant f X 4 1 = 1 := by
    have h := resultant_X_pow_right f 4 1 hf.le
    rw [pow_one (X : (ZMod 5)[X]), Nat.mul_one, pow_one, h₀, mul_one] at h
    exact h.trans (by decide)
  rw [hlog, hf, natDegree_X, hr]
  exact one_ne_zero

-- Client example at a composite degree.
example : ¬ IsSquare (truncatedLogPolynomial 21).discr :=
  not_isSquare_discr_truncatedLog_mul_prime (m := 3) (q := 7)
    (by decide) seven_not_exceptional_three (by decide) (by decide)

end MathlibExtTest.NumberTheory.TruncatedLogDiscriminantFinitePrimesIsSquareDiscrTruncatedLog
