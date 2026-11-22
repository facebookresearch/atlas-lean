/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
The two source statement types, not their proof bodies, are reproduced from:

anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2:
Theorems/Thm_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply.lean
Theorems/Thm_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime.lean
Copyright 2026 Anthropic, PBC.
Licensed under Apache 2.0, https://www.apache.org/licenses/LICENSE-2.0.
The source names no individual authors for these statements.
-/
module

public import MathlibExt.FieldTheory.BinomialIrreducibility
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.Algebra.Field.ZMod

/-!
# Integer-character binomial applications and sharp boundaries

The two source-shaped consumers below use the exact statement types from
anthropics/fermats-last-theorem at
6e837e75355538c7f80bab5b956861e86c4eacc2, entry295, the wrappers
Thm_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply.lean and
Thm_Polynomial_irreducible_X_pow_sub_C_of_monoidHom_units_coprime.lean.
They call the new public API, not the source proofs. All application and
boundary proofs in this file are independently authored.
-/

public section

universe u

namespace BinomialIrreducibilityTest

open Polynomial

/-- The full function source contract, including its arbitrary universe. -/
theorem function_source {F : Type*} [Field F] (v : F → ℤ)
    (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {a : F} (ha : a ≠ 0)
    (hcop : IsCoprime (v a) n) : Irreducible (X ^ n - C a) :=
  irreducible_X_pow_sub_C_of_integerCharacter v hv hn ha hcop

/-- The full unit-hom source contract at its explicit universe `u`. -/
theorem unit_source {K : Type u} [Field K] {N : ℕ} (hN : 0 < N)
    {β : K} (hβ : β ≠ 0) (φ : Kˣ →* Multiplicative ℤ)
    (hφ : (Multiplicative.toAdd (φ (Units.mk0 β hβ))).natAbs.Coprime N) :
    Irreducible (X ^ N - C β) :=
  irreducible_X_pow_sub_C_of_unitHom hN hβ φ hφ

/-- The exact integer/natural coprimality bridge, including negative values. -/
theorem coprimality_bridge (z : ℤ) (n : ℕ) :
    IsCoprime z (n : ℤ) ↔ z.natAbs.Coprime n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_def, Int.natAbs_natCast]

/-- Composite even exponent over the rationals. -/
theorem rational_six_two : Irreducible (X ^ 6 - C (2 : ℚ)) := by
  apply irreducible_X_pow_sub_C_of_integerCharacter (padicValRat 2)
    (fun _ _ hx hy => padicValRat.mul hx hy) (by decide) (by norm_num)
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by decide)
  rw [h2, coprimality_bridge]
  decide

/-- The quotient is a field of the claimed degree, not just a vector space. -/
private theorem binomial_extension {F : Type*} [Field F] {n : ℕ} {a : F}
    (h : Irreducible (X ^ n - C a)) :
    IsField (AdjoinRoot (X ^ n - C a)) ∧
      Module.finrank F (AdjoinRoot (X ^ n - C a)) = n := by
  refine ⟨AdjoinRoot.isField_iff_irreducible.mpr h, ?_⟩
  rw [(AdjoinRoot.powerBasis h.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim h.ne_zero, natDegree_X_pow_sub_C]

/-- The sixth-root-of-two field has degree six. -/
theorem rational_six_two_extension :
    IsField (AdjoinRoot (X ^ 6 - C (2 : ℚ))) ∧
      Module.finrank ℚ (AdjoinRoot (X ^ 6 - C (2 : ℚ))) = 6 :=
  binomial_extension rational_six_two

/-- Negative character value: a sixth root of one half. -/
theorem rational_six_half : Irreducible (X ^ 6 - C (1 / 2 : ℚ)) := by
  apply irreducible_X_pow_sub_C_of_integerCharacter (padicValRat 2)
    (fun _ _ hx hy => padicValRat.mul hx hy) (by decide) (by norm_num)
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by decide)
  rw [one_div, padicValRat.inv, h2, coprimality_bridge]
  decide

/-- The negative character value still gives extension degree six. -/
theorem rational_six_half_extension :
    IsField (AdjoinRoot (X ^ 6 - C (1 / 2 : ℚ))) ∧
      Module.finrank ℚ (AdjoinRoot (X ^ 6 - C (1 / 2 : ℚ))) = 6 :=
  binomial_extension rational_six_half

/-- A coprime character value other than `1` or `-1`. -/
theorem rational_three_four : Irreducible (X ^ 3 - C (4 : ℚ)) := by
  apply irreducible_X_pow_sub_C_of_integerCharacter (padicValRat 2)
    (fun _ _ hx hy => padicValRat.mul hx hy) (by decide) (by norm_num)
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by decide)
  rw [show (4 : ℚ) = 2 ^ 2 by norm_num, padicValRat.pow, h2,
    coprimality_bridge]
  decide

/-- The cube-root-of-four field has degree three. -/
theorem rational_three_four_extension :
    IsField (AdjoinRoot (X ^ 3 - C (4 : ℚ))) ∧
      Module.finrank ℚ (AdjoinRoot (X ^ 3 - C (4 : ℚ))) = 3 :=
  binomial_extension rational_three_four

/-- The canonical rational function field has characteristic two. -/
theorem ratFunc_characteristic : CharP (RatFunc (ZMod 2)) 2 := inferInstance

/-- Every positive radical exponent works over this characteristic-two field. -/
theorem ratFunc_binomial (n : ℕ) (hn : 0 < n) :
    Irreducible (X ^ n - C (RatFunc.X : RatFunc (ZMod 2))) := by
  apply irreducible_X_pow_sub_C_of_integerCharacter
    (K := RatFunc (ZMod 2)) (RatFunc.intDegree (K := ZMod 2))
    (fun x y hx hy => RatFunc.intDegree_mul (x := x) (y := y) hx hy)
    hn RatFunc.X_ne_zero
  rw [RatFunc.intDegree_X]
  exact isCoprime_one_left

/-- A genuine quadratic function-field extension in characteristic two. -/
theorem ratFunc_two_extension :
    IsField (AdjoinRoot (X ^ 2 - C (RatFunc.X : RatFunc (ZMod 2)))) ∧
      Module.finrank (RatFunc (ZMod 2))
        (AdjoinRoot (X ^ 2 - C (RatFunc.X : RatFunc (ZMod 2)))) = 2 :=
  binomial_extension (ratFunc_binomial 2 (by decide))

/-- Composite even degree also works in characteristic two. -/
theorem ratFunc_six_extension :
    IsField (AdjoinRoot (X ^ 6 - C (RatFunc.X : RatFunc (ZMod 2)))) ∧
      Module.finrank (RatFunc (ZMod 2))
        (AdjoinRoot (X ^ 6 - C (RatFunc.X : RatFunc (ZMod 2)))) = 6 :=
  binomial_extension (ratFunc_binomial 6 (by decide))

/-- Even binomials have zero derivative, including exponents two and six. -/
theorem ratFunc_even_derivative (n : ℕ) :
    derivative (X ^ (2 * n) - C (RatFunc.X : RatFunc (ZMod 2))) = 0 := by
  have h2 : (2 : RatFunc (ZMod 2)) = 0 := by
    simpa using CharP.cast_eq_zero (RatFunc (ZMod 2)) 2
  simp [derivative_X_pow, Nat.cast_mul, h2]

/-- Irreducibility does not imply separability in these examples. -/
theorem ratFunc_even_inseparable (n : ℕ) (hn : 0 < n) :
    ¬ (X ^ (2 * n) - C (RatFunc.X : RatFunc (ZMod 2))).Separable := by
  intro h
  exact (separable_iff_derivative_ne_zero
    (ratFunc_binomial (2 * n) (Nat.mul_pos (by decide) hn))).mp h
      (ratFunc_even_derivative n)

/-- The adjoined generator is inseparable, not merely its presentation. -/
theorem ratFunc_even_root_inseparable (n : ℕ) (hn : 0 < n) :
    ¬ IsSeparable (RatFunc (ZMod 2))
      (AdjoinRoot.root (X ^ (2 * n) - C (RatFunc.X : RatFunc (ZMod 2)))) := by
  have hm := monic_X_pow_sub_C (RatFunc.X : RatFunc (ZMod 2))
    (n := 2 * n) (Nat.ne_of_gt (Nat.mul_pos (by decide) hn))
  change ¬ (minpoly (RatFunc (ZMod 2)) (AdjoinRoot.root _)).Separable
  rw [AdjoinRoot.minpoly_root hm.ne_zero, hm.leadingCoeff, inv_one,
    map_one, mul_one]
  exact ratFunc_even_inseparable n hn

/-- This sum of two valuations is a multiplicative-additive character. -/
theorem sum_character_mul (x y : ℚ) (hx : x ≠ 0) (hy : y ≠ 0) :
    padicValRat 2 (x * y) + padicValRat 3 (x * y) =
      (padicValRat 2 x + padicValRat 3 x) +
        (padicValRat 2 y + padicValRat 3 y) := by
  rw [padicValRat.mul hx hy, padicValRat.mul hx hy]
  omega

private theorem padic_rat_nat_not_dvd (p n : ℕ) (h : ¬ p ∣ n) :
    padicValRat p (n : ℚ) = 0 := by
  rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd h, Nat.cast_zero]

/-- Exact witnesses that separate characters from ultrametric valuations. -/
theorem sum_character_values :
    let v := fun q : ℚ => padicValRat 2 q + padicValRat 3 q
    v 2 = 1 ∧ v 3 = 1 ∧ v 5 = 0 := by
  have h22 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by decide)
  have h33 : padicValRat 3 (3 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 3) (by decide)
  have h32 : padicValRat 3 (2 : ℚ) = 0 := by
    simpa using padic_rat_nat_not_dvd 3 2 (by decide)
  have h23 : padicValRat 2 (3 : ℚ) = 0 := by
    simpa using padic_rat_nat_not_dvd 2 3 (by decide)
  have h25 : padicValRat 2 (5 : ℚ) = 0 := by
    simpa using padic_rat_nat_not_dvd 2 5 (by decide)
  have h35 : padicValRat 3 (5 : ℚ) = 0 := by
    simpa using padic_rat_nat_not_dvd 3 5 (by decide)
  simp only [h22, h33, h32, h23, h25, h35, zero_add, add_zero, and_self]

/-- The valuation inequality fails on the nonzero inputs `2`, `3`, and `5`. -/
theorem sum_character_not_ultrametric :
    let v := fun q : ℚ => padicValRat 2 q + padicValRat 3 q
    ¬ ∀ x y : ℚ, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (v x) (v y) ≤ v (x + y) := by
  dsimp only
  intro h
  have h23 := h 2 3 (by norm_num) (by norm_num) (by norm_num)
  rcases sum_character_values with ⟨h2, h3, h5⟩
  dsimp only at h2 h3 h5
  rw [show (2 : ℚ) + 3 = 5 by norm_num, h2, h3, h5] at h23
  norm_num at h23

/-- The genuinely non-ultrametric character is still accepted by the API. -/
theorem sum_character_application : Irreducible (X ^ 6 - C (2 : ℚ)) := by
  apply irreducible_X_pow_sub_C_of_integerCharacter
    (fun q => padicValRat 2 q + padicValRat 3 q) sum_character_mul
    (by decide) (by norm_num)
  have h2 : padicValRat 2 (2 : ℚ) + padicValRat 3 (2 : ℚ) = 1 :=
    sum_character_values.1
  rw [h2, coprimality_bridge]
  decide

/-- The positive-exponent contract includes one and the trivial character. -/
theorem exponent_one {K : Type*} [Field K] {a : K} (ha : a ≠ 0) :
    Irreducible (X ^ 1 - C a) := by
  apply irreducible_X_pow_sub_C_of_integerCharacter (fun _ => 0)
    (fun _ _ _ _ => rfl) (by decide) ha
  exact isCoprime_one_right

/-- Without positivity, coprimality can leave a unit polynomial. -/
theorem exponent_zero_counterexample :
    IsCoprime (padicValRat 2 (2 : ℚ)) (0 : ℤ) ∧
      IsUnit (X ^ 0 - C (2 : ℚ)) ∧
        ¬ Irreducible (X ^ 0 - C (2 : ℚ)) := by
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by decide)
  have heq : (X ^ 0 - C (2 : ℚ)) = (-1 : ℚ[X]) := by
    norm_num [C_ofNat]
  have hu : IsUnit (X ^ 0 - C (2 : ℚ)) := by
    rw [heq]
    exact isUnit_one.neg
  refine ⟨?_, hu, fun hi => hi.not_isUnit hu⟩
  rw [h2]
  exact isCoprime_one_left

/-- Arbitrary value at zero makes the nonzero-coefficient premise essential. -/
theorem zero_coefficient_counterexample :
    let v := fun x : ℚ => if x = 0 then (1 : ℤ) else 0
    (∀ x y : ℚ, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y) ∧
      IsCoprime (v 0) (2 : ℤ) ∧
        ¬ Irreducible (X ^ 2 - C (0 : ℚ)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    simp [hx, hy, mul_ne_zero hx hy]
  · simpa only [ite_true] using (isCoprime_one_left (x := (2 : ℤ)))
  · rw [map_zero, sub_zero]
    exact not_irreducible_pow (by decide)

/-- Omitting coprimality permits an explicit product of two nonunits. -/
theorem missing_coprimality_counterexample :
    ¬ IsCoprime (padicValRat 2 (4 : ℚ)) (2 : ℤ) ∧
      X ^ 2 - C (4 : ℚ) = (X - C 2) * (X + C 2) ∧
        ¬ Irreducible (X ^ 2 - C (4 : ℚ)) := by
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by decide)
  have hf : X ^ 2 - C (4 : ℚ) = (X - C 2) * (X + C 2) := by
    simp only [C_ofNat]
    ring
  refine ⟨?_, hf, ?_⟩
  · rw [show (4 : ℚ) = 2 ^ 2 by norm_num, padicValRat.pow, h2]
    norm_num [Int.isCoprime_iff_gcd_eq_one]
  · intro hi
    rcases hi.isUnit_or_isUnit hf with hl | hr
    · exact (irreducible_X_sub_C (2 : ℚ)).not_isUnit hl
    · exact (not_isUnit_of_natDegree_pos (X + C (2 : ℚ)) (by simp)) hr

/-- A unit character extends with any chosen integer at zero. -/
theorem unit_character_extension {K : Type u} [Field K]
    (φ : Kˣ →* Multiplicative ℤ) (z : ℤ) :
    ∃ v : K → ℤ, v 0 = z ∧
      (∀ x y : K, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y) ∧
      ∀ (x : K) (hx : x ≠ 0),
        v x = Multiplicative.toAdd (φ (Units.mk0 x hx)) := by
  classical
  let v := fun x : K => if hx : x = 0 then z else
    Multiplicative.toAdd (φ (Units.mk0 x hx))
  refine ⟨v, ?_, ?_, ?_⟩
  · simp [v]
  · intro x y hx hy
    have hu : Units.mk0 (x * y) (mul_ne_zero hx hy) =
        Units.mk0 x hx * Units.mk0 y hy := Units.ext rfl
    simp only [v, dite_eq_right hx, dite_eq_right hy,
      dite_eq_right (mul_ne_zero hx hy)]
    rw [hu, map_mul]
    rfl
  · intro x hx
    simp only [v, dite_eq_right hx]

end BinomialIrreducibilityTest
