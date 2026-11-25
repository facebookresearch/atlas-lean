/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.KummerCharacter
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

open NumberField.LevelArith Polynomial

/-- Exact-source consumer, with the original binders: the Kummer
exponent describes the Galois action on the chosen root. -/
example (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : (↥F)ˣ)
    (σ : ↥F.fixingSubgroup) :
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) =
      ζ ^ (kummerExp p ζ hζ F x σ).val * kummerRoot p F x :=
  kummerExp_spec p ζ hζ F x σ

/-- Characterization consumer: the chosen root of the identity unit is
a `p`-th root of unity. -/
example (p : ℕ) [Fact p.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    kummerRoot p F 1 ^ p = 1 := by
  rw [kummerRoot_pow]
  simp

/-- Nontrivial instance: the identity automorphism has trivial Kummer
exponent, for every unit and every prime. -/
example (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : (↥F)ˣ) :
    ζ ^ (kummerExp p ζ hζ F x 1).val = 1 := by
  have h := kummerExp_spec p ζ hζ F x (1 : ↥F.fixingSubgroup)
  simp only [Subgroup.coe_one, AlgEquiv.one_apply] at h
  exact (mul_eq_right₀ (kummerRoot_ne_zero p F x)).mp h.symm

/-- Character consumer: when `ζ ∈ F`, the Kummer exponent is additive in
`σ`, and the Kummer character describes the Galois action on the chosen
root. -/
example (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F)
    (x : (↥F)ˣ) (σ τ : ↥F.fixingSubgroup) :
    kummerExp p ζ hζ F x (σ * τ) =
        kummerExp p ζ hζ F x σ + kummerExp p ζ hζ F x τ ∧
      (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) =
        ζ ^ (Multiplicative.toAdd (kummerChar p ζ hζ F hζF x σ)).val *
          kummerRoot p F x :=
  ⟨congrArg Multiplicative.toAdd (map_mul (kummerChar p ζ hζ F hζF x) σ τ),
    kummerChar_spec p ζ hζ F hζF x σ⟩

/-- Concrete instance of the hypothesis: the cyclotomic field `ℚ(ζ)`
contains `ζ`, so its Kummer exponents are additive. -/
example (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ p) (x : (↥(IntermediateField.adjoin ℚ {ζ}))ˣ)
    (σ τ : ↥(IntermediateField.adjoin ℚ {ζ}).fixingSubgroup) :
    kummerExp p ζ hζ _ x (σ * τ) =
      kummerExp p ζ hζ _ x σ + kummerExp p ζ hζ _ x τ :=
  congrArg Multiplicative.toAdd (map_mul (kummerChar p ζ hζ _
    (IntermediateField.mem_adjoin_simple_self ℚ ζ) x) σ τ)

/-- `2` is not the cube of a rational number. -/
private theorem kummerTest_cube_ne_two (b : ℚ) : b ^ 3 ≠ 2 := by
  intro h
  have h2 := congrArg (padicValRat 2) h
  rw [padicValRat.pow, show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num,
    padicValRat.self (by norm_num)] at h2
  omega

/-- The boundary below is not vacuous: `AlgebraicClosure ℚ` has a
primitive cube root of unity. -/
example : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ 3 :=
  HasEnoughRootsOfUnity.prim

/-- Boundary: without `ζ ∈ F` the Kummer exponent is not a character.
Over `F = ℚ` (the bottom intermediate field), with `p = 3` and `x = 2`,
`ζ ∉ F`, and an automorphism `σ` with `σ ζ = ζ ^ 2` and one `τ` moving
the cube root of `2` break additivity, as the twisted law
`kummerExp_mul` predicts. -/
example (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ 3) :
    ζ ∉ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) ∧
      ∃ (x : (↥(⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)))ˣ)
        (σ τ : ↥(⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)).fixingSubgroup),
        kummerExp 3 ζ hζ ⊥ x (σ * τ) ≠
          kummerExp 3 ζ hζ ⊥ x σ + kummerExp 3 ζ hζ ⊥ x τ := by
  have hmem : ∀ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      g ∈ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)).fixingSubgroup :=
    fun g => by
      rw [IntermediateField.fixingSubgroup_bot]
      exact Subgroup.mem_top g
  -- An automorphism `σ₀` with `σ₀ ζ = ζ ^ 2`.
  have hζ2 : minpoly ℚ (ζ ^ 2) = minpoly ℚ ζ :=
    (cyclotomic_eq_minpoly_rat (hζ.pow_of_coprime 2 (by norm_num))
      (by norm_num)).symm.trans (cyclotomic_eq_minpoly_rat hζ (by norm_num))
  obtain ⟨σ₀, hσ₀⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure ℚ)).mp hζ2)
  rw [AlgEquiv.smul_def] at hσ₀
  -- The unit `2` and its chosen cube root.
  let x : (↥(⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)))ˣ :=
    Units.mk0 2 two_ne_zero
  have hα : kummerRoot 3 ⊥ x ^ 3 = 2 := by
    rw [kummerRoot_pow]
    rfl
  -- An automorphism `τ₀` with `τ₀ α = ζ * α`, where `α ^ 3 = 2`.
  have hminpoly (y : AlgebraicClosure ℚ) (hy : y ^ 3 = 2) :
      minpoly ℚ y = X ^ 3 - C 2 :=
    (minpoly.eq_of_irreducible_of_monic
      (irreducible_X_pow_sub_C_of_prime Nat.prime_three kummerTest_cube_ne_two)
      (by simp [hy]) (monic_X_pow_sub_C 2 (by norm_num))).symm
  have hζα : (ζ * kummerRoot 3 ⊥ x) ^ 3 = 2 := by
    rw [mul_pow, hζ.pow_eq_one, one_mul, hα]
  obtain ⟨τ₀, hτ₀⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure ℚ)).mp
      ((hminpoly _ hζα).trans (hminpoly _ hα).symm))
  rw [AlgEquiv.smul_def] at hτ₀
  refine ⟨fun hζB => ?_, x, ⟨σ₀, hmem σ₀⟩, ⟨τ₀, hmem τ₀⟩, fun hadd => ?_⟩
  · -- `σ₀` fixes `ℚ` but moves `ζ`.
    have hfix :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hmem σ₀) ζ hζB
    rw [hσ₀] at hfix
    have h21 := hζ.pow_inj (by norm_num) (by norm_num)
      (hfix.trans (pow_one ζ).symm)
    omega
  · -- The twisted law with `k = 2` forces `kummerExp τ = 0`, so `τ₀ α = α`.
    have htw := kummerExp_mul 3 ζ hζ ⊥ x ⟨σ₀, hmem σ₀⟩ ⟨τ₀, hmem τ₀⟩ hσ₀
    push_cast at htw
    have hτ : kummerExp 3 ζ hζ ⊥ x ⟨τ₀, hmem τ₀⟩ = 0 := by
      linear_combination hadd - htw
    have hspec := kummerExp_spec 3 ζ hζ ⊥ x ⟨τ₀, hmem τ₀⟩
    rw [hτ, ZMod.val_zero, pow_zero, one_mul] at hspec
    exact hζ.ne_one (by norm_num)
      ((mul_eq_right₀ (kummerRoot_ne_zero 3 ⊥ x)).mp (hτ₀.symm.trans hspec))
