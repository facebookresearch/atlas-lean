/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Galois.KummerCharacter

open NumberField.LevelArith

/-- Exact-source consumer, with the original binders: the Kummer
character describes the Galois action on the chosen root. -/
example (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : (↥F)ˣ)
    (σ : ↥F.fixingSubgroup) :
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) =
      ζ ^ (kummerChar p ζ hζ F x σ).val * kummerRoot p F x :=
  kummerChar_spec p ζ hζ F x σ

/-- Characterization consumer: the chosen root of the identity unit is
a `p`-th root of unity. -/
example (p : ℕ) [Fact p.Prime]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    kummerRoot p F 1 ^ p = 1 := by
  rw [kummerRoot_pow]
  simp

/-- Nontrivial instance: the identity automorphism has trivial Kummer
character, for every unit and every prime. -/
example (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ)
    (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (x : (↥F)ˣ) :
    ζ ^ (kummerChar p ζ hζ F x 1).val = 1 := by
  have h := kummerChar_spec p ζ hζ F x (1 : ↥F.fixingSubgroup)
  simp only [Subgroup.coe_one, AlgEquiv.one_apply] at h
  exact (mul_eq_right₀ (kummerRoot_ne_zero p F x)).mp h.symm
