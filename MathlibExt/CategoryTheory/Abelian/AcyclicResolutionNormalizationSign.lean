/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolutionSignedNormalization
public import Mathlib.Tactic.Linarith

/-!
## # The forced triangular sign and its canonical scalar correction
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution

/-- The exponent obtained by summing the original kernel-tail cross exponents. -/
def acyclicResolutionNormalizationExponent : ℕ → ℕ
  | 0 => 0
  | n + 1 => acyclicResolutionNormalizationExponent n + n + 1

/-- Twice the forced exponent is the literal triangular product. -/
theorem acyclicResolutionNormalizationExponent_two_mul (n : ℕ) :
    2 * acyclicResolutionNormalizationExponent n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [acyclicResolutionNormalizationExponent]
      nlinarith

/-- The original accumulated exponent is n(n+1)/2. -/
theorem acyclicResolutionNormalizationExponent_eq (n : ℕ) :
    acyclicResolutionNormalizationExponent n = n * (n + 1) / 2 := by
  have h := acyclicResolutionNormalizationExponent_two_mul n
  omega

/-- The recursively proved normalization sign is the triangular sign. -/
theorem acyclicResolutionNormalizationSign_closed (n : ℕ) :
    acyclicResolutionNormalizationSign n = (-1 : ℤ) ^ (n * (n + 1) / 2) := by
  have h : acyclicResolutionNormalizationSign n =
      (-1 : ℤ) ^ acyclicResolutionNormalizationExponent n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [acyclicResolutionNormalizationSign, normalizationCrossSign, ih,
          acyclicResolutionNormalizationExponent]
        rw [show acyclicResolutionNormalizationExponent n + n + 1 =
          (n + 1) + acyclicResolutionNormalizationExponent n from by omega]
        simp only [pow_add, mul_assoc]
  rw [acyclicResolutionNormalizationExponent_eq] at h
  exact h

/-- The original normalization scalar is its own inverse. -/
theorem acyclicResolutionNormalizationSign_mul_self (n : ℕ) :
    acyclicResolutionNormalizationSign n * acyclicResolutionNormalizationSign n = 1 := by
  rw [acyclicResolutionNormalizationSign_closed, ← mul_pow]
  norm_num

/-- The canonical original scalar correction on any object in a preadditive category. -/
def acyclicResolutionNormalizationIso {C : Type u} [Category.{v} C] [Preadditive C]
    (X : C) (n : ℕ) : X ≅ X where
  hom := acyclicResolutionNormalizationSign n • 𝟙 X
  inv := acyclicResolutionNormalizationSign n • 𝟙 X
  hom_inv_id := by
    rw [zsmul_comp, comp_zsmul, Category.id_comp, smul_smul,
      acyclicResolutionNormalizationSign_mul_self, one_zsmul]
  inv_hom_id := by
    rw [zsmul_comp, comp_zsmul, Category.id_comp, smul_smul,
      acyclicResolutionNormalizationSign_mul_self, one_zsmul]

end CategoryTheory.ProjectiveResolution
