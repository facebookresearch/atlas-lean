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
# Triangular normalization scalars

The recursively defined exponent `a_0=0`, `a_(n+1)=a_n+n+1`
is `n(n+1)/2`. The associated sign `σ_n=(-1)^a_n` is
self-inverse and gives a scalar automorphism of every object of
a preadditive category.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Preadditive
namespace CategoryTheory.ProjectiveResolution

/- Proof implementation note.
The exponent obtained by summing the original kernel-tail cross exponents.
-/

/-- The normalization exponent is the natural-number sequence
`a_0=0`, `a_(n+1)=a_n+n+1`, namely the sum of the
integers from one through `n`. -/
def acyclicResolutionNormalizationExponent : ℕ → ℕ
  | 0 => 0
  | n + 1 => acyclicResolutionNormalizationExponent n + n + 1

/- Proof implementation note.
Twice the forced exponent is the literal triangular product.
-/

/-- For each `n ∈ ℕ`, the normalization exponent defined by
`a₀=0` and `a_(n+1)=a_n+n+1` satisfies `2a_n = n(n+1)`. -/
theorem acyclicResolutionNormalizationExponent_two_mul (n : ℕ) :
    2 * acyclicResolutionNormalizationExponent n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [acyclicResolutionNormalizationExponent]
      nlinarith

/- Proof implementation note.
The original accumulated exponent is n(n+1)/2.
-/

/-- For each `n ∈ ℕ`, the recursively defined exponent
`a_0=0`, `a_(n+1)=a_n+n+1` has the closed formula
`a_n = n(n+1)/2`. -/
theorem acyclicResolutionNormalizationExponent_eq (n : ℕ) :
    acyclicResolutionNormalizationExponent n = n * (n + 1) / 2 := by
  have h := acyclicResolutionNormalizationExponent_two_mul n
  omega

/- Proof implementation note.
The recursively proved normalization sign is the triangular sign.
-/

/-- For each `n ∈ ℕ`, the integer scalar of the acyclic-resolution
normalization is the triangular sign
`σ_n = (-1)^(n(n+1)/2)`. -/
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

/- Proof implementation note.
The original normalization scalar is its own inverse.
-/

/-- For each `n ∈ ℕ`, the integer normalization scalar
`σ_n=(-1)^(n(n+1)/2)` satisfies `σ_n²=1`; it is its
own multiplicative inverse. -/
theorem acyclicResolutionNormalizationSign_mul_self (n : ℕ) :
    acyclicResolutionNormalizationSign n * acyclicResolutionNormalizationSign n = 1 := by
  rw [acyclicResolutionNormalizationSign_closed, ← mul_pow]
  norm_num

/- Proof implementation note.
The canonical original scalar correction on any object in a preadditive category.
-/

/-- For an object `X` of a preadditive category `C` and `n ∈ ℕ`,
the normalization sign `σ_n=(-1)^(n(n+1)/2)` defines an
automorphism of `X`. Both its forward and inverse morphisms
are `σ_n • 𝟙 X`. -/
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
