/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.FieldTensorTorComparison
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Field tensor Tor clients with nilpotent and infinite-dimensional coefficients

The coefficients are actual square-zero extensions. One contains the polynomial
module and is infinite-dimensional over the original field. Both middle-ring
actions kill the polynomial variable and are proved nonflat. The comparisons
still accept every native Tor degree and arbitrary common module universes.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct ModuleCat.UniverseTensor
open ModuleCat.UniverseTensor

namespace FieldTensorTorComparisonTests

/-- The original rational square-zero extension by the polynomial module. -/
abbrev LargeCoefficient := TrivSqZeroExt ℚ (Polynomial ℚ)
/-- The original rational square-zero extension by the rational module. -/
abbrev SmallCoefficient := TrivSqZeroExt ℚ ℚ

/-- The nonzero square-zero polynomial-coordinate coefficient. -/
def epsilon : LargeCoefficient := TrivSqZeroExt.inr 1
/-- The nonzero square-zero rational-coordinate coefficient. -/
def eta : SmallCoefficient := TrivSqZeroExt.inr 1

theorem epsilon_ne_zero : epsilon ≠ 0 := by
  intro h
  have h' := congrArg (TrivSqZeroExt.snd : LargeCoefficient → Polynomial ℚ) h
  simp [epsilon] at h'

theorem epsilon_mul_epsilon : epsilon * epsilon = 0 :=
  TrivSqZeroExt.inr_mul_inr ℚ 1 1

theorem eta_ne_zero : eta ≠ 0 := by
  intro h
  have h' := congrArg (TrivSqZeroExt.snd : SmallCoefficient → ℚ) h
  simp [eta] at h'

theorem eta_mul_eta : eta * eta = 0 :=
  TrivSqZeroExt.inr_mul_inr ℚ 1 1

theorem largeCoefficient_not_finite : ¬ Module.Finite ℚ LargeCoefficient := by
  intro h
  let : Module.Finite ℚ LargeCoefficient := h
  let : Module.Finite ℚ (Polynomial ℚ) := Module.Finite.of_surjective
    (TrivSqZeroExt.sndHom ℚ (Polynomial ℚ))
    (fun p => ⟨TrivSqZeroExt.inr p, rfl⟩)
  exact (Module.Finite.not_linearIndependent_of_infinite
    (R := ℚ) (Polynomial.basisMonomials ℚ : ℕ → Polynomial ℚ))
      (Polynomial.basisMonomials ℚ).linearIndependent

/-- Actual polynomial evaluation at zero in the large coefficient algebra. -/
def largeSupport : Polynomial ℚ →ₐ[ℚ] LargeCoefficient := Polynomial.aeval 0
/-- Actual polynomial evaluation at zero in the small coefficient algebra. -/
def smallSupport : Polynomial ℚ →ₐ[ℚ] SmallCoefficient := Polynomial.aeval 0

/-- The original left support map combines rational scalars and polynomial evaluation. -/
def leftSupport : ℚ ⊗[ℚ] Polynomial ℚ →ₐ[ℚ] LargeCoefficient :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ LargeCoefficient) largeSupport
    (fun _ _ => Commute.all _ _)

/-- The original right support map combines polynomial evaluation and rational scalars. -/
def rightSupport : Polynomial ℚ ⊗[ℚ] ℚ →ₐ[ℚ] SmallCoefficient :=
  Algebra.TensorProduct.lift smallSupport (Algebra.ofId ℚ SmallCoefficient)
    (fun _ _ => Commute.all _ _)

/-- The actual original middle-ring action map obtained from the left support. -/
abbrev actualLargeSupport := originalMiddleLeftMap ℚ ℚ (Polynomial ℚ) LargeCoefficient leftSupport
/-- The actual original middle-ring action map obtained from the right support. -/
abbrev actualSmallSupport := originalMiddleRightMap ℚ (Polynomial ℚ) ℚ SmallCoefficient rightSupport

theorem actualLargeSupport_X : actualLargeSupport Polynomial.X = 0 := by
  change (Algebra.ofId ℚ LargeCoefficient) 1 * largeSupport Polynomial.X = 0
  simp [largeSupport]

theorem actualSmallSupport_X : actualSmallSupport Polynomial.X = 0 := by
  change smallSupport Polynomial.X * (Algebra.ofId ℚ SmallCoefficient) 1 = 0
  simp [smallSupport]

private theorem not_flat_of_X_zero (D : Type*) [CommRing D] [Nontrivial D] [Algebra ℚ D]
    (f : Polynomial ℚ →ₐ[ℚ] D) (hf : f Polynomial.X = 0) :
    letI : Algebra (Polynomial ℚ) D := f.toRingHom.toAlgebra
    ¬ Module.Flat (Polynomial ℚ) D := by
  let : Algebra (Polynomial ℚ) D := f.toRingHom.toAlgebra
  intro h
  let : Module.Flat (Polynomial ℚ) D := h
  have hi : Function.Injective (fun d : D => (Polynomial.X : Polynomial ℚ) • d) :=
    Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero Polynomial.X_ne_zero)
  have hz : (Polynomial.X : Polynomial ℚ) • (1 : D) = 0 := by
    change f Polynomial.X * 1 = 0
    rw [hf, zero_mul]
  exact one_ne_zero (hi (hz.trans (smul_zero (Polynomial.X : Polynomial ℚ)).symm))

theorem largeCoefficient_not_flat :
    letI : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
    ¬ Module.Flat (Polynomial ℚ) LargeCoefficient :=
  not_flat_of_X_zero LargeCoefficient actualLargeSupport actualLargeSupport_X

theorem smallCoefficient_not_flat :
    letI : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
    ¬ Module.Flat (Polynomial ℚ) SmallCoefficient :=
  not_flat_of_X_zero SmallCoefficient actualSmallSupport actualSmallSupport_X

universe m

/-- Original standard ambient native Tor at degree q in an arbitrary module universe. -/
abbrev StandardTor (q : ℕ) :=
  originalStandardAmbientTorModule.{0,0,0,0,0,0,m}
    ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q

/-- Original intrinsic graph ambient native Tor for the same two actual support maps. -/
abbrev IntrinsicTor (q : ℕ) :=
  originalIntrinsicAmbientTorModule.{0,0,0,0,m}
    ℚ (Polynomial ℚ) LargeCoefficient SmallCoefficient actualLargeSupport actualSmallSupport q

/-- This client applies the actual field-only equivalence at every degree,
with module carriers larger than the original ring carriers permitted. -/
def nilpotentComparison (q : ℕ) :=
  fieldTensorAmbientTorEquiv.{0,0,0,0,0,0,m}
    ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q

/-- An explicit positive-degree native comparison of the nonflat nilpotent
coefficients, keeping the common module universe arbitrary. -/
def nilpotentDegreeOneComparison := nilpotentComparison.{m} 1

theorem standard_nilpotent_pure_action (q : ℕ) (z : StandardTor.{m} q) :
    letI : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
    letI : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
    letI : Module (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) (StandardTor.{m} q) :=
      originalStandardAmbientTensorModule.{0,0,0,0,0,0,m}
        ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q
    (epsilon ⊗ₜ[Polynomial ℚ] eta) • z =
      originalStandardAmbientLeftOperator.{0,0,0,0,0,0,m}
        ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q epsilon
          (originalStandardAmbientRightOperator.{0,0,0,0,0,0,m}
            ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q eta z) :=
  originalStandardAmbientTensorModule_tmul.{0,0,0,0,0,0,m}
    ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q epsilon eta z

theorem intrinsic_nilpotent_pure_action (q : ℕ) (z : IntrinsicTor.{m} q) :
    letI : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
    letI : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
    letI : Module (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) (IntrinsicTor.{m} q) :=
      originalIntrinsicAmbientTensorModule.{0,0,0,0,m}
        ℚ (Polynomial ℚ) LargeCoefficient SmallCoefficient actualLargeSupport actualSmallSupport q
    (epsilon ⊗ₜ[Polynomial ℚ] eta) • z =
      originalIntrinsicAmbientLeftOperator.{0,0,0,0,m}
        ℚ (Polynomial ℚ) LargeCoefficient SmallCoefficient actualLargeSupport actualSmallSupport q epsilon
          (originalIntrinsicAmbientRightOperator.{0,0,0,0,m}
            ℚ (Polynomial ℚ) LargeCoefficient SmallCoefficient actualLargeSupport actualSmallSupport q eta z) :=
  originalIntrinsicAmbientTensorModule_tmul.{0,0,0,0,m}
    ℚ (Polynomial ℚ) LargeCoefficient SmallCoefficient actualLargeSupport actualSmallSupport q epsilon eta z

theorem nilpotent_tensor_square :
    letI : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
    letI : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
    (epsilon ⊗ₜ[Polynomial ℚ] eta : LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) *
      (epsilon ⊗ₜ[Polynomial ℚ] eta) = 0 := by
  let : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
  let : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
  rw [Algebra.TensorProduct.tmul_mul_tmul, epsilon_mul_epsilon, TensorProduct.zero_tmul]

theorem standard_nilpotent_square_action (q : ℕ) (z : StandardTor.{m} q) :
    letI : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
    letI : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
    letI : Module (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) (StandardTor.{m} q) :=
      originalStandardAmbientTensorModule.{0,0,0,0,0,0,m}
        ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q
    (epsilon ⊗ₜ[Polynomial ℚ] eta) • ((epsilon ⊗ₜ[Polynomial ℚ] eta) • z) = 0 := by
  let : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
  let : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
  let : Module (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) (StandardTor.{m} q) :=
    originalStandardAmbientTensorModule.{0,0,0,0,0,0,m}
      ℚ ℚ (Polynomial ℚ) ℚ LargeCoefficient SmallCoefficient leftSupport rightSupport q
  rw [← mul_smul, nilpotent_tensor_square]
  exact zero_smul (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) z

theorem intrinsic_nilpotent_square_action (q : ℕ) (z : IntrinsicTor.{m} q) :
    letI : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
    letI : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
    letI : Module (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) (IntrinsicTor.{m} q) :=
      originalIntrinsicAmbientTensorModule.{0,0,0,0,m}
        ℚ (Polynomial ℚ) LargeCoefficient SmallCoefficient actualLargeSupport actualSmallSupport q
    (epsilon ⊗ₜ[Polynomial ℚ] eta) • ((epsilon ⊗ₜ[Polynomial ℚ] eta) • z) = 0 := by
  let : Algebra (Polynomial ℚ) LargeCoefficient := actualLargeSupport.toRingHom.toAlgebra
  let : Algebra (Polynomial ℚ) SmallCoefficient := actualSmallSupport.toRingHom.toAlgebra
  let : Module (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) (IntrinsicTor.{m} q) :=
    originalIntrinsicAmbientTensorModule.{0,0,0,0,m}
      ℚ (Polynomial ℚ) LargeCoefficient SmallCoefficient actualLargeSupport actualSmallSupport q
  rw [← mul_smul, nilpotent_tensor_square]
  exact zero_smul (LargeCoefficient ⊗[Polynomial ℚ] SmallCoefficient) z


section ArbitraryModuleUniverses

universe ku au bu xu

variable (K : Type ku) (A : Type au) (B : Type bu)
  [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  (X : Type (max ku au bu xu)) [AddCommGroup X] [Module K X] [Module B X]
  [IsScalarTower K B X]

/-- Original coefficients remain arbitrary modules in their actual common
universe, with the product action supplied by the proved canonical construction. -/
def arbitraryCoefficientUniverseClient := tensorAdjoinCoefficientEquiv.{ku,au,bu,xu} K A B X

/-- The actual native adjoining comparison accepts an arbitrary coefficient
module and original ambient module, deriving the adjoining flatness from K. -/
def arbitraryNativeTorUniverseClient
    (N : ModuleCat.{max ku au bu xu} (A ⊗[K] B)) (q : ℕ) :=
  tensorAdjoinNativeTorIso.{ku,au,bu,xu} K A B X N q

/-- This raw pure-tensor client does not require a ring or flatness on X. -/
example (a : A) (b : B) (x : X) :
    letI : Algebra B (A ⊗[K] B) := Algebra.TensorProduct.rightAlgebra
    tensorAdjoinBaseEquiv.{ku,au,bu,xu} K A B X ((a ⊗ₜ[K] b) ⊗ₜ[B] x) =
      a ⊗ₜ[K] (b • x) :=
  tensorAdjoinBaseEquiv_tmul.{ku,au,bu,xu} K A B X a b x

end ArbitraryModuleUniverses

end FieldTensorTorComparisonTests
