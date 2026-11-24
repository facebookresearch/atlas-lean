/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- UNEXECUTED guarded source proposal from the adjacent bar provider; original maps retained. -/
-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.Cyclic
public import MathlibExt.Algebra.Homology.Embedding.PositiveNat
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# The augmented adjacent-product bar complex

Degree n consists of n + 2 algebra factors, with the alternating
adjacent-product differential b′. The augmentation multiplies the two
factors in degree zero. This differential has no cyclic last face.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) (A : Type v) [CommRing k] [NonUnitalRing A] [Module k A]
  [IsScalarTower k A A] [SMulCommClass k A A]

/-- The unaugmented bar has old b-prime degree n+1 in new degree n. -/
def underlyingBar : ChainComplex (ModuleCat.{max u v} k) ℕ :=
  (ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).restriction
    ComplexShape.positiveNatEmbedding

/-- The literal bar degree retains n+2 ordered algebra factors. -/
theorem underlyingBar_X (n : ℕ) :
    (underlyingBar k A).X n = ModuleCat.of k (A ⊗[k] TensorPower k (n + 1) A) := rfl

/-- The boundary is the alternating sum of adjacent-product faces. -/
theorem underlyingBar_d (n : ℕ) :
    (underlyingBar k A).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        ModuleCat.Algebra.Hochschild.NonUnital.regularFace k A (n + 1) i.castSucc :=
  ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex_d k A (n + 1)

/-- Canonical empty tensor coordinates identify the augmentation target with A. -/
def underlyingBarZeroCoordinate :
    (ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).X 0 ≃ₗ[k] A :=
  (TensorProduct.congr (LinearEquiv.refl k A) (TensorPower.zeroEquiv k A)).trans
    (TensorProduct.rid k A)

/-- Multiplication augmentation as a linear map to the original carrier A. -/
def underlyingBarAugmentationLinear : (underlyingBar k A).X 0 →ₗ[k] A :=
  (underlyingBarZeroCoordinate k A).toLinearMap.comp
    ((ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).d 1 0).hom

/-- The same augmentation in the native complex universe, using the canonical lift. -/
def underlyingBarAugmentation :
    (underlyingBar k A).X 0 ⟶ ModuleCat.of k (ULift.{max u v} A) :=
  ModuleCat.ofHom ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[k] ULift.{max u v} A).comp
    (underlyingBarAugmentationLinear k A))

/-- Empty tensor coordinates send an algebra element with its empty word to itself. -/
theorem underlyingBarZeroCoordinate_tprod (a : A) (z : Fin 0 → A) :
    underlyingBarZeroCoordinate k A (a ⊗ₜ[k] PiTensorProduct.tprod k z) = a := by
  change (TensorProduct.rid k A)
    ((TensorProduct.congr (LinearEquiv.refl k A) (TensorPower.zeroEquiv k A))
      (a ⊗ₜ[k] PiTensorProduct.tprod k z)) = a
  rw [TensorProduct.congr_tmul]
  change (TensorProduct.rid k A) (a ⊗ₜ[k] (PiTensorProduct.isEmptyEquiv (Fin 0))
    (PiTensorProduct.tprod k z)) = a
  rw [PiTensorProduct.isEmptyEquiv_apply_tprod, TensorProduct.rid_tmul, one_smul]

/-- The augmentation is literally multiplication on its two ordered factors. -/
theorem underlyingBarAugmentationLinear_tprod (a : A) (z : Fin 1 → A) :
    underlyingBarAugmentationLinear k A (a ⊗ₜ[k] PiTensorProduct.tprod k z) = a * z 0 := by
  change underlyingBarZeroCoordinate k A
    (((ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A).d 1 0).hom
      (a ⊗ₜ[k] PiTensorProduct.tprod k z)) = _
  rw [ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex_d_one_tprod,
    underlyingBarZeroCoordinate_tprod]

/-- This equation is the necessary data law for the augmentation. -/
theorem underlyingBar_d_augmentation :
    (underlyingBar k A).d 1 0 ≫ underlyingBarAugmentation k A = 0 := by
  let K : ChainComplex (ModuleCat.{max u v} k) ℕ :=
    ModuleCat.Algebra.Hochschild.NonUnital.bPrimeComplex k A
  let tail : K.X 0 ⟶ ModuleCat.of k (ULift.{max u v} A) :=
    ModuleCat.ofHom
      ((ULift.moduleEquiv.symm.toLinearMap : A →ₗ[k] ULift.{max u v} A).comp
        (underlyingBarZeroCoordinate k A).toLinearMap)
  have hd : (underlyingBar k A).d 1 0 = K.d 2 1 := by
    exact HomologicalComplex.restriction_d K ComplexShape.positiveNatEmbedding 1 0
  have haug : underlyingBarAugmentation k A = K.d 1 0 ≫ tail := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  have hfirst : (underlyingBar k A).d 1 0 ≫ underlyingBarAugmentation k A =
      K.d 2 1 ≫ (K.d 1 0 ≫ tail) :=
    congrArg₂ (fun (d : K.X 2 ⟶ K.X 1)
        (a : K.X 1 ⟶ ModuleCat.of k (ULift.{max u v} A)) => d ≫ a) hd haug
  have hassoc : K.d 2 1 ≫ (K.d 1 0 ≫ tail) =
      (K.d 2 1 ≫ K.d 1 0) ≫ tail :=
    (Category.assoc (K.d 2 1) (K.d 1 0) tail).symm
  have hzero : (K.d 2 1 ≫ K.d 1 0) ≫ tail = 0 :=
    (congrArg (fun d : K.X 2 ⟶ K.X 0 => d ≫ tail)
      (K.d_comp_d 2 1 0)).trans (zero_comp : (0 : K.X 2 ⟶ K.X 0) ≫ tail = 0)
  exact hfirst.trans (hassoc.trans hzero)

end ModuleCat.Algebra.Hochschild.AdjacentBar
