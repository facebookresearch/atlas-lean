/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Category.ModuleCat.AnnihilatorQuotient
public import MathlibExt.LinearAlgebra.TensorProduct.PiFiniteFactorScalar

/-!
# Original-world integer Hom products with a finite-projective tensor factor

The index is the actual cochain index ℤ. Original categorical projectivity and
finiteness of the tensor factor earn the product comparison on the original
module carriers. Quotient scalar smallness is earned from the original product
and factor actions; no Small R or carrier/world equality premise is introduced.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- The original integer-indexed product comparison is bijective for the
original finite categorical-projective tensor factor. -/
theorem tensorIntegerProductFiniteFactor_bijective (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    Function.Bijective (TensorProduct.piRightHom R R U (fun i => (N i).carrier)) := by
  classical
  let P := ModuleCat.of R (∀ i : ℤ, N i)
  let I := Module.annihilator R (P × P × U)
  let S := R ⧸ I
  have hP : I ≤ Module.annihilator R P := by
    rw [show I = Module.annihilator R P ⊓ Module.annihilator R P ⊓
      Module.annihilator R U from annihilator_tuple R P P U]
    exact inf_le_left.trans inf_le_left
  have hU : I ≤ Module.annihilator R U := by
    rw [show I = Module.annihilator R P ⊓ Module.annihilator R P ⊓
      Module.annihilator R U from annihilator_tuple R P P U]
    exact inf_le_right
  have hN (i : ℤ) : I ≤ Module.annihilator R (N i) := by
    intro r hr
    rw [Module.mem_annihilator]
    intro x
    have hp := (Module.mem_annihilator.mp (hP hr)) (Pi.single i x : ∀ j : ℤ, N j)
    have hi := congrArg (fun y : ∀ j : ℤ, N j => y i) hp
    change r • ((Pi.single i x : ∀ j : ℤ, N j) i) = 0 at hi
    simpa only [Pi.single_eq_same] using hi
  letI (i : ℤ) : Module S (N i) := annihilatorQuotientModule R I (N i) (hN i)
  letI : Module S U := annihilatorQuotientModule R I U hU
  letI (i : ℤ) : IsScalarTower R S (N i) := annihilatorQuotientTower R I (N i) (hN i)
  letI : IsScalarTower R S U := annihilatorQuotientTower R I U hU
  letI : Small.{v} S := small_annihilatorQuotient R (P × P × U)
  letI : CategoryTheory.Projective (ModuleCat.of S U) := annihilatorQuotient_projective R I U hU
  letI : Module.Projective S U := ModuleCat.projective_of_module_projective (ModuleCat.of S U)
  letI : Module.Finite S U := annihilatorQuotient_finite R I U hU
  have hs : Function.Surjective (algebraMap R S) := Ideal.Quotient.mk_surjective (I := I)
  let e := TensorProduct.piRightFiniteFactorOfSurjectiveScalars
    (R := R) (S := S) (U := U) (fun i => (N i).carrier) hs
  have he : e.toLinearMap = TensorProduct.piRightHom R R U (fun i => (N i).carrier) :=
    TensorProduct.piRightFiniteFactorOfSurjectiveScalars_toLinearMap (fun i => (N i).carrier) hs
  rw [← he]
  exact e.bijective

/-- The original integer-product Iso has exactly the native original product
comparison as its hom, including all original coordinate projections. -/
def tensorIntegerProductFiniteFactorIso (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    ModuleCat.of R (U ⊗[R] (∀ i : ℤ, N i)) ≅
      ModuleCat.of R (∀ i : ℤ, U ⊗[R] N i) :=
  (LinearEquiv.ofBijective (TensorProduct.piRightHom R R U (fun i => (N i).carrier))
    (tensorIntegerProductFiniteFactor_bijective R N U)).toModuleIso

theorem tensorIntegerProductFiniteFactorIso_hom (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    (tensorIntegerProductFiniteFactorIso R N U).hom.hom =
      TensorProduct.piRightHom R R U (fun i => (N i).carrier) := rfl

/-- The actual comparison for an original Hom product followed by the tensor
factor: each original product projection is tensored with the identity of U. -/
def integerProductRightTensorComparison (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R) :
    (∀ i : ℤ, N i) ⊗[R] U →ₗ[R] ∀ i : ℤ, N i ⊗[R] U :=
  LinearMap.pi (fun i => (LinearMap.proj i).rTensor U)

/-- Native tensor symmetry transports the earned original product comparison
to the original right-tensor position, preserving each original projection. -/
theorem integerProductRightTensorComparison_bijective
    (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    Function.Bijective (integerProductRightTensorComparison R N U) := by
  let d := TensorProduct.comm R (∀ i : ℤ, N i) U
  let c := LinearEquiv.piCongrRight (fun i => TensorProduct.comm R U (N i))
  have h : integerProductRightTensorComparison R N U =
      c.toLinearMap.comp ((TensorProduct.piRightHom R R U (fun i => (N i).carrier)).comp
        d.toLinearMap) := by
    apply TensorProduct.ext'
    intro x u
    funext i
    rfl
  rw [h]
  exact c.bijective.comp ((tensorIntegerProductFiniteFactor_bijective R N U).comp d.bijective)

/-- The actual original right-tensor product Iso has the original tensorized
projections as its hom, even for the full unbounded integer Hom product. -/
def integerProductRightTensorIso (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    ModuleCat.of R ((∀ i : ℤ, N i) ⊗[R] U) ≅ ModuleCat.of R (∀ i : ℤ, N i ⊗[R] U) :=
  (LinearEquiv.ofBijective (integerProductRightTensorComparison R N U)
    (integerProductRightTensorComparison_bijective R N U)).toModuleIso

theorem integerProductRightTensorIso_hom (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    (integerProductRightTensorIso R N U).hom.hom = integerProductRightTensorComparison R N U := rfl

end ModuleCat
