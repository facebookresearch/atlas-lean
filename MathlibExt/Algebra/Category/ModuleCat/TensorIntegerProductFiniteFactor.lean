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
# Tensoring integer-indexed products with a finite projective module

Let `R` be a commutative ring, `N : ℤ → ModuleCat.{v} R` an integer-indexed family, and `U :
ModuleCat.{v} R` a finite, categorically projective module. The canonical map `U ⊗_R (∏ i, N
i) → ∏ i, U ⊗_R N i` is an isomorphism, with `u ⊗ x ↦ (i ↦ u ⊗ x i)`.

There is also a comparison with `U` on the right, `(∏ i, N i) ⊗_R U → ∏ i, N i ⊗_R U`, given
by the coordinate projections. It is an isomorphism under the same finite-projective
hypothesis. The scalar universe is independent of `v`, and the products range over all integer
indices.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- Left finite-projective tensor factor commutes with integer products.

For an integer-indexed family of `R`-modules and a finite categorically projective module `U`,
the canonical map `U ⊗_R (∏ i : ℤ, N i) → ∏ i : ℤ, U ⊗_R N i` is bijective. -/
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

/-- Left finite-projective tensor factor gives an integer-product isomorphism.

Bundle the bijective canonical product comparison as an isomorphism in `ModuleCat.{v} R` from
`U ⊗_R (∏ i : ℤ, N i)` to `∏ i : ℤ, U ⊗_R N i`. -/
def tensorIntegerProductFiniteFactorIso (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    ModuleCat.of R (U ⊗[R] (∀ i : ℤ, N i)) ≅
      ModuleCat.of R (∀ i : ℤ, U ⊗[R] N i) :=
  (LinearEquiv.ofBijective (TensorProduct.piRightHom R R U (fun i => (N i).carrier))
    (tensorIntegerProductFiniteFactor_bijective R N U)).toModuleIso

/-- Forward left-factor product isomorphism is the canonical tensor comparison.

The underlying linear map of the finite-projective left-factor product isomorphism is
`TensorProduct.piRightHom R R U (fun i => (N i).carrier)`. -/
theorem tensorIntegerProductFiniteFactorIso_hom (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    (tensorIntegerProductFiniteFactorIso R N U).hom.hom =
      TensorProduct.piRightHom R R U (fun i => (N i).carrier) := rfl

/-- Integer-product comparison with the tensor factor on the right.

For any `U`, tensor each product projection with `U` to define `(∏ i : ℤ, N i) ⊗_R U →ₗ[R] ∏ i
: ℤ, N i ⊗_R U`. On a pure tensor it gives the family `i ↦ x i ⊗ u`. -/
def integerProductRightTensorComparison (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R) :
    (∀ i : ℤ, N i) ⊗[R] U →ₗ[R] ∀ i : ℤ, N i ⊗[R] U :=
  LinearMap.pi (fun i => (LinearMap.proj i).rTensor U)

/-- Right finite-projective tensor factor commutes with integer products.

If `U` is finite and categorically projective, the canonical right-factor integer-product
comparison is bijective. -/
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

/-- Right finite-projective tensor factor gives an integer-product isomorphism.

For finite categorically projective `U`, the right-factor product comparison gives an
isomorphism `(∏ i : ℤ, N i) ⊗_R U ≅ ∏ i : ℤ, N i ⊗_R U` in the chosen module universe. -/
def integerProductRightTensorIso (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    ModuleCat.of R ((∀ i : ℤ, N i) ⊗[R] U) ≅ ModuleCat.of R (∀ i : ℤ, N i ⊗[R] U) :=
  (LinearEquiv.ofBijective (integerProductRightTensorComparison R N U)
    (integerProductRightTensorComparison_bijective R N U)).toModuleIso

/-- Forward right-factor product isomorphism is its projection comparison.

The underlying linear map of the right-factor product isomorphism is
`integerProductRightTensorComparison R N U`. -/
theorem integerProductRightTensorIso_hom (N : ℤ → ModuleCat.{v} R) (U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    (integerProductRightTensorIso R N U).hom.hom = integerProductRightTensorComparison R N U := rfl

end ModuleCat
