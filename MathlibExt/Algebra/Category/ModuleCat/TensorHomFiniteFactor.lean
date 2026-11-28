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
public import MathlibExt.LinearAlgebra.TensorProduct.HomFiniteFactorScalar

/-!
# Tensor–Hom comparison for a finite projective tensor factor

Let R be commutative in universe u and P,N,U R-modules in carrier universe v. If the tensor
factor U is finitely generated and projective in R-Mod_v, the contraction χ:Hom_R(P,N)⊗_R
U→Hom_R(P,N⊗_R U), χ(f⊗u)(p)=f(p)⊗u, is bijective. The Hom domain P is arbitrary.

The common annihilator quotient R/Ann_R(P×N×U) has a representative in v and transfers the
projectivity of U. Its finite-projective comparison gives an R-module isomorphism on the given
carriers, with the same contraction as its forward map. An ambient-ring smallness hypothesis is
not needed.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- Let R be a commutative ring in universe u and P,N,U R-modules in carrier universe v. Assume U is
projective as an object of R-Mod_v and finitely generated over R; P and N are arbitrary. The
R-linear map χ:Hom_R(P,N)⊗_R U→Hom_R(P,N⊗_R U), χ(f⊗u)(p)=f(p)⊗u, is bijective. The common
annihilator quotient provides a scalar ring representable in v and carries the stated
projectivity of U; no smallness premise on R is imposed. -/
theorem finiteProjectiveTensorFactorHomTensor_bijective (P N U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    Function.Bijective (TensorProduct.rTensorHomToHomRTensor (.id R) P N U) := by
  let I := Module.annihilator R (P × N × U)
  let S := R ⧸ I
  have hN : I ≤ Module.annihilator R N := by
    rw [show I = Module.annihilator R P ⊓ Module.annihilator R N ⊓
      Module.annihilator R U from annihilator_tuple R P N U]
    exact inf_le_left.trans inf_le_right
  have hU : I ≤ Module.annihilator R U := by
    rw [show I = Module.annihilator R P ⊓ Module.annihilator R N ⊓
      Module.annihilator R U from annihilator_tuple R P N U]
    exact inf_le_right
  letI : Module S N := annihilatorQuotientModule R I N hN
  letI : Module S U := annihilatorQuotientModule R I U hU
  letI : IsScalarTower R S N := annihilatorQuotientTower R I N hN
  letI : IsScalarTower R S U := annihilatorQuotientTower R I U hU
  letI : Small.{v} S := small_annihilatorQuotient R (P × N × U)
  letI : CategoryTheory.Projective (ModuleCat.of S U) :=
    annihilatorQuotient_projective R I U hU
  letI : Module.Projective S U :=
    ModuleCat.projective_of_module_projective (ModuleCat.of S U)
  letI : Module.Finite S U := annihilatorQuotient_finite R I U hU
  have hs : Function.Surjective (algebraMap R S) := Ideal.Quotient.mk_surjective (I := I)
  let e := TensorProduct.homTensorFiniteFactorEquivOfSurjectiveScalars
    (R := R) (S := S) (P := P) (N := N) (U := U) hs
  have he : e.toLinearMap = TensorProduct.rTensorHomToHomRTensor (.id R) P N U :=
    TensorProduct.homTensorFiniteFactorEquivOfSurjectiveScalars_toLinearMap hs
  rw [← he]
  exact e.bijective

/-- Let R be a commutative ring in universe u and P,N,U R-modules in carrier universe v. Assume U is
projective as an object of R-Mod_v and finitely generated over R; P and N are arbitrary. This is
the R-module isomorphism Hom_R(P,N)⊗_R U≅Hom_R(P,N⊗_R U) obtained from the bijective contraction
χ(f⊗u)(p)=f(p)⊗u. The comparison is returned over R on the given carrier modules. -/
def finiteProjectiveTensorFactorHomTensorIso (P N U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    ModuleCat.of R ((P →ₗ[R] N) ⊗[R] U) ≅ ModuleCat.of R (P →ₗ[R] N ⊗[R] U) :=
  (LinearEquiv.ofBijective (TensorProduct.rTensorHomToHomRTensor (.id R) P N U)
    (finiteProjectiveTensorFactorHomTensor_bijective R P N U)).toModuleIso

/-- Let R be a commutative ring in universe u and P,N,U R-modules in carrier universe v. Assume U is
projective as an object of R-Mod_v and finitely generated over R; P and N are arbitrary. The
forward linear map of the canonical isomorphism Hom_R(P,N)⊗_R U≅Hom_R(P,N⊗_R U) equals χ, with
χ(f⊗u)(p)=f(p)⊗u. This identifies the existing comparison through its exact coefficient map. -/
theorem finiteProjectiveTensorFactorHomTensorIso_hom (P N U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    (finiteProjectiveTensorFactorHomTensorIso R P N U).hom.hom =
      TensorProduct.rTensorHomToHomRTensor (.id R) P N U := rfl

end ModuleCat
