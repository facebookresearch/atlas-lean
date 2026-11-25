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
# Hom–tensor comparison with a finite-projective tensor factor

Categorical projectivity is required on the tensor factor U; P is arbitrary.
The common annihilator quotient is small in the carrier universe, and
fully faithful epi-preserving scalar restriction transfers projectivity.
The coefficient comparison is invertible without a `Small R` hypothesis
or a carrier lift.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- The actual original R map is bijective when its original tensor factor is
finite categorical projective. Native scalar quotient smallness is earned. -/
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

/-- The original-world coefficient Iso has the original map as its hom. -/
def finiteProjectiveTensorFactorHomTensorIso (P N U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    ModuleCat.of R ((P →ₗ[R] N) ⊗[R] U) ≅ ModuleCat.of R (P →ₗ[R] N ⊗[R] U) :=
  (LinearEquiv.ofBijective (TensorProduct.rTensorHomToHomRTensor (.id R) P N U)
    (finiteProjectiveTensorFactorHomTensor_bijective R P N U)).toModuleIso

theorem finiteProjectiveTensorFactorHomTensorIso_hom (P N U : ModuleCat.{v} R)
    [CategoryTheory.Projective U] [Module.Finite R U] :
    (finiteProjectiveTensorFactorHomTensorIso R P N U).hom.hom =
      TensorProduct.rTensorHomToHomRTensor (.id R) P N U := rfl

end ModuleCat
