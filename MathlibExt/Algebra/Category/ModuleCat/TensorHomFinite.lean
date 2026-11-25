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

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Contraction
public import MathlibExt.Algebra.Category.ModuleCat.AnnihilatorQuotient
public import MathlibExt.LinearAlgebra.TensorProduct.SurjectiveScalarHom

/-!
# Native finite-projective tensor–Hom coefficient comparison

The coefficient comparison is the existing native finite-projective
contraction equivalence. Converting the original categorical projective
object uses the native `Small R` hypothesis in its original carrier world.
No basis, splitting, arbitrary comparison or desired IsIso is input data.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R] [Small.{v} R]

/-- The actual native right tensor–Hom equivalence on original finite-projective coefficients. -/
def finiteProjectiveHomTensorIso (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    ModuleCat.of R ((M →ₗ[R] J) ⊗[R] U) ≅
      ModuleCat.of R (M →ₗ[R] J ⊗[R] U) := by
  letI : Module.Projective R M := ModuleCat.projective_of_module_projective M
  exact (_root_.rTensorHomEquivHomRTensor R M J U).toModuleIso

/-- The original canonical coefficient map is the forward map of the earned native Iso. -/
theorem finiteProjectiveHomTensorIso_hom (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    (finiteProjectiveHomTensorIso R M J U).hom.hom =
      TensorProduct.rTensorHomToHomRTensor (.id R) M J U := by
  letI : Module.Projective R M := ModuleCat.projective_of_module_projective M
  exact _root_.rTensorHomEquivHomRTensor_toLinearMap (R := R) (M := M) (P := J) (Q := U)

end ModuleCat

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R]

/-- The canonical original R coefficient map is bijective in the original carrier
world. The actual tuple-annihilator quotient earns its needed small ring. -/
theorem finiteProjectiveHomTensor_bijective (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    Function.Bijective (TensorProduct.rTensorHomToHomRTensor (.id R) M J U) := by
  let I := Module.annihilator R (M × J × U)
  let S := R ⧸ I
  have hM : I ≤ Module.annihilator R M := by
    rw [show I = Module.annihilator R M ⊓ Module.annihilator R J ⊓
      Module.annihilator R U from annihilator_tuple R M J U]
    exact inf_le_left.trans inf_le_left
  have hJ : I ≤ Module.annihilator R J := by
    rw [show I = Module.annihilator R M ⊓ Module.annihilator R J ⊓
      Module.annihilator R U from annihilator_tuple R M J U]
    exact inf_le_left.trans inf_le_right
  have hU : I ≤ Module.annihilator R U := by
    rw [show I = Module.annihilator R M ⊓ Module.annihilator R J ⊓
      Module.annihilator R U from annihilator_tuple R M J U]
    exact inf_le_right
  letI : Module S M := annihilatorQuotientModule R I M hM
  letI : Module S J := annihilatorQuotientModule R I J hJ
  letI : Module S U := annihilatorQuotientModule R I U hU
  letI : IsScalarTower R S M := annihilatorQuotientTower R I M hM
  letI : IsScalarTower R S J := annihilatorQuotientTower R I J hJ
  letI : IsScalarTower R S U := annihilatorQuotientTower R I U hU
  letI : Small.{v} S := small_annihilatorQuotient R (M × J × U)
  letI : CategoryTheory.Projective (ModuleCat.of S M) :=
    annihilatorQuotient_projective R I M hM
  letI : Module.Projective S M :=
    ModuleCat.projective_of_module_projective (ModuleCat.of S M)
  letI : Module.Finite S M := annihilatorQuotient_finite R I M hM
  have hs : Function.Surjective (algebraMap R S) := Ideal.Quotient.mk_surjective (I := I)
  let e := TensorProduct.rTensorHomEquivOfSurjectiveScalars
    (R := R) (S := S) (M := M) (J := J) (U := U) hs
  have he : e.toLinearMap = TensorProduct.rTensorHomToHomRTensor (.id R) M J U :=
    TensorProduct.rTensorHomEquivOfSurjectiveScalars_toLinearMap hs
  rw [← he]
  exact e.bijective

/-- The actual coefficient Iso has the canonical original R map as its forward
component; no Small R/world equality or desired comparison is a premise. -/
def finiteProjectiveHomTensorIsoOfAnnihilatorQuotient (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    ModuleCat.of R ((M →ₗ[R] J) ⊗[R] U) ≅
      ModuleCat.of R (M →ₗ[R] J ⊗[R] U) :=
  (LinearEquiv.ofBijective (TensorProduct.rTensorHomToHomRTensor (.id R) M J U)
    (finiteProjectiveHomTensor_bijective R M J U)).toModuleIso

/-- Exact original forward-map receipt for the earned original-world coefficient Iso. -/
theorem finiteProjectiveHomTensorIsoOfAnnihilatorQuotient_hom (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    (finiteProjectiveHomTensorIsoOfAnnihilatorQuotient R M J U).hom.hom =
      TensorProduct.rTensorHomToHomRTensor (.id R) M J U := rfl

/-- The earned inverse undoes the canonical original R coefficient map. -/
theorem finiteProjectiveHomTensorIsoOfAnnihilatorQuotient_inv_forward
    (M J U : ModuleCat.{v} R) [CategoryTheory.Projective M] [Module.Finite R M]
    (t : (M →ₗ[R] J) ⊗[R] U) :
    (finiteProjectiveHomTensorIsoOfAnnihilatorQuotient R M J U).inv.hom
        (TensorProduct.rTensorHomToHomRTensor (.id R) M J U t) = t := by
  let c := finiteProjectiveHomTensorIsoOfAnnihilatorQuotient R M J U
  have h := congrArg (fun f : ModuleCat.of R ((M →ₗ[R] J) ⊗[R] U) ⟶
      ModuleCat.of R ((M →ₗ[R] J) ⊗[R] U) => f.hom t) c.hom_inv_id
  simpa only [c, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply, finiteProjectiveHomTensorIsoOfAnnihilatorQuotient_hom] using h

/-- The canonical original R map recovers the original map from the earned inverse. -/
theorem finiteProjectiveHomTensorIsoOfAnnihilatorQuotient_forward_inv
    (M J U : ModuleCat.{v} R) [CategoryTheory.Projective M] [Module.Finite R M]
    (f : M →ₗ[R] J ⊗[R] U) :
    (finiteProjectiveHomTensorIsoOfAnnihilatorQuotient R M J U).hom.hom
        ((finiteProjectiveHomTensorIsoOfAnnihilatorQuotient R M J U).inv.hom f) = f := by
  let c := finiteProjectiveHomTensorIsoOfAnnihilatorQuotient R M J U
  have h := congrArg (fun g : ModuleCat.of R (M →ₗ[R] J ⊗[R] U) ⟶
      ModuleCat.of R (M →ₗ[R] J ⊗[R] U) => g.hom f) c.inv_hom_id
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using h

end ModuleCat
