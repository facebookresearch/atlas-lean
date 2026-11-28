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
# Tensor–Hom comparison for a finite projective Hom domain

Let R be a commutative ring in universe u, and M,J,U R-modules in carrier universe v. Assume M
is finitely generated and projective as an object of R-Mod_v. The canonical contraction
χ:Hom_R(M,J)⊗_R U→Hom_R(M,J⊗_R U), defined by χ(f⊗u)(m)=f(m)⊗u, is an isomorphism.

One construction uses the additional assumption that R can be represented in v. The
annihilator-quotient construction instead passes through R/Ann_R(M×J×U), whose underlying set
has a representative in v, and returns the same R-linear contraction map. It yields bijectivity
and an isomorphism without an ambient-ring smallness premise. Both inverse identities are stated
on the given R-module carriers; J and U need not be finite or projective.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

universe u v

variable (R : Type u) [CommRing R] [Small.{v} R]

/-- Let R be commutative in universe u and M,J,U R-modules in a common carrier universe v. Assume M
is projective as an object of R-Mod_v and finitely generated over R. Assume also that the
underlying set of R can be represented in v. This is the R-module isomorphism Hom_R(M,J)⊗_R
U≅Hom_R(M,J⊗_R U) induced by contraction. Its forward map sends f⊗u to the linear map m↦f(m)⊗u.
No basis or splitting is chosen as input. -/
def finiteProjectiveHomTensorIso (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    ModuleCat.of R ((M →ₗ[R] J) ⊗[R] U) ≅
      ModuleCat.of R (M →ₗ[R] J ⊗[R] U) := by
  letI : Module.Projective R M := ModuleCat.projective_of_module_projective M
  exact (_root_.rTensorHomEquivHomRTensor R M J U).toModuleIso

/-- Let R be commutative in universe u and M,J,U R-modules in a common carrier universe v. Assume M
is projective as an object of R-Mod_v and finitely generated over R. Assume also that the
underlying set of R can be represented in v. The forward R-linear map of Hom_R(M,J)⊗_R
U≅Hom_R(M,J⊗_R U) equals the canonical contraction χ(f⊗u)(m)=f(m)⊗u. This equation identifies
the comparison map on the Hom and tensor modules. -/
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

/-- Let R be commutative in universe u and M,J,U R-modules in a common carrier universe v. Assume M
is projective as an object of R-Mod_v and finitely generated over R. Then χ:Hom_R(M,J)⊗_R
U→Hom_R(M,J⊗_R U), χ(f⊗u)(m)=f(m)⊗u, is bijective. The common annihilator quotient
R/Ann_R(M×J×U) supplies a scalar ring representable in v and preserves this same R-linear map,
so no such assumption on R is required. -/
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

/-- Let R be commutative in universe u and M,J,U R-modules in a common carrier universe v. Assume M
is projective as an object of R-Mod_v and finitely generated over R. The contraction
χ(f⊗u)(m)=f(m)⊗u gives this R-module isomorphism Hom_R(M,J)⊗_R U≅Hom_R(M,J⊗_R U). Bijectivity is
obtained through the common annihilator quotient, and the returned isomorphism has the given
R-linear contraction as its forward map. -/
def finiteProjectiveHomTensorIsoOfAnnihilatorQuotient (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    ModuleCat.of R ((M →ₗ[R] J) ⊗[R] U) ≅
      ModuleCat.of R (M →ₗ[R] J ⊗[R] U) :=
  (LinearEquiv.ofBijective (TensorProduct.rTensorHomToHomRTensor (.id R) M J U)
    (finiteProjectiveHomTensor_bijective R M J U)).toModuleIso

/-- Let R be commutative in universe u and M,J,U R-modules in a common carrier universe v. Assume M
is projective as an object of R-Mod_v and finitely generated over R. Let e:Hom_R(M,J)⊗_R
U≅Hom_R(M,J⊗_R U) be the annihilator-quotient comparison. Its forward linear map is exactly χ,
where χ(f⊗u)(m)=f(m)⊗u. The scalar quotient therefore does not change the final R-module
comparison. -/
theorem finiteProjectiveHomTensorIsoOfAnnihilatorQuotient_hom (M J U : ModuleCat.{v} R)
    [CategoryTheory.Projective M] [Module.Finite R M] :
    (finiteProjectiveHomTensorIsoOfAnnihilatorQuotient R M J U).hom.hom =
      TensorProduct.rTensorHomToHomRTensor (.id R) M J U := rfl

/-- Let R be commutative in universe u and M,J,U R-modules in a common carrier universe v. Assume M
is projective as an object of R-Mod_v and finitely generated over R. For t∈Hom_R(M,J)⊗_R U and
the canonical comparison e with forward contraction χ, e.inv(χ(t))=t. The equality is the
inverse identity on the complete source tensor module. -/
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

/-- Let R be commutative in universe u and M,J,U R-modules in a common carrier universe v. Assume M
is projective as an object of R-Mod_v and finitely generated over R. For g∈Hom_R(M,J⊗_R U) and
the annihilator-quotient comparison e, e.hom(e.inv(g))=g. Its forward map is the contraction χ,
so the equality identifies every target linear map with the contraction of its inverse tensor. -/
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
