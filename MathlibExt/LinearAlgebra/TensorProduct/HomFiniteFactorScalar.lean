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

public import MathlibExt.LinearAlgebra.TensorProduct.HomFiniteFactor
public import MathlibExt.LinearAlgebra.TensorProduct.SurjectiveScalarHom

/-!
# Hom–tensor comparison along a surjective scalar map

For a surjective algebra map `R → S`, compatible scalar actions identify the
tensor products over `R` and `S`. Reinterpreting an `R`-linear map into an
`S`-module as an algebra-map-semilinear map permits the Hom source to remain
an arbitrary `R`-module. Finite projectivity is required over `S` only on the
tensor factor, and the resulting forward map is the `R`-linear comparison.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped TensorProduct

namespace TensorProduct

universe uR uS uP uN uU

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
  {P : Type uP} {N : Type uN} {U : Type uU}
  [AddCommGroup P] [AddCommGroup N] [AddCommGroup U]
  [Module R P] [Module R N] [Module R U]
  [Module S N] [Module S U]
  [IsScalarTower R S N] [IsScalarTower R S U]

/-- Scalar restriction on the codomain identifies linear maps with
algebra-map-semilinear maps without a target-ring action on the source. -/
private def homTensorAlgebraMapEquiv :
    (P →ₗ[R] N) ≃ₗ[R] (P →ₛₗ[algebraMap R S] N) where
  toFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r p => by
        simpa only [IsScalarTower.algebraMap_smul] using f.map_smul r p }
  invFun f :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r p => by
        simpa only [IsScalarTower.algebraMap_smul] using f.map_smulₛₗ r p }
  map_add' f g := by
    apply LinearMap.ext
    intro p
    rfl
  map_smul' r f := by
    apply LinearMap.ext
    intro p
    rfl
  left_inv f := by
    apply LinearMap.ext
    intro p
    rfl
  right_inv f := by
    apply LinearMap.ext
    intro p
    rfl

private def homTensorFiniteFactorScalarInputEquiv
    (h : Function.Surjective (algebraMap R S)) :
    (P →ₗ[R] N) ⊗[R] U ≃ₗ[R] (P →ₛₗ[algebraMap R S] N) ⊗[S] U := by
  letI : CompatibleSMul R S (P →ₛₗ[algebraMap R S] N) U :=
    compatibleSMul_of_surjective_algebraMap
      (M := P →ₛₗ[algebraMap R S] N) (J := U) h
  exact TensorProduct.congr (homTensorAlgebraMapEquiv (R := R) (S := S))
      (LinearEquiv.refl R U) ≪≫ₗ
    TensorProduct.equivOfCompatibleSMul S R R (P →ₛₗ[algebraMap R S] N) U

private def homTensorFiniteFactorScalarOutputEquiv
    (h : Function.Surjective (algebraMap R S)) :
    (P →ₛₗ[algebraMap R S] N ⊗[S] U) ≃ₗ[R] (P →ₗ[R] N ⊗[R] U) := by
  letI : CompatibleSMul R S N U :=
    compatibleSMul_of_surjective_algebraMap (M := N) (J := U) h
  let eTensor : N ⊗[S] U ≃ₗ[R] N ⊗[R] U :=
    TensorProduct.equivOfCompatibleSMul R S R N U
  exact (homTensorAlgebraMapEquiv (R := R) (S := S) (P := P) (N := N ⊗[S] U)).symm ≪≫ₗ
    (LinearEquiv.refl R P).arrowCongr eTensor

/-- A finite projective `S`-module tensor factor gives the `R`-linear
comparison equivalence along a surjective algebra map. The source `P` needs
only its original `R`-module structure. -/
def homTensorFiniteFactorEquivOfSurjectiveScalars
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (P →ₗ[R] N) ⊗[R] U ≃ₗ[R] P →ₗ[R] N ⊗[R] U :=
  homTensorFiniteFactorScalarInputEquiv h ≪≫ₗ
    (LinearEquiv.ofBijective
      (rTensorHomToHomRTensor (algebraMap R S) P N U)
      (rTensorHomToHomRTensor_bijective_of_finite_projective
        (algebraMap R S) P N U)).restrictScalars R ≪≫ₗ
    homTensorFiniteFactorScalarOutputEquiv h

/-- Every original pure tensor retains its actual coefficient evaluation. -/
theorem homTensorFiniteFactorEquivOfSurjectiveScalars_tmul
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) (f : P →ₗ[R] N) (u : U) (p : P) :
    homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h
        (f ⊗ₜ[R] u) p = f p ⊗ₜ[R] u := by
  simp [homTensorFiniteFactorEquivOfSurjectiveScalars, homTensorAlgebraMapEquiv,
    homTensorFiniteFactorScalarInputEquiv, homTensorFiniteFactorScalarOutputEquiv,
    TensorProduct.congr_tmul, TensorProduct.rTensorHomToHomRTensor_apply,
    TensorProduct.equivOfCompatibleSMul, LinearEquiv.arrowCongr]

/-- The source map is exactly the original R coefficient comparison, with the
scalar quotient and its actual inverse completely internal to the construction. -/
theorem homTensorFiniteFactorEquivOfSurjectiveScalars_toLinearMap
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h).toLinearMap =
      rTensorHomToHomRTensor (.id R) P N U := by
  apply TensorProduct.ext'
  intro f u
  apply LinearMap.ext
  intro p
  change homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h
      (f ⊗ₜ[R] u) p = rTensorHomToHomRTensor (.id R) P N U (f ⊗ₜ[R] u) p
  rw [homTensorFiniteFactorEquivOfSurjectiveScalars_tmul,
    TensorProduct.rTensorHomToHomRTensor_apply]

end TensorProduct
