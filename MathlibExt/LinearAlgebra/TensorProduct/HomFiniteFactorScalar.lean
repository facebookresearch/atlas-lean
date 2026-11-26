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
# Finite-projective tensor–Hom comparison under a scalar surjection

Let S be a commutative R-algebra whose algebra map is surjective. Let P be an arbitrary
R-module, and N,U compatible R,S-modules. If U is finitely generated and projective over S, the
canonical R-linear map χ:Hom_R(P,N)⊗_R U→Hom_R(P,N⊗_R U), χ(f⊗u)(p)=f(p)⊗u, is an isomorphism.

Compatible scalar actions identify R-linear maps into N with algebra-map-semilinear maps,
without requiring an S-action on P. Surjectivity identifies the R- and S-balanced tensor
quotients, and finite projectivity of U over S gives the contraction comparison. The returned
equivalence has χ as its forward map, with independent universes for both rings and all three
modules.
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

/-- Let S be a commutative R-algebra, P an R-module and N an R,S-module with r•n=algebraMap(r)•n.
The map space Hom_R(P,N) is canonically R-linearly equivalent to the space of
algebra-map-semilinear maps P→N. Forward and inverse maps retain the same functions; the
scalar-tower equation identifies their linearity laws. P requires only its R-action, and the
ring and carrier universes are independent. -/
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
        simpa only [RingHom.id_apply, IsScalarTower.algebraMap_smul]
          using f.map_smulₛₗ r p }
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

/-- Let R,S be commutative rings with an R-algebra structure on S. Let P be an R-module and N,U
modules over R and S with compatible scalar towers r•x=algebraMap(r)•x. All ring and module
universes are independent. Assume algebraMap:R→S is surjective and U is finitely generated and
projective as an S-module. Then χ:Hom_R(P,N)⊗_R U→Hom_R(P,N⊗_R U), χ(f⊗u)(p)=f(p)⊗u, is
bijective. Finite projectivity is required on U over S, with no finiteness or projectivity
condition on P. -/
theorem homTensorFiniteFactor_bijective_of_surjective_scalars
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    Function.Bijective (rTensorHomToHomRTensor (.id R) P N U) := by
  let e : (P →ₗ[R] N) ⊗[R] U ≃ₗ[R] P →ₗ[R] N ⊗[R] U :=
    homTensorFiniteFactorScalarInputEquiv h ≪≫ₗ
      (LinearEquiv.ofBijective
        (rTensorHomToHomRTensor (algebraMap R S) P N U)
        (rTensorHomToHomRTensor_bijective_of_finite_projective
          (algebraMap R S) P N U)).restrictScalars R ≪≫ₗ
      homTensorFiniteFactorScalarOutputEquiv h
  have he : e.toLinearMap = rTensorHomToHomRTensor (.id R) P N U := by
    apply TensorProduct.ext'
    intro f u
    apply LinearMap.ext
    intro p
    rfl
  rw [← he]
  exact e.bijective

/-- Let R,S be commutative rings with an R-algebra structure on S. Let P be an R-module and N,U
modules over R and S with compatible scalar towers r•x=algebraMap(r)•x. All ring and module
universes are independent. If algebraMap:R→S is surjective and U is finitely generated
projective over S, this is the R-linear equivalence Hom_R(P,N)⊗_R U≅Hom_R(P,N⊗_R U). Its forward
map is the canonical contraction χ(f⊗u)(p)=f(p)⊗u, with P retaining only its R-module structure. -/
def homTensorFiniteFactorEquivOfSurjectiveScalars
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (P →ₗ[R] N) ⊗[R] U ≃ₗ[R] P →ₗ[R] N ⊗[R] U :=
  LinearEquiv.ofBijective (rTensorHomToHomRTensor (.id R) P N U)
    (homTensorFiniteFactor_bijective_of_surjective_scalars (P := P) (N := N) (U := U) h)

/-- Let R,S be commutative rings with an R-algebra structure on S. Let P be an R-module and N,U
modules over R and S with compatible scalar towers r•x=algebraMap(r)•x. All ring and module
universes are independent. Assume the algebra map is surjective and U is finitely generated
projective over S. For f∈Hom_R(P,N), u∈U and p∈P, the comparison sends f⊗u to the map whose
value at p is f(p)⊗_R u. The result is in N⊗_R U, over the base ring R. -/
theorem homTensorFiniteFactorEquivOfSurjectiveScalars_tmul
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) (f : P →ₗ[R] N) (u : U) (p : P) :
    homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h
        (f ⊗ₜ[R] u) p = f p ⊗ₜ[R] u :=
  rTensorHomToHomRTensor_apply f u p

/-- Let R,S be commutative rings with an R-algebra structure on S. Let P be an R-module and N,U
modules over R and S with compatible scalar towers r•x=algebraMap(r)•x. All ring and module
universes are independent. Under surjectivity of R→S and finite projectivity of U over S, the
underlying R-linear map of the contraction equivalence is χ:Hom_R(P,N)⊗_R U→Hom_R(P,N⊗_R U),
with χ(f⊗u)(p)=f(p)⊗u. The scalar comparisons identify this precise map. -/
theorem homTensorFiniteFactorEquivOfSurjectiveScalars_toLinearMap
    [Module.Finite S U] [Module.Projective S U]
    (h : Function.Surjective (algebraMap R S)) :
    (homTensorFiniteFactorEquivOfSurjectiveScalars (P := P) (N := N) (U := U) h).toLinearMap =
      rTensorHomToHomRTensor (.id R) P N U := rfl

end TensorProduct
