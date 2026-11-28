/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY PROPOSAL. Native verification is UNEXECUTED.
module

public import MathlibExt.Algebra.Category.CommAlgCat.ExtendScalars
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Scalar extension and restriction of commutative algebras

Let `R : Type u` and `S : Type v` be commutative rings and `f : R →+* S`. On algebra carriers
of universe `max u v w`, tensor scalar extension `A ↦ S ⊗_{R,f} A` is left adjoint to
restriction of scalars.

The unit sends `a` to `1 ⊗ a`, and the counit sends `s ⊗ b` to `s·b` in an `S`-algebra `B`.
Their triangle identities give the adjunction correspondence `Hom_S(S ⊗_R A,B) ≅ Hom_R(A,Res_f
B)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct

universe u v w

namespace CommAlgCat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)

/-- Let `R : Type u` and `S : Type v` be commutative rings and `f : R →+* S`. On commutative
algebras of carrier universe `max u v w`, `extendScalars f ⊣ restrictScalars f`. The unit is
`a ↦ 1 ⊗ a`, and the counit is `s ⊗ b ↦ s·b`, giving `Hom_S(S ⊗_R A,B) ≅ Hom_R(A,Res_f B)`. -/
def extendRestrictScalarsAdj :
    extendScalars.{u, v, w} f ⊣ restrictScalars f where
  unit := extendScalarsUnit f
  counit := extendRestrictScalarsCounit f
  left_triangle_components A := by
    letI : Algebra R S := f.toAlgebra
    let B := (extendScalars.{u, v, w} f).obj A
    letI : Algebra R B := restrictedAlgebra f B
    letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
    let e : B →ₐ[S] B :=
      ((extendRestrictScalarsCounit.{u, v, w} f).app B).hom.comp
        ((extendScalars.{u, v, w} f).map ((extendScalarsUnit.{u, v, w} f).app A)).hom
    apply CommAlgCat.hom_ext
    change e = AlgHom.id S B
    apply AlgHom.ext
    intro z
    change e z = z
    induction z using TensorProduct.induction_on with
    | zero => exact e.map_zero
    | tmul s a =>
      have hMap := extendScalars_map_tmul.{u, v, w} f
        ((extendScalarsUnit.{u, v, w} f).app A) s a
      have hCounit := extendRestrictScalarsCounit_tmul.{u, v, w} f B s
        (((extendScalarsUnit.{u, v, w} f).app A).hom a)
      have hUnit := extendScalarsUnit_app.{u, v, w} f A a
      let x : B := (1 : S) ⊗ₜ[R] a
      have hMul : algebraMap S B s * x = (s ⊗ₜ[R] a : B) := by
        change ((s ⊗ₜ[R] (1 : A)) * ((1 : S) ⊗ₜ[R] a)) = s ⊗ₜ[R] a
        simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact (congrArg ((extendRestrictScalarsCounit.{u, v, w} f).app B).hom hMap).trans
        (hCounit.trans ((congrArg (fun x : B => algebraMap S B s * x) hUnit).trans hMul))
    | add x y hx hy =>
      exact (e.map_add x y).trans (congrArg₂ (fun x y : B => x + y) hx hy)
  right_triangle_components B := by
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R B := restrictedAlgebra f B
    letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro b
    change ((extendRestrictScalarsCounit f).app B).hom
      (((extendScalarsUnit f).app ((restrictScalars f).obj B)).hom b) = b
    exact (congrArg ((extendRestrictScalarsCounit f).app B).hom
      (extendScalarsUnit_app f ((restrictScalars f).obj B) b)).trans
        (extendRestrictScalarsCounit_one_tmul f B b)

/-- For commutative rings `R : Type u`, `S : Type v`, and `f : R →+* S`, the functor
`extendScalars.{u,v,w} f` is a left adjoint on carriers of universe `max u v w`. Its right
adjoint is `CommAlgCat.restrictScalars f`. -/
instance extendScalars_isLeftAdjoint : (extendScalars.{u, v, w} f).IsLeftAdjoint :=
  (extendRestrictScalarsAdj f).isLeftAdjoint

/-- For commutative rings `R : Type u`, `S : Type v`, and `f : R →+* S`, `restrictScalars f :
CommAlgCat.{max u v w} S → CommAlgCat.{max u v w} R` is a right adjoint. Its left adjoint is
tensor scalar extension `extendScalars.{u,v,w} f`. -/
instance restrictScalars_isRightAdjoint :
    (restrictScalars f : CommAlgCat.{max u v w} S ⥤ CommAlgCat.{max u v w} R).IsRightAdjoint :=
  (extendRestrictScalarsAdj.{u, v, w} f).isRightAdjoint

end CommAlgCat

end
