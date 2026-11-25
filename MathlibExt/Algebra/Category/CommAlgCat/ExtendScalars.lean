/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY PROPOSAL. Native Lean verification is UNEXECUTED.
module

public import MathlibExt.Algebra.Category.CommAlgCat.RestrictScalars
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Native scalar extension of commutative algebras in independent universes

For the original ring homomorphism R to S, use the original action on S
and the native algebra tensor product S tensor_R P. Native tensor maps
are S-linear in the left factor, so their functor laws require no new
carrier model, flatness or universe-equality premise.

The native right tensor inclusion gives the actual unit. The native
algebra tensor universal map gives the actual counit over every original
S-algebra. Their pure-tensor formula retains the original scalar and
algebra element and earns the original one-tensor point identity.
Every proposed declaration is UNEXECUTED.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace CommAlgCat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

section OfAlgebra

variable (R S) [Algebra R S]

/-- The native tensor functor for an actual structural algebra, with all carrier worlds explicit. -/
def extendScalarsOfAlgebra :
    CommAlgCat.{max u v w} R ⥤ CommAlgCat.{max u v w} S :=
  { obj P := CommAlgCat.of S (S ⊗[R] P)
    map g := { hom' := Algebra.TensorProduct.map (AlgHom.id S S) g.hom }
    map_id P := by
      apply CommAlgCat.hom_ext
      change Algebra.TensorProduct.map (AlgHom.id S S) (AlgHom.id R P) = AlgHom.id S _
      exact Algebra.TensorProduct.map_id
    map_comp g h := by
      apply CommAlgCat.hom_ext
      change Algebra.TensorProduct.map (AlgHom.id S S) (h.hom.comp g.hom) =
        (Algebra.TensorProduct.map (AlgHom.id S S) h.hom).comp
          (Algebra.TensorProduct.map (AlgHom.id S S) g.hom)
      exact Algebra.TensorProduct.map_id_comp h.hom g.hom }

end OfAlgebra

/-- Scalar extension along a ring map uses the single native tensor functor. -/
def extendScalars (f : R →+* S) :
    CommAlgCat.{max u v w} R ⥤ CommAlgCat.{max u v w} S := by
  letI : Algebra R S := f.toAlgebra
  exact extendScalarsOfAlgebra.{u, v, w} R S

/-- The original algebra action and its structural map give the same generic tensor functor. -/
theorem extendScalars_algebraMap [Algebra R S] :
    extendScalars.{u, v, w} (algebraMap R S) = extendScalarsOfAlgebra.{u, v, w} R S := by
  unfold extendScalars
  rw [toAlgebra_algebraMap]

theorem extendScalars_map_tmul (f : R →+* S)
    {P Q : CommAlgCat.{max u v w} R} (g : P ⟶ Q) (s : S) (p : P) :
    letI : Algebra R S := f.toAlgebra
    ((extendScalars.{u, v, w} f).map g).hom (s ⊗ₜ[R] p) = s ⊗ₜ[R] g.hom p := by
  letI : Algebra R S := f.toAlgebra
  rfl

/-- The native right tensor inclusion, on the original augmented algebra carrier. -/
def extendScalarsUnit (f : R →+* S) :
    𝟭 (CommAlgCat.{max u v w} R) ⟶
      extendScalars.{u, v, w} f ⋙ restrictScalars f := by
  letI : Algebra R S := f.toAlgebra
  exact
    { app P :=
        { hom' :=
          { toRingHom := (Algebra.TensorProduct.includeRight : P →ₐ[R] S ⊗[R] P).toRingHom
            commutes' r := by
              exact (RingHom.congr_fun
                (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
                  (R := R) (A := S) (B := P)) r).symm } }
      naturality {P Q} g := by
        apply CommAlgCat.hom_ext
        ext p
        rfl }

@[simp]
theorem extendScalarsUnit_app (f : R →+* S)
    (P : CommAlgCat.{max u v w} R) (p : P) :
    letI : Algebra R S := f.toAlgebra
    ((extendScalarsUnit.{u, v, w} f).app P).hom p = (1 : S) ⊗ₜ[R] p := by
  letI : Algebra R S := f.toAlgebra
  rfl

/-- Native multiplication of the scalar and original algebra element gives the actual counit. -/
def extendRestrictScalarsCounit (f : R →+* S) :
    restrictScalars f ⋙ extendScalars.{u, v, w} f ⟶ 𝟭 (CommAlgCat.{max u v w} S) := by
  letI : Algebra R S := f.toAlgebra
  refine
    { app B := ?_
      naturality := ?_ }
  · letI : Algebra R B := restrictedAlgebra f B
    letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
    let ε : S ⊗[R] B →ₐ[S] B :=
      Algebra.TensorProduct.lift (R := R) (S := S) (A := S) (B := B) (C := B)
        (Algebra.ofId S B) (AlgHom.id R B) (fun s b => Commute.all _ _)
    exact CommAlgCat.ofHom ε
  · intro B C g
    letI : Algebra R B := restrictedAlgebra f B
    letI : Algebra R C := restrictedAlgebra f C
    letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' rfl
    let l : S ⊗[R] B →ₐ[S] C :=
      (Algebra.TensorProduct.lift (R := R) (S := S) (A := S) (B := C) (C := C)
        (Algebra.ofId S C) (AlgHom.id R C) (fun s c => Commute.all _ _)).comp
          (Algebra.TensorProduct.map (AlgHom.id S S) ((restrictScalars f).map g).hom)
    let t : S ⊗[R] B →ₐ[S] C :=
      g.hom.comp (Algebra.TensorProduct.lift (R := R) (S := S) (A := S) (B := B) (C := B)
        (Algebra.ofId S B) (AlgHom.id R B) (fun s b => Commute.all _ _))
    apply CommAlgCat.hom_ext
    change l = t
    apply AlgHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact l.map_zero.trans t.map_zero.symm
    | tmul s b =>
      change algebraMap S C s * g.hom b = g.hom (algebraMap S B s * b)
      exact (congrArg (fun a => a * g.hom b) (g.hom.commutes s).symm).trans
        (g.hom.map_mul _ _).symm
    | add z z' hz hz' =>
      exact (l.map_add z z').trans
        ((congrArg₂ (fun x y : C => x + y) hz hz').trans (t.map_add z z').symm)

theorem extendRestrictScalarsCounit_tmul (f : R →+* S)
    (B : CommAlgCat.{max u v w} S) (s : S) (b : B) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R B := restrictedAlgebra f B
    ((extendRestrictScalarsCounit.{u, v, w} f).app B).hom (s ⊗ₜ[R] b) =
      algebraMap S B s * b := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R B := restrictedAlgebra f B
  letI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  change (Algebra.TensorProduct.lift (R := R) (S := S) (A := S) (B := B) (C := B)
    (Algebra.ofId S B) (AlgHom.id R B) (fun s b => Commute.all _ _)) (s ⊗ₜ[R] b) = _
  exact Algebra.TensorProduct.lift_tmul _ _ _ s b

@[simp]
theorem extendRestrictScalarsCounit_one_tmul (f : R →+* S)
    (B : CommAlgCat.{max u v w} S) (b : B) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R B := restrictedAlgebra f B
    ((extendRestrictScalarsCounit.{u, v, w} f).app B).hom ((1 : S) ⊗ₜ[R] b) = b := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R B := restrictedAlgebra f B
  rw [extendRestrictScalarsCounit_tmul, map_one, one_mul]

end CommAlgCat

end
