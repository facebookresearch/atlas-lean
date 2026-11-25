/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ProjectiveRestriction
public import MathlibExt.Algebra.Category.FGModuleCat.RestrictScalarsCoherence
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Finite projective restriction of scalars

A unital ring homomorphism preserves finite projective modules under scalar
restriction when the extension ring is finite projective over the source.
The scalar action and underlying functions are the original restriction of
scalars. Both ring universes are independent of the common module universe.
-/

@[expose] public section
noncomputable section

open CategoryTheory

universe v uR uS

namespace FGProjectiveCat

variable {R : Type uR} {S : Type uS}
variable [Ring R] [Ring S]

/-- Restriction preserves projectivity for finite projective modules when
`S` is projective over `R` through the actual homomorphism `f`. -/
theorem projective_restrictScalars (f : R →+* S)
    (hp : @Module.Projective R _ S _ f.toModule)
    (P : Type v) [AddCommGroup P] [Module S P]
    [Module.Finite S P] [Module.Projective S P] :
    @Module.Projective R _ P _ (Module.compHom P f) := by
  classical
  let : Module R S := f.toModule
  let : Module R P := Module.compHom P f
  let : Module.Projective R S := hp
  obtain ⟨n, q, i, _, _, hi⟩ := Module.Finite.exists_comp_eq_id_of_projective S P
  let e : (Fin n →₀ S) ≃ₗ[R] Π₀ _ : Fin n, S := finsuppLequivDFinsupp R
  let : Module.Projective R (Fin n →₀ S) := Module.Projective.of_equiv' e.symm
  let : Module.Projective R (Fin n → S) :=
    Module.Projective.of_equiv' (Finsupp.linearEquivFunOnFinite R S (Fin n))
  let iR : P →ₗ[R] (Fin n → S) :=
    { toFun := i
      map_add' := i.map_add
      map_smul' := fun r x => i.map_smul (f r) x }
  let qR : (Fin n → S) →ₗ[R] P :=
    { toFun := q
      map_add' := q.map_add
      map_smul' := fun r x => q.map_smul (f r) x }
  apply Module.Projective.of_split iR qR
  ext x
  exact LinearMap.congr_fun hi x

/-- The actual finite scalar-restriction functor on finite projectives. -/
def restrictScalars (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) :
    FGProjectiveCat.{v} S ⥤ FGProjectiveCat.{v} R :=
  projectiveRestriction (FGModuleCat.restrictScalars.{v} f hf)
    (fun P => projective_restrictScalars f hp P)

/-- Restriction retains exactly the original underlying module object. -/
@[simp]
theorem restrictScalars_obj_obj (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (P : FGProjectiveCat.{v} S) :
    ((restrictScalars.{v} f hf hp).obj P).obj =
      (ModuleCat.restrictScalars.{v} f).obj P.obj := rfl

/-- Restriction retains exactly the original underlying module map. -/
@[simp]
theorem restrictScalars_map_hom (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule)
    {P Q : FGProjectiveCat.{v} S} (g : P ⟶ Q) :
    ((restrictScalars.{v} f hf hp).map g).hom =
      (ModuleCat.restrictScalars.{v} f).map g.hom := rfl

/-- Restriction leaves each morphism's underlying function unchanged. -/
theorem restrictScalars_map_apply (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule)
    {P Q : FGProjectiveCat.{v} S} (g : P ⟶ Q) (x : P) :
    (restrictScalars.{v} f hf hp).map g x = g x := rfl

instance restrictScalars_additive (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) :
    (restrictScalars.{v} f hf hp).Additive :=
  projectiveRestrictionAdditive (FGModuleCat.restrictScalars.{v} f hf)
    (fun P => projective_restrictScalars f hp P)

instance restrictScalars_exact (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) :
    (restrictScalars.{v} f hf hp).IsExact :=
  CategoryTheory.ExactCategory.isExact_splitSource (restrictScalars.{v} f hf hp)

/-- The identity extension is projective under its original scalar action. -/
theorem projective_id (R : Type uR) [Ring R] :
    @Module.Projective R _ R _ (RingHom.id R).toModule := by
  infer_instance

/-- Restriction along the identity is the identity finite-projective functor. -/
def restrictScalarsId (R : Type uR) [Ring R] :
    restrictScalars.{v} (RingHom.id R) RingHom.isFinite_id (projective_id R) ≅
      𝟭 (FGProjectiveCat.{v} R) :=
  Functor.fullyFaithfulCancelRight (inclusion R)
    (projectiveRestrictionInclusionIso _ _ ≪≫
      Functor.isoWhiskerLeft (inclusion R) (FGModuleCat.restrictScalarsId.{v} R) ≪≫
      Functor.rightUnitor (inclusion R) ≪≫ (Functor.leftUnitor (inclusion R)).symm)

end FGProjectiveCat

end
