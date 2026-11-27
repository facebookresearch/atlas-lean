/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.AutomorphismRestriction
public import MathlibExt.Algebra.Category.FGProjectiveCat.NatIsoFromRegular
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts

/-!
# Actual scalar extension after finite projective restriction

The native counit and native automorphism unit form a natural map to the
original projective and its automorphism scalar extension. An actual
coefficient tensor decomposition proves the regular component is an
isomorphism; finite-free presentations and projective retracts extend it.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u

namespace FGProjectiveCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The original extension/restriction counit on finite projectives. -/
def baseChangeRestrictScalarsCounit (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) :
    restrictScalars f hf hp ⋙ baseChange f ⟶ 𝟭 (FGProjectiveCat.{u} S) where
  app P := ObjectProperty.homMk ((ModuleCat.extendRestrictScalarsAdj f).counit.app P.obj)
  naturality P Q g := by
    apply ObjectProperty.hom_ext
    exact (ModuleCat.extendRestrictScalarsAdj f).counit.naturality g.hom

/-- The counit retains the original tensor unit on every module element. -/
theorem baseChangeRestrictScalarsCounit_unit (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (P : FGProjectiveCat.{u} S) (p : P) :
    (baseChangeRestrictScalarsCounit f hf hp).app P ((1 : S) ⊗ₜ[R,f] p) = p := by
  change (ModuleCat.extendRestrictScalarsAdj f).counit.app P.obj ((1 : S) ⊗ₜ[R,f] p) = p
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul f P.obj p

/-- The adjoint of the inverse native automorphism-restriction comparison. -/
def baseChangeRestrictScalarsAutomorphismMap (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) :
    restrictScalars f hf hp ⋙ baseChange f ⟶ baseChange σ.toRingHom :=
  Functor.whiskerRight (baseChangeAutomorphismRestrictScalarsIso f hf hp σ hσ).inv
      (baseChange f) ≫
    (Functor.associator (baseChange σ.toRingHom) (restrictScalars f hf hp)
      (baseChange f)).hom ≫
    Functor.whiskerLeft (baseChange σ.toRingHom) (baseChangeRestrictScalarsCounit f hf hp) ≫
    (Functor.rightUnitor (baseChange σ.toRingHom)).hom

/-- The adjoint comparison keeps the original automorphism extension unit. -/
theorem baseChangeRestrictScalarsAutomorphismMap_unit
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f) (P : FGProjectiveCat.{u} S) (p : P) :
    (baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P
        ((1 : S) ⊗ₜ[R,f] p) =
      (show (baseChange σ.toRingHom).obj P from
        (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app P.obj p) := by
  change (ModuleCat.extendRestrictScalarsAdj f).counit.app
      ((ModuleCat.extendScalars σ.toRingHom).obj P.obj)
      ((ModuleCat.extendScalars f).map
        ((ModuleCat.automorphismRestrictionIso f σ hσ).inv.app P.obj)
        ((1 : S) ⊗ₜ[R,f] p)) = _
  change (ModuleCat.extendRestrictScalarsAdj f).counit.app
      ((ModuleCat.extendScalars σ.toRingHom).obj P.obj)
      ((1 : S) ⊗ₜ[R,f]
        ((ModuleCat.automorphismRestrictionIso f σ hσ).inv.app P.obj p)) = _
  have h := ModuleCat.automorphismRestrictionLinearEquiv_symm_apply f σ hσ P.obj p
  change (ModuleCat.automorphismRestrictionIso f σ hσ).inv.app P.obj p = _ at h
  rw [h]
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul f _ _

/-- The native pointwise biproduct of identity and automorphism base change. -/
def baseChangeAutomorphismBiprodFunctor (σ : S ≃+* S) :
    FGProjectiveCat.{u} S ⥤ FGProjectiveCat.{u} S :=
  (pointwiseBinaryBicone (𝟭 (FGProjectiveCat.{u} S)) (baseChange σ.toRingHom)).pt

instance baseChangeAutomorphismBiprodFunctor_additive (σ : S ≃+* S) :
    (baseChangeAutomorphismBiprodFunctor σ).Additive where
  map_add {X Y g h} := by
    change biprod.map (g + h) ((baseChange σ.toRingHom).map (g + h)) =
      biprod.map g ((baseChange σ.toRingHom).map g) +
        biprod.map h ((baseChange σ.toRingHom).map h)
    apply biprod.hom_ext <;>
      simp only [biprod.map_fst, biprod.map_snd, Functor.map_add,
        Preadditive.add_comp, Preadditive.comp_add]

/-- The two actual native maps into the original projective biproduct. -/
def baseChangeRestrictScalarsDecompositionMap (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (σ : S ≃+* S)
    (hσ : σ.toRingHom.comp f = f) :
    restrictScalars f hf hp ⋙ baseChange f ⟶ baseChangeAutomorphismBiprodFunctor σ where
  app P := biprod.lift ((baseChangeRestrictScalarsCounit f hf hp).app P)
    ((baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P)
  naturality P Q g := by
    dsimp only [baseChangeAutomorphismBiprodFunctor, pointwiseBinaryBicone]
    apply biprod.hom_ext
    · simpa only [Category.assoc, biprod.lift_fst, biprod.lift_fst_assoc, biprod.map_fst,
        Functor.id_map] using (baseChangeRestrictScalarsCounit f hf hp).naturality g
    · simpa only [Category.assoc, biprod.lift_snd, biprod.lift_snd_assoc, biprod.map_snd]
        using (baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).naturality g

/-- The original automorphism extension of the regular module is identified
with that same regular module by the native inverse-restriction bridge. -/
def baseChangeAutomorphismRegularIso (σ : S ≃+* S) :
    (baseChange σ.toRingHom).obj (regular S) ≅ regular S :=
  (ModuleCat.isFGProjective S).isoMk
    ((ModuleCat.automorphismExtendRestrictIso σ).app (ModuleCat.of S S) ≪≫
      ModuleCat.restrictScalarsIsoOfEquiv σ.symm)

/-- The native regular comparison sends its tensor unit to σ of the element. -/
theorem baseChangeAutomorphismRegularIso_unit (σ : S ≃+* S) (p : S) :
    (baseChangeAutomorphismRegularIso σ).hom
        (show (baseChange σ.toRingHom).obj (regular S) from
          (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app (ModuleCat.of S S) p) =
      σ p := by
  change (ModuleCat.restrictScalarsIsoOfEquiv σ.symm).hom
    ((ModuleCat.automorphismExtendRestrictIso σ).hom.app (ModuleCat.of S S)
      ((ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app (ModuleCat.of S S) p)) = _
  rw [ModuleCat.automorphismExtendRestrictIso_hom_unit]
  rfl

/-- The first actual map sends every native pure tensor to its scalar action. -/
theorem baseChangeRestrictScalarsCounit_pure (f : R →+* S) (hf : f.IsFinite)
    (hp : @Module.Projective R _ S _ f.toModule) (P : FGProjectiveCat.{u} S)
    (z : S) (p : P) :
    (baseChangeRestrictScalarsCounit f hf hp).app P (z ⊗ₜ[R,f] p) = z • p := by
  let M := (restrictScalars f hf hp ⋙ baseChange f).obj P
  let : Module R P := Module.compHom P f
  let : Module S M := M.obj.isModule
  let unitPoint : M := (1 : S) ⊗ₜ[R,f] p
  have ht : (z • unitPoint : M) = z ⊗ₜ[R,f] p := by
    change (z * 1) ⊗ₜ[R,f] p = z ⊗ₜ[R,f] p
    rw [mul_one]
  calc
    _ = (baseChangeRestrictScalarsCounit f hf hp).app P
        (z • unitPoint : M) := congrArg _ ht.symm
    _ = z • (baseChangeRestrictScalarsCounit f hf hp).app P unitPoint :=
      ((baseChangeRestrictScalarsCounit f hf hp).app P).hom.hom.map_smul z _
    _ = z • p := congrArg (fun q : P => z • q)
      (baseChangeRestrictScalarsCounit_unit f hf hp P p)

/-- The second actual map keeps every native automorphism unit and left scalar. -/
theorem baseChangeRestrictScalarsAutomorphismMap_pure
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f) (P : FGProjectiveCat.{u} S)
    (z : S) (p : P) :
    (baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P (z ⊗ₜ[R,f] p) =
      z • (show (baseChange σ.toRingHom).obj P from
        (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app P.obj p) := by
  let M := (restrictScalars f hf hp ⋙ baseChange f).obj P
  let : Module R P := Module.compHom P f
  let : Module S M := M.obj.isModule
  let unitPoint : M := (1 : S) ⊗ₜ[R,f] p
  have ht : (z • unitPoint : M) = z ⊗ₜ[R,f] p := by
    change (z * 1) ⊗ₜ[R,f] p = z ⊗ₜ[R,f] p
    rw [mul_one]
  calc
    _ = (baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P
        (z • unitPoint : M) := congrArg _ ht.symm
    _ = z • (baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P
        unitPoint :=
      ((baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P).hom.hom.map_smul z _
    _ = _ := congrArg (fun q : (baseChange σ.toRingHom).obj P => z • q)
      (baseChangeRestrictScalarsAutomorphismMap_unit f hf hp σ hσ P p)

/-- Both native component maps are retained in the original biproduct coordinates. -/
theorem baseChangeRestrictScalarsDecompositionMap_coordinates
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f) (P : FGProjectiveCat.{u} S)
    (t : (restrictScalars f hf hp ⋙ baseChange f).obj P) :
    biprodCarrierLinearEquiv P ((baseChange σ.toRingHom).obj P)
        ((baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app P t) =
      ((baseChangeRestrictScalarsCounit f hf hp).app P t,
        (baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P t) := by
  change biprodCarrierLinearEquiv P ((baseChange σ.toRingHom).obj P)
    ((biprod.lift ((baseChangeRestrictScalarsCounit f hf hp).app P)
      ((baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P)) t) = _
  have hfst : (baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app P ≫
      (biprod.fst : P ⊞ (baseChange σ.toRingHom).obj P ⟶ P) =
      (baseChangeRestrictScalarsCounit f hf hp).app P := biprod.lift_fst _ _
  have hsnd : (baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app P ≫
      (biprod.snd : P ⊞ (baseChange σ.toRingHom).obj P ⟶ (baseChange σ.toRingHom).obj P) =
      (baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app P := biprod.lift_snd _ _
  apply Prod.ext
  · rw [biprodCarrierLinearEquiv_apply_fst]
    exact congrArg (fun g : (restrictScalars f hf hp ⋙ baseChange f).obj P ⟶ P =>
      g.hom.hom t) hfst
  · rw [biprodCarrierLinearEquiv_apply_snd]
    exact congrArg (fun g : (restrictScalars f hf hp ⋙ baseChange f).obj P ⟶
      (baseChange σ.toRingHom).obj P => g.hom.hom t) hsnd

/-- The regular comparison retains σ on the second tensor factor and the
original scalar-linear action on the first. -/
theorem baseChangeAutomorphismRegularIso_pure (σ : S ≃+* S) (z p : S) :
    (baseChangeAutomorphismRegularIso σ).hom
        (z • (show (baseChange σ.toRingHom).obj (regular S) from
          (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app (ModuleCat.of S S) p)) =
      z * σ p := by
  calc
    _ = z • (baseChangeAutomorphismRegularIso σ).hom
        (show (baseChange σ.toRingHom).obj (regular S) from
          (ModuleCat.extendRestrictScalarsAdj σ.toRingHom).unit.app (ModuleCat.of S S) p) :=
      (baseChangeAutomorphismRegularIso σ).hom.hom.hom.map_smul z _
    _ = z • σ p := congrArg (fun q : S => z • q) (baseChangeAutomorphismRegularIso_unit σ p)
    _ = z * σ p := rfl

/-- Native biproduct and regular comparison coordinates for the regular component. -/
def baseChangeRestrictScalarsRegularCoordinates (σ : S ≃+* S) :
    (baseChangeAutomorphismBiprodFunctor σ).obj (regular S) ≃ₗ[S] S × S :=
  (biprodCarrierLinearEquiv (regular S) ((baseChange σ.toRingHom).obj (regular S))).trans
    ((LinearEquiv.refl S S).prodCongr (isoToLinearEquiv (baseChangeAutomorphismRegularIso σ)))

/-- The actual regular component is multiplication and σ multiplication on pure tensors. -/
theorem baseChangeRestrictScalarsRegularCoordinates_tmul
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f) (z w : S) :
    baseChangeRestrictScalarsRegularCoordinates σ
        ((baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app (regular S)
          (z ⊗ₜ[R,f] w)) = (z * w, z * σ w) := by
  let : Module R S := f.toModule
  have hc := baseChangeRestrictScalarsDecompositionMap_coordinates f hf hp σ hσ (regular S)
    (z ⊗ₜ[R,f] w)
  have hcoords := congrArg (fun p : regular S × (baseChange σ.toRingHom).obj (regular S) =>
    (p.1, (baseChangeAutomorphismRegularIso σ).hom p.2)) hc
  calc
    _ = ((baseChangeRestrictScalarsCounit f hf hp).app (regular S) (z ⊗ₜ[R,f] w),
        (baseChangeAutomorphismRegularIso σ).hom
          ((baseChangeRestrictScalarsAutomorphismMap f hf hp σ hσ).app (regular S)
            (z ⊗ₜ[R,f] w))) := hcoords
    _ = _ := Prod.ext (baseChangeRestrictScalarsCounit_pure f hf hp (regular S) z w)
      ((congrArg (baseChangeAutomorphismRegularIso σ).hom
        (baseChangeRestrictScalarsAutomorphismMap_pure f hf hp σ hσ (regular S) z w)).trans
        (baseChangeAutomorphismRegularIso_pure σ z w))

/-- An actual coefficient tensor equivalence proves the original regular
component is an isomorphism. Only the coefficient decomposition is an input. -/
theorem baseChangeRestrictScalarsDecompositionMap_isIso_regular
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f)
    (e : (restrictScalars f hf hp ⋙ baseChange f).obj (regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) :
    IsIso ((baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app (regular S)) := by
  let : Module R S := f.toModule
  let C := baseChangeRestrictScalarsRegularCoordinates σ
  let L := e.trans C.symm
  have h : (baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app (regular S) =
      (isoOfLinearEquiv L).hom := by
    apply ObjectProperty.hom_ext
    apply ModuleCat.ExtendScalars.hom_ext
    intro w
    change S at w
    apply C.injective
    change C ((baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app (regular S)
      ((1 : S) ⊗ₜ[R,f] w)) = C (L ((1 : S) ⊗ₜ[R,f] w))
    calc
      _ = (1 * w, 1 * σ w) :=
        baseChangeRestrictScalarsRegularCoordinates_tmul f hf hp σ hσ 1 w
      _ = e ((1 : S) ⊗ₜ[R,f] w) := (he 1 w).symm
      _ = C (L ((1 : S) ⊗ₜ[R,f] w)) := (C.apply_symm_apply _).symm
  rw [h]
  infer_instance

/-- The actual native decomposition becomes a whole natural isomorphism
through finite-free presentations and original projective retracts. -/
def baseChangeRestrictScalarsDecompositionIso
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f)
    (e : (restrictScalars f hf hp ⋙ baseChange f).obj (regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) :
    restrictScalars f hf hp ⋙ baseChange f ≅ baseChangeAutomorphismBiprodFunctor σ := by
  letI : IsIso ((baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ).app (regular S)) :=
    baseChangeRestrictScalarsDecompositionMap_isIso_regular f hf hp σ hσ e he
  exact natIsoOfRegular (baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ)

/-- The earned isomorphism has exactly the original native forward map. -/
@[simp]
theorem baseChangeRestrictScalarsDecompositionIso_hom
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f)
    (e : (restrictScalars f hf hp ⋙ baseChange f).obj (regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) :
    (baseChangeRestrictScalarsDecompositionIso f hf hp σ hσ e he).hom =
      baseChangeRestrictScalarsDecompositionMap f hf hp σ hσ := rfl

/-- Each original projective scalar extension of restriction is its original
biproduct with its automorphism scalar extension. -/
def baseChangeRestrictScalarsBiprodIso
    (f : R →+* S) (hf : f.IsFinite) (hp : @Module.Projective R _ S _ f.toModule)
    (σ : S ≃+* S) (hσ : σ.toRingHom.comp f = f)
    (e : (restrictScalars f hf hp ⋙ baseChange f).obj (regular S) ≃ₗ[S] S × S)
    (he : ∀ z w : S, e (z ⊗ₜ[R,f] w) = (z * w, z * σ w)) (P : FGProjectiveCat.{u} S) :
    (baseChange f).obj ((restrictScalars f hf hp).obj P) ≅
      P ⊞ (baseChange σ.toRingHom).obj P :=
  (baseChangeRestrictScalarsDecompositionIso f hf hp σ hσ e he).app P

end FGProjectiveCat

end
