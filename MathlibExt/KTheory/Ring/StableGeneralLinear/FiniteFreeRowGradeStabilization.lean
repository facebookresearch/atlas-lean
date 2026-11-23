/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowCoreHomology
public import MathlibExt.KTheory.Ring.K0.FiniteFreeCofinality
public import MathlibExt.CategoryTheory.Monoidal.SInverseSCoreGrade

/-!
# Actual free stabilization of every component in a finite-free K0 grade

An object in the rank-n free K0 grade becomes isomorphic to that free
object after adding the SAME derived finite free summand. Categorical
component connectedness then factors the entire translated component
through the actual rank-(n+k) free component. The derived finite-row
homology Iso supplies an original finite-GL class for every translated
component class, in every degree.

Only the specified free K0 grade is used here. An arbitrary denominator
is regularized separately through its actual finite-free complement.
-/

noncomputable section

open CategoryTheory Limits Algebra

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- Every actual categorical component in the free-n K0 grade, after a
derived free-k left translation, factors through the literal free-(n+k)
core component. The whole underlying functor is retained. -/
public theorem finiteFreeRowGradeComponent_exists_stabilizedFunctor (n : ℕ)
    (c : CategoryTheory.ConnectedComponents
      (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
        (GrothendieckAddGroup.of
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))))) :
    ∃ (k : ℕ) (F : c.Component ⥤
      (CategoryTheory.ConnectedComponents.mk
        (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (n + k)))).Component),
      F ⋙ CategoryTheory.ConnectedComponents.ι
          (CategoryTheory.ConnectedComponents.mk
            (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (n + k)))) =
        CategoryTheory.ConnectedComponents.ι c ⋙
          (SInverseS.coreGradeProperty (C := FGProjectiveCat.IdempotentModel R)
            (GrothendieckAddGroup.of
              (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))).ι ⋙
          SInverseS.coreLeftTranslationFunctor
            ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k) := by
  let C := FGProjectiveCat.IdempotentModel R
  let free := fun k : ℕ => (Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k
  let g := GrothendieckAddGroup.of (toSkeleton (free n))
  let X₀ : c.Component := Classical.choice inferInstance
  let P : C := X₀.obj.obj.of
  have hClass : GrothendieckAddGroup.of (toSkeleton P) = g := X₀.obj.property
  have hDifference : (SInverseS.Pair.mk P (free n)).difference = 0 := by
    change GrothendieckAddGroup.of (toSkeleton P) -
      GrothendieckAddGroup.of (toSkeleton (free n)) = 0
    rw [hClass]
    exact sub_self g
  obtain ⟨k, ⟨e⟩⟩ :=
    (RingK0.idempotentPair_zeroDifference_iff_exists_same_free_stabilization
      R P (free n)).mp hDifference
  let F₀ : c.Component ⥤ Core C :=
    CategoryTheory.ConnectedComponents.ι c ⋙ (SInverseS.coreGradeProperty (C := C) g).ι
  let hF₀ : F₀.FullyFaithful :=
    (c.objectProperty.fullyFaithfulι).comp
      (SInverseS.coreGradeProperty (C := C) g).fullyFaithfulι
  letI : Groupoid c.Component := Groupoid.ofFullyFaithfulToGroupoid F₀ hF₀
  let T := SInverseS.coreLeftTranslationFunctor (free k)
  let L : c.Component ⥤ Core C := F₀ ⋙ T
  let target := CategoryTheory.ConnectedComponents.mk (Core.mk (free (n + k)))
  let e₀ : free k ⊞ P ≅ free (n + k) :=
    biprod.braiding (free k) P ≪≫ e ≪≫
      (FGProjectiveCat.IdempotentModel.freeBiprodIso R n k).symm
  have hObjects (X : c.Component) : target.objectProperty (L.obj X) := by
    obtain ⟨a⟩ := nonempty_hom_of_preconnected_groupoid X₀ X
    have hBase : (L.obj X₀).of = (free k ⊞ P) :=
      SInverseS.coreLeftTranslationFunctor_obj_of (free k) (F₀.obj X₀)
    let eX : free (n + k) ≅ (L.obj X).of :=
      e₀.symm ≪≫ (eqToIso hBase).symm ≪≫ (T.map (F₀.map a)).iso
    exact (finiteFreeRowCore_isoclass_iff_component R (n + k) (L.obj X)).mp ⟨eX⟩
  let F : c.Component ⥤ target.Component := ObjectProperty.lift target.objectProperty L hObjects
  refine ⟨k, F, ?_⟩
  change ObjectProperty.lift target.objectProperty L hObjects ⋙ target.ι = L
  rfl

/-- EVERY homology class from an actual component of the free-n K0 grade,
after its derived free translation, is the image of an ORIGINAL finite
opposite-GL stage class. No homology/image witness is an input. -/
public theorem finiteFreeRowGradeComponent_homology_exists_stage
    (A : AddCommGrpCat.{u}) (q n : ℕ)
    (c : CategoryTheory.ConnectedComponents
      (SInverseS.CoreGrade (C := FGProjectiveCat.IdempotentModel R)
        (GrothendieckAddGroup.of
          (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))))
    (x : (nerve c.Component).homology (C := AddCommGrpCat.{u}) A q) :
    ∃ (k : ℕ)
      (y : (nerve (SingleObj (Matrix.GeneralLinearGroup (Fin (n + k)) R)ᵐᵒᵖ)).homology
        (C := AddCommGrpCat.{u}) A q),
      SSet.homologyMap (C := AddCommGrpCat.{u}) (finiteFreeRowStageCoreNerveMap R (n + k)) A q y =
        SSet.homologyMap (C := AddCommGrpCat.{u})
          (nerveMap (CategoryTheory.ConnectedComponents.ι c ⋙
            (SInverseS.coreGradeProperty (C := FGProjectiveCat.IdempotentModel R)
              (GrothendieckAddGroup.of
                (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n)))).ι ⋙
            SInverseS.coreLeftTranslationFunctor
              ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k))) A q x := by
  obtain ⟨k, F, hF⟩ := finiteFreeRowGradeComponent_exists_stabilizedFunctor R n c
  let C := FGProjectiveCat.IdempotentModel R
  let g := GrothendieckAddGroup.of
    (toSkeleton ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj n))
  let L := CategoryTheory.ConnectedComponents.ι c ⋙ (SInverseS.coreGradeProperty (C := C) g).ι ⋙
    SInverseS.coreLeftTranslationFunctor
      ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj k)
  let J := CategoryTheory.ConnectedComponents.ι
    (CategoryTheory.ConnectedComponents.mk
      (Core.mk ((Idempotents.toKaroubi (FGProjectiveCat.FiniteRowRanks R)).obj (n + k))))
  let e := finiteFreeRowCoreComponentHomologyIso R A q (n + k)
  let z := SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap F) A q x
  let y := e.inv z
  have hStage : SSet.homologyMap (C := AddCommGrpCat.{u})
    (finiteFreeRowStageCoreNerveMap R (n + k)) A q =
      e.hom ≫ SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap J) A q := by
    have h := (congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u}) f A q)
      (finiteFreeRowCoreComponentNerveMap_comp_inclusion R (n + k))).symm.trans
        ((SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q).map_comp
          (finiteFreeRowCoreComponentNerveMap R (n + k)) (nerveMap J))
    exact h.trans (congrArg (fun f => f ≫ SSet.homologyMap (C := AddCommGrpCat.{u})
      (nerveMap J) A q)
      (finiteFreeRowCoreComponentHomologyIso_hom R A q (n + k)).symm)
  have hNerve : nerveMap F ≫ nerveMap J = nerveMap L :=
    (nerveMap_comp F J).trans (congrArg nerveMap hF)
  have hTarget : SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap J) A q z =
      SSet.homologyMap (C := AddCommGrpCat.{u}) (nerveMap L) A q x :=
    ConcreteCategory.congr_hom
      (((SSet.homologyFunctor (C := AddCommGrpCat.{u})
        A q).map_comp (nerveMap F) (nerveMap J)).symm.trans
        (congrArg (fun f => SSet.homologyMap (C := AddCommGrpCat.{u}) f A q) hNerve)) x
  refine ⟨k, y, ?_⟩
  exact (ConcreteCategory.congr_hom hStage y).trans
    ((congrArg (SSet.homologyMap (C := AddCommGrpCat.{u})
      (nerveMap J) A q) (Iso.inv_hom_id_apply e z)).trans hTarget)

end AlgebraicKTheory.StableGL
