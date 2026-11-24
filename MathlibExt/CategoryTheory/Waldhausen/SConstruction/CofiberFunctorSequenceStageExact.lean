/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeStageTransposeExact
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenNatTrans
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FunctorSequencePrecomposition

/-!
# Stage stability of the original cofiber functor-sequence condition

The original exact cofiber lift acts on the actual source stages and
then on the full relative cofiber-stage transpose. Precomposition of the
internally earned universal stage triangle gives the complete staged
sequence, including its original pushout base condition.

The three stage functors and both stage natural transformations retain
the original source sequence. No gluing or target sequence outcome is
an input. All four source/target object/Hom universe roles are independent.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

universe uD vD uC vC uA vA uB vB

namespace CategoryTheory.Waldhausen.SConstruction

private theorem stageSequenceFunctor_eq
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    (P : ObjectProperty B) (F G : A ⥤ P.FullSubcategory)
    (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  have hobj (X : A) : F.obj X = G.obj X := by
    apply ObjectProperty.FullSubcategory.ext
    exact Functor.congr_obj h X
  refine Functor.ext hobj ?_
  intro X Y f
  apply P.fullyFaithfulι.map_injective
  simp only [Functor.map_comp, eqToHom_map]
  exact Functor.congr_hom h f

private theorem stageSequenceNatTransHExt
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (h : ∀ X : A, HEq (α.app X) (β.app X)) :
    HEq α β := by
  cases hF
  cases hG
  apply heq_of_eq
  apply NatTrans.ext
  funext X
  exact eq_of_heq (h X)

private theorem stageSequenceHomHEq
    {B : Type uB} [Category.{vB} B] (P : ObjectProperty B)
    {X Y X' Y' : P.FullSubcategory} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f.hom g.hom) : HEq f g := by
  cases hX
  cases hY
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  exact eq_of_heq h

private theorem stageMapFunctor_eq
    {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {F G : A ⥤ B} (h : F = G) (hF : F.IsWaldhausenExact)
    (hG : G.IsWaldhausenExact) (n : ℕ) : hF.mapStage n = hG.mapStage n := by
  cases h
  rfl

private theorem stageSequence_of_heq
    {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {F₀ F₁ F₂ G₀ G₁ G₂ : A ⥤ B}
    (h₀ : F₀ = G₀) (h₁ : F₁ = G₁) (h₂ : F₂ = G₂)
    (i : F₀ ⟶ F₁) (p : F₁ ⟶ F₂) (i' : G₀ ⟶ G₁) (p' : G₁ ⟶ G₂)
    (hi : HEq i i') (hp : HEq p p')
    (H : IsWaldhausenCofiberFunctorSequence F₀ F₁ F₂ i p) :
    IsWaldhausenCofiberFunctorSequence G₀ G₁ G₂ i' p' := by
  cases h₀
  cases h₁
  cases h₂
  cases hi
  cases hp
  exact H

private theorem stageSequence_precomp
    {A : Type uA} [Category.{vA} A] [HasZeroObject A] [WaldhausenCategoryWithoutGluing A]
    {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
    (G : A ⥤ B) (hG : G.IsWaldhausenExact)
    {F₀ F₁ F₂ : B ⥤ C} {i : F₀ ⟶ F₁} {p : F₁ ⟶ F₂}
    (H : IsWaldhausenCofiberFunctorSequence F₀ F₁ F₂ i p) :
    IsWaldhausenCofiberFunctorSequence (G ⋙ F₀) (G ⋙ F₁) (G ⋙ F₂)
      (Functor.whiskerLeft G i) (Functor.whiskerLeft G p) := by
  refine ⟨hG.comp H.sourceExact, hG.comp H.middleExact, hG.comp H.quotientExact,
    fun X => H.objectwise (G.obj X), ?_⟩
  intro X Y f hf
  exact H.baseCofibration (G.map f) (hG.map_cofibration f hf)

namespace IsWaldhausenCofiberFunctorSequence

variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {F₀ F₁ F₂ : D ⥤ C} {i : F₀ ⟶ F₁} {p : F₁ ⟶ F₂}
variable (H : IsWaldhausenCofiberFunctorSequence F₀ F₁ F₂ i p)

/-- The original relative Waldhausen value on the lifted target cofiber category. -/
local instance originalRelativeWaldhausen : WaldhausenCategoryWithoutGluing
    (CofiberSequenceCategory C) :=
  CofiberSequenceCategory.relativeWaldhausenCategory C

local instance originalSourceStageZero (n : ℕ) : HasZeroObject (Stage D n) :=
  generalStageHasZeroObject D n

/-- The original general Waldhausen value on each source finite stage. -/
local instance originalSourceStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing
    (Stage D n) :=
  generalStageWaldhausenCategory D n

local instance originalTargetStageZero (n : ℕ) : HasZeroObject (Stage C n) :=
  generalStageHasZeroObject C n

/-- The original general Waldhausen value on each target finite stage. -/
local instance originalTargetStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing
    (Stage C n) :=
  generalStageWaldhausenCategory C n

local instance originalRelativeStageZero (n : ℕ) :
    HasZeroObject (Stage (CofiberSequenceCategory C) n) :=
  generalStageHasZeroObject (CofiberSequenceCategory C) n

/-- The original general stage value over the lifted target relative cofiber category. -/
local instance originalRelativeStageWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (Stage (CofiberSequenceCategory C) n) :=
  generalStageWaldhausenCategory (CofiberSequenceCategory C) n

/-- The original relative cofiber value over each target general stage category. -/
local instance originalStageRelativeWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C n)) :=
  CofiberSequenceCategory.relativeWaldhausenCategory (Stage C n)

private theorem triangleStageFunctor_eq (n : ℕ) (t : Fin 3) :
    (CofiberSequenceCategory.stageEvaluationTriangle C n).obj t =
      (CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C t).mapStage n := by
  apply stageSequenceFunctor_eq (stageProperty C n)
  rw [(CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C t).mapStage_forget n]
  apply Functor.hext
  · intro A
    exact CofiberSequenceCategory.stageEvaluationTriangle_obj_forget C t n A
  · intro A B φ
    exact CofiberSequenceCategory.stageEvaluationTriangle_map_forget C t n φ

private theorem stagedSource_eq (n : ℕ) :
    H.lift_isWaldhausenExact.mapStage n ⋙
        (CofiberSequenceCategory.stageEvaluationTriangle C n).obj 0 =
      H.sourceExact.mapStage n := by
  rw [triangleStageFunctor_eq (C := C) n 0,
    ← Functor.IsWaldhausenExact.mapStage_comp H.lift_isWaldhausenExact
      (CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C 0) n]
  exact stageMapFunctor_eq (cofiberFunctorSequenceLift_source F₀ F₁ F₂ i p H.objectwise)
    (H.lift_isWaldhausenExact.comp
      (CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C 0)) H.sourceExact n

private theorem stagedMiddle_eq (n : ℕ) :
    H.lift_isWaldhausenExact.mapStage n ⋙
        (CofiberSequenceCategory.stageEvaluationTriangle C n).obj 1 =
      H.middleExact.mapStage n := by
  rw [triangleStageFunctor_eq (C := C) n 1,
    ← Functor.IsWaldhausenExact.mapStage_comp H.lift_isWaldhausenExact
      (CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C 1) n]
  exact stageMapFunctor_eq (cofiberFunctorSequenceLift_middle F₀ F₁ F₂ i p H.objectwise)
    (H.lift_isWaldhausenExact.comp
      (CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C 1)) H.middleExact n

private theorem stagedQuotient_eq (n : ℕ) :
    H.lift_isWaldhausenExact.mapStage n ⋙
        (CofiberSequenceCategory.stageEvaluationTriangle C n).obj 2 =
      H.quotientExact.mapStage n := by
  rw [triangleStageFunctor_eq (C := C) n 2,
    ← Functor.IsWaldhausenExact.mapStage_comp H.lift_isWaldhausenExact
      (CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C 2) n]
  exact stageMapFunctor_eq (cofiberFunctorSequenceLift_quotient F₀ F₁ F₂ i p H.objectwise)
    (H.lift_isWaldhausenExact.comp
      (CofiberSequenceCategory.evaluationIsRelativeWaldhausenExact C 2)) H.quotientExact n

private theorem stagedFirstArrow_heq (n : ℕ) :
    HEq (Functor.whiskerLeft (H.lift_isWaldhausenExact.mapStage n)
      (CofiberSequenceCategory.stageSourceToMiddle C n))
      (H.sourceExact.mapStageNatTrans H.middleExact i n) := by
  apply stageSequenceNatTransHExt (stagedSource_eq H n) (stagedMiddle_eq H n)
  intro A
  apply stageSequenceHomHEq (stageProperty C n)
    (Functor.congr_obj (stagedSource_eq H n) A)
    (Functor.congr_obj (stagedMiddle_eq H n) A)
  have h : HEq
      ((CofiberSequenceCategory.stageSourceToMiddle C n).app
        ((H.lift_isWaldhausenExact.mapStage n).obj A)).hom
      (Functor.whiskerLeft A.obj i) :=
    CofiberSequenceCategory.stageSourceToMiddle_app_hom C n
      ((H.lift_isWaldhausenExact.mapStage n).obj A)
  exact h.trans (heq_of_eq
    (Functor.IsWaldhausenExact.mapStageNatTrans_app_hom H.sourceExact H.middleExact i n A)).symm

private theorem stagedSecondArrow_heq (n : ℕ) :
    HEq (Functor.whiskerLeft (H.lift_isWaldhausenExact.mapStage n)
      (CofiberSequenceCategory.stageMiddleToQuotient C n))
      (H.middleExact.mapStageNatTrans H.quotientExact p n) := by
  apply stageSequenceNatTransHExt (stagedMiddle_eq H n) (stagedQuotient_eq H n)
  intro A
  apply stageSequenceHomHEq (stageProperty C n)
    (Functor.congr_obj (stagedMiddle_eq H n) A)
    (Functor.congr_obj (stagedQuotient_eq H n) A)
  have h : HEq
      ((CofiberSequenceCategory.stageMiddleToQuotient C n).app
        ((H.lift_isWaldhausenExact.mapStage n).obj A)).hom
      (Functor.whiskerLeft A.obj p) :=
    CofiberSequenceCategory.stageMiddleToQuotient_app_hom C n
      ((H.lift_isWaldhausenExact.mapStage n).obj A)
  exact h.trans (heq_of_eq
    (Functor.IsWaldhausenExact.mapStageNatTrans_app_hom H.middleExact H.quotientExact p n A)).symm

/-- The SAME original sequence after the actual stage functors, including
its complete original pushout base condition. -/
theorem mapStage (n : ℕ) :
    IsWaldhausenCofiberFunctorSequence (H.sourceExact.mapStage n)
      (H.middleExact.mapStage n) (H.quotientExact.mapStage n)
      (H.sourceExact.mapStageNatTrans H.middleExact i n)
      (H.middleExact.mapStageNatTrans H.quotientExact p n) := by
  have HU := CofiberSequenceCategory.stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n
  have HG := stageSequence_precomp (H.lift_isWaldhausenExact.mapStage n)
    (H.lift_isWaldhausenExact.mapStage_isWaldhausenExact n) HU
  exact stageSequence_of_heq (stagedSource_eq H n) (stagedMiddle_eq H n) (stagedQuotient_eq H n)
    (Functor.whiskerLeft (H.lift_isWaldhausenExact.mapStage n)
      (CofiberSequenceCategory.stageSourceToMiddle C n))
    (Functor.whiskerLeft (H.lift_isWaldhausenExact.mapStage n)
      (CofiberSequenceCategory.stageMiddleToQuotient C n))
    (H.sourceExact.mapStageNatTrans H.middleExact i n)
    (H.middleExact.mapStageNatTrans H.quotientExact p n)
    (stagedFirstArrow_heq H n) (stagedSecondArrow_heq H n) HG

/-- The original stage lift followed by the actual full relative transpose. -/
@[expose]
def stageLift (n : ℕ) : Stage D n ⥤ CofiberSequenceCategory (Stage C n) :=
  H.lift_isWaldhausenExact.mapStage n ⋙ CofiberSequenceCategory.relativeStageTranspose C n

/-- Exactness of this actual composite is earned from the two actual exact functors. -/
theorem stageLift_isWaldhausenExact (n : ℕ) : (H.stageLift n).IsWaldhausenExact :=
  (H.lift_isWaldhausenExact.mapStage_isWaldhausenExact n).comp
    (CofiberSequenceCategory.relativeStageTranspose_isWaldhausenExact C n)

/-- The entire source stage functor is the SAME original first-functor stage map. -/
theorem stageLift_source (n : ℕ) :
    H.stageLift n ⋙ CofiberSequenceCategory.source (Stage C n) = H.sourceExact.mapStage n := by
  change H.lift_isWaldhausenExact.mapStage n ⋙
    (CofiberSequenceCategory.relativeStageTranspose C n ⋙
      CofiberSequenceCategory.source (Stage C n)) = _
  rw [CofiberSequenceCategory.relativeStageTranspose_source]
  exact stagedSource_eq H n

/-- The entire middle stage functor is the SAME original middle-functor stage map. -/
theorem stageLift_middle (n : ℕ) :
    H.stageLift n ⋙ CofiberSequenceCategory.middle (Stage C n) = H.middleExact.mapStage n := by
  change H.lift_isWaldhausenExact.mapStage n ⋙
    (CofiberSequenceCategory.relativeStageTranspose C n ⋙
      CofiberSequenceCategory.middle (Stage C n)) = _
  rw [CofiberSequenceCategory.relativeStageTranspose_middle]
  exact stagedMiddle_eq H n

/-- The entire quotient stage functor is the SAME original last-functor stage map. -/
theorem stageLift_quotient (n : ℕ) :
    H.stageLift n ⋙ CofiberSequenceCategory.quotient (Stage C n) = H.quotientExact.mapStage n := by
  change H.lift_isWaldhausenExact.mapStage n ⋙
    (CofiberSequenceCategory.relativeStageTranspose C n ⋙
      CofiberSequenceCategory.quotient (Stage C n)) = _
  rw [CofiberSequenceCategory.relativeStageTranspose_quotient]
  exact stagedQuotient_eq H n

private theorem stagedNatTrans_app_heq
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (h : HEq α β) (X : A) :
    HEq (α.app X) (β.app X) := by
  cases hF
  cases hG
  cases h
  rfl

private theorem stagedMap_heq_of_eq
    {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
    {F G : A ⥤ B} (h : F = G) {X Y : A} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  cases h
  rfl

/-- The entire actual stage lift is the SAME stock cofiber lift of the
earned staged sequence, with the original stage functors and transformations. -/
theorem stageLift_eq (n : ℕ) :
    H.stageLift n = cofiberFunctorSequenceLift (H.sourceExact.mapStage n)
      (H.middleExact.mapStage n) (H.quotientExact.mapStage n)
      (H.sourceExact.mapStageNatTrans H.middleExact i n)
      (H.middleExact.mapStageNatTrans H.quotientExact p n) (H.mapStage n).objectwise := by
  let L := H.stageLift n
  let R := cofiberFunctorSequenceLift (H.sourceExact.mapStage n)
    (H.middleExact.mapStage n) (H.quotientExact.mapStage n)
    (H.sourceExact.mapStageNatTrans H.middleExact i n)
    (H.middleExact.mapStageNatTrans H.quotientExact p n) (H.mapStage n).objectwise
  have hobj (A : Stage D n) : L.obj A = R.obj A := by
    apply ObjectProperty.FullSubcategory.ext
    have h₀ : (L.obj A).obj.obj' 0 = (R.obj A).obj.obj' 0 :=
      Functor.congr_obj (stageLift_source H n) A
    have h₁ : (L.obj A).obj.obj' 1 = (R.obj A).obj.obj' 1 :=
      Functor.congr_obj (stageLift_middle H n) A
    have h₂ : (L.obj A).obj.obj' 2 = (R.obj A).obj.obj' 2 :=
      Functor.congr_obj (stageLift_quotient H n) A
    refine ComposableArrows.ext₂ (f := (L.obj A).obj) (g := (R.obj A).obj)
      h₀ h₁ h₂ ?_ ?_
    · apply (conj_eqToHom_iff_heq _ _ h₀ h₁).mpr
      have h := stagedNatTrans_app_heq (stagedSource_eq H n) (stagedMiddle_eq H n)
        (Functor.whiskerLeft (H.lift_isWaldhausenExact.mapStage n)
          (CofiberSequenceCategory.stageSourceToMiddle C n))
        (H.sourceExact.mapStageNatTrans H.middleExact i n) (stagedFirstArrow_heq H n) A
      change HEq
        (((CofiberSequenceCategory.relativeStageTranspose C n).obj
          ((H.lift_isWaldhausenExact.mapStage n).obj A)).obj.map' 0 1)
        ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A)
      rw [CofiberSequenceCategory.relativeStageTranspose_firstArrow]
      exact h
    · apply (conj_eqToHom_iff_heq _ _ h₁ h₂).mpr
      have h := stagedNatTrans_app_heq (stagedMiddle_eq H n) (stagedQuotient_eq H n)
        (Functor.whiskerLeft (H.lift_isWaldhausenExact.mapStage n)
          (CofiberSequenceCategory.stageMiddleToQuotient C n))
        (H.middleExact.mapStageNatTrans H.quotientExact p n) (stagedSecondArrow_heq H n) A
      change HEq
        (((CofiberSequenceCategory.relativeStageTranspose C n).obj
          ((H.lift_isWaldhausenExact.mapStage n).obj A)).obj.map' 1 2)
        ((H.middleExact.mapStageNatTrans H.quotientExact p n).app A)
      rw [CofiberSequenceCategory.relativeStageTranspose_secondArrow]
      exact h
  change L = R
  apply Functor.hext
  · exact hobj
  · intro A B φ
    apply stageSequenceHomHEq (cofiberSequenceProperty (Stage C n)) (hobj A) (hobj B)
    apply stageSequenceNatTransHExt
      (congrArg (CofiberSequenceCategory.forget (Stage C n)).obj (hobj A))
      (congrArg (CofiberSequenceCategory.forget (Stage C n)).obj (hobj B))
    intro t
    fin_cases t
    · exact stagedMap_heq_of_eq (stageLift_source H n) φ
    · exact stagedMap_heq_of_eq (stageLift_middle H n) φ
    · exact stagedMap_heq_of_eq (stageLift_quotient H n) φ

/-- The complete lifted cofiber diagram retains the original flag and
the original functor-sequence diagram with its two indices transposed. -/
theorem stageLift_obj_forget (n : ℕ) (A : Stage D n) :
    ((H.stageLift n).obj A).obj ⋙ SConstruction.forget C n =
      (A.obj ⋙ functorSequenceDiagram F₀ F₁ F₂ i p).flip := by
  have h := CofiberSequenceCategory.relativeStageTranspose_obj_forget C n
    ((H.lift_isWaldhausenExact.mapStage n).obj A)
  rw [H.lift_isWaldhausenExact.mapStage_obj n A] at h
  change ((H.stageLift n).obj A).obj ⋙ SConstruction.forget C n =
    ((A.obj ⋙ cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise) ⋙
      CofiberSequenceCategory.forget C).flip at h
  rw [Functor.assoc A.obj (cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise)
    (CofiberSequenceCategory.forget C), cofiberFunctorSequenceLift_forget] at h
  exact h

/-- Every coefficient is the original functor-sequence coefficient of
the same original source flag. -/
theorem stageLift_obj_app (n : ℕ) (A : Stage D n) (t : Fin 3) (x : Ar n) :
    ((((H.stageLift n).obj A).obj.obj t).obj.obj x) =
      ((functorSequenceDiagram F₀ F₁ F₂ i p).obj (A.obj.obj x)).obj t :=
  Functor.congr_obj (Functor.congr_obj (stageLift_obj_forget H n A) t) x

/-- The complete lifted stage map is the original functor-sequence map
on the original flag morphism, with both indices transposed. -/
theorem stageLift_map_forget_heq (n : ℕ) {A B : Stage D n} (φ : A ⟶ B) :
    HEq (Functor.whiskerRight ((H.stageLift n).map φ).hom (SConstruction.forget C n))
      ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
        (Functor.whiskerRight φ.hom (functorSequenceDiagram F₀ F₁ F₂ i p))) := by
  have h := CofiberSequenceCategory.relativeStageTranspose_map_forget_heq C n
    ((H.lift_isWaldhausenExact.mapStage n).map φ)
  rw [H.lift_isWaldhausenExact.mapStage_map n φ] at h
  change HEq
    (Functor.whiskerRight ((H.stageLift n).map φ).hom (SConstruction.forget C n))
    ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
      (Functor.whiskerRight φ.hom
        (cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise ⋙
          CofiberSequenceCategory.forget C))) at h
  rw [cofiberFunctorSequenceLift_forget] at h
  exact h

/-- Every scalar map is the original full functor-sequence component
applied to the same original scalar flag morphism. -/
theorem stageLift_map_app_heq (n : ℕ) {A B : Stage D n} (φ : A ⟶ B)
    (t : Fin 3) (x : Ar n) :
    HEq ((((H.stageLift n).map φ).hom.app t).hom.app x)
      (((functorSequenceDiagram F₀ F₁ F₂ i p).map (φ.hom.app x)).app t) := by
  have ht := stagedNatTrans_app_heq (stageLift_obj_forget H n A) (stageLift_obj_forget H n B)
    (Functor.whiskerRight ((H.stageLift n).map φ).hom (SConstruction.forget C n))
    ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
      (Functor.whiskerRight φ.hom (functorSequenceDiagram F₀ F₁ F₂ i p)))
    (stageLift_map_forget_heq H n φ) t
  exact stagedNatTrans_app_heq (Functor.congr_obj (stageLift_obj_forget H n A) t)
    (Functor.congr_obj (stageLift_obj_forget H n B) t) _ _ ht x

/-- The actual staged arrows have their internally earned whole stage cofiber sequence. -/
theorem mapStage_objectwise (n : ℕ) (A : Stage D n) :
    IsCofiberSequence ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A)
      ((H.middleExact.mapStageNatTrans H.quotientExact p n).app A) :=
  (H.mapStage n).objectwise A

/-- The SAME staged base descent is a genuine target stage cofibration,
with its original stock pushout earned from the actual first staged arrow. -/
theorem mapStage_baseCofibration (n : ℕ) {A B : Stage D n} (φ : A ⟶ B)
    (hφ : IsCofibration φ) :
    letI : HasPushout ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A)
        ((H.sourceExact.mapStage n).map φ) := (by
      obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
        (C := Stage C n) ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A)
        (mapStage_objectwise H n A).1 ((H.sourceExact.mapStage n).obj B)
        ((H.sourceExact.mapStage n).map φ)
      exact hP.flip.hasPushout)
    IsCofibration (pushout.desc ((H.middleExact.mapStage n).map φ)
      ((H.sourceExact.mapStageNatTrans H.middleExact i n).app B)
      ((H.sourceExact.mapStageNatTrans H.middleExact i n).naturality φ).symm) :=
  (H.mapStage n).baseCofibration φ hφ

/-- The whole original stage lift commutes with every original simplex operator,
with the same exact target reindex functor acting on the original cofiber rows. -/
theorem stageLift_reindex {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStage (C := D) f ⋙ H.stageLift a.len =
      H.stageLift b.len ⋙ CofiberSequenceCategory.mapOfWaldhausenExact
        (reindexStage (C := C) f) (reindexStage_general_isWaldhausenExact C f) := by
  calc
    _ = (reindexStage (C := D) f ⋙ H.lift_isWaldhausenExact.mapStage a.len) ⋙
        CofiberSequenceCategory.relativeStageTranspose C a.len := rfl
    _ = (H.lift_isWaldhausenExact.mapStage b.len ⋙
        reindexStage (C := CofiberSequenceCategory C) f) ⋙
          CofiberSequenceCategory.relativeStageTranspose C a.len :=
      congrArg (fun G => G ⋙ CofiberSequenceCategory.relativeStageTranspose C a.len)
        (H.lift_isWaldhausenExact.mapStage_reindex f)
    _ = H.lift_isWaldhausenExact.mapStage b.len ⋙
        (reindexStage (C := CofiberSequenceCategory C) f ⋙
          CofiberSequenceCategory.relativeStageTranspose C a.len) := rfl
    _ = H.lift_isWaldhausenExact.mapStage b.len ⋙
        (CofiberSequenceCategory.relativeStageTranspose C b.len ⋙
          CofiberSequenceCategory.mapOfWaldhausenExact (reindexStage (C := C) f)
            (reindexStage_general_isWaldhausenExact C f)) :=
      congrArg (fun G => H.lift_isWaldhausenExact.mapStage b.len ⋙ G)
        (CofiberSequenceCategory.relativeStageTranspose_reindex C f)
    _ = _ := rfl

/-- Both actual stage transformations retain the same full original flags. -/
theorem mapStage_firstArrow_app_hom (n : ℕ) (A : Stage D n) :
    ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A).hom =
      Functor.whiskerLeft A.obj i :=
  Functor.IsWaldhausenExact.mapStageNatTrans_app_hom H.sourceExact H.middleExact i n A

/-- The original quotient transformation retains the complete original flag. -/
theorem mapStage_secondArrow_app_hom (n : ℕ) (A : Stage D n) :
    ((H.middleExact.mapStageNatTrans H.quotientExact p n).app A).hom =
      Functor.whiskerLeft A.obj p :=
  Functor.IsWaldhausenExact.mapStageNatTrans_app_hom H.middleExact H.quotientExact p n A

/-- Every first-arrow component is the original source-sequence component. -/
theorem mapStage_firstArrow_app (n : ℕ) (A : Stage D n) (x : Ar n) :
    ((H.sourceExact.mapStageNatTrans H.middleExact i n).app A).hom.app x =
      i.app (A.obj.obj x) :=
  Functor.IsWaldhausenExact.mapStageNatTrans_app_hom_app H.sourceExact H.middleExact i n A x

/-- Every quotient-arrow component is the original source-sequence component. -/
theorem mapStage_secondArrow_app (n : ℕ) (A : Stage D n) (x : Ar n) :
    ((H.middleExact.mapStageNatTrans H.quotientExact p n).app A).hom.app x =
      p.app (A.obj.obj x) :=
  Functor.IsWaldhausenExact.mapStageNatTrans_app_hom_app H.middleExact H.quotientExact p n A x

/-- Degree zero retains the same actual staged sequence on the original zero-stage carriers. -/
theorem mapStage_zero :
    IsWaldhausenCofiberFunctorSequence (H.sourceExact.mapStage 0)
      (H.middleExact.mapStage 0) (H.quotientExact.mapStage 0)
      (H.sourceExact.mapStageNatTrans H.middleExact i 0)
      (H.middleExact.mapStageNatTrans H.quotientExact p 0) := H.mapStage 0

end IsWaldhausenCofiberFunctorSequence

end CategoryTheory.Waldhausen.SConstruction

end
