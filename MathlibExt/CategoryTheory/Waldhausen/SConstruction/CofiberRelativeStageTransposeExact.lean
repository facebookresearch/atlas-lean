/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeStageTriangle
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberFunctorSequence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageReindexWaldhausenExact
public import Mathlib.Tactic.FinCases

/-!
# The full relative cofiber-stage transpose

The original three stage evaluations and their two original arrows satisfy
the cofiber functor-sequence condition. The stock cofiber lift therefore
gives the actual functor `Stage (E(C)) n → E(Stage C n)` and its exactness
for the named relative and general stage Waldhausen structures.

For a source stage cofibration, its original zero-row corner is a pushout
in `E(C)`. Its two evaluated pushout squares, the two evaluations of the
stock stage base pushout, and the relative scalar corner form a cube.
The scalar relative corner is also the next zero-row corner of that stock
stage base map. This follows from their actual universal properties, so
neither gluing nor global pushout existence is needed.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

universe u v uB vB uD vD

namespace CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

/-- The five scalar pushout faces of the original base-corner cube.
The two `R` faces come from one original pushout in the cofiber category. -/
private structure CornerCube (C : Type u) [Category.{v} C] where
  A₀ : C
  A₁ : C
  B₀ : C
  B₁ : C
  A₀' : C
  A₁' : C
  B₀' : C
  B₁' : C
  D₀ : C
  D₁ : C
  R₀ : C
  R₁ : C
  T : C
  iA : A₀ ⟶ A₁
  iA' : A₀' ⟶ A₁'
  iB : B₀ ⟶ B₁
  iB' : B₀' ⟶ B₁'
  a₀ : A₀ ⟶ A₀'
  a₁ : A₁ ⟶ A₁'
  b₀ : B₀ ⟶ B₀'
  b₁ : B₁ ⟶ B₁'
  f₀ : A₀ ⟶ B₀
  f₁ : A₁ ⟶ B₁
  f₀' : A₀' ⟶ B₀'
  f₁' : A₁' ⟶ B₁'
  d₀L : A₁ ⟶ D₀
  d₀R : B₀ ⟶ D₀
  d₁L : A₁' ⟶ D₁
  d₁R : B₀' ⟶ D₁
  d₀Pushout : IsPushout iA f₀ d₀L d₀R
  d₁Pushout : IsPushout iA' f₀' d₁L d₁R
  ρ : D₀ ⟶ D₁
  d₀ : D₀ ⟶ B₁
  d₁ : D₁ ⟶ B₁'
  d₀L_ρ : d₀L ≫ ρ = a₁ ≫ d₁L
  d₀R_ρ : d₀R ≫ ρ = b₀ ≫ d₁R
  d₀L_d₀ : d₀L ≫ d₀ = f₁
  d₀R_d₀ : d₀R ≫ d₀ = iB
  d₁L_d₁ : d₁L ≫ d₁ = f₁'
  d₁R_d₁ : d₁R ≫ d₁ = iB'
  u₀ : A₀' ⟶ R₀
  v₀ : B₀ ⟶ R₀
  u₁ : A₁' ⟶ R₁
  v₁ : B₁ ⟶ R₁
  r₀Pushout : IsPushout a₀ f₀ u₀ v₀
  r₁Pushout : IsPushout a₁ f₁ u₁ v₁
  iR : R₀ ⟶ R₁
  r₀ : R₀ ⟶ B₀'
  r₁ : R₁ ⟶ B₁'
  u₀_iR : u₀ ≫ iR = iA' ≫ u₁
  v₀_iR : v₀ ≫ iR = iB ≫ v₁
  u₀_r₀ : u₀ ≫ r₀ = f₀'
  v₀_r₀ : v₀ ≫ r₀ = b₀
  u₁_r₁ : u₁ ≫ r₁ = f₁'
  v₁_r₁ : v₁ ≫ r₁ = b₁
  tL : R₁ ⟶ T
  tR : B₀' ⟶ T
  tPushout : IsPushout iR r₀ tL tR
  dT : T ⟶ B₁'
  tL_dT : tL ≫ dT = r₁
  tR_dT : tR ≫ dT = iB'

namespace CornerCube

private theorem next_condition {C : Type u} [Category.{v} C] (D : CornerCube C) :
    D.iA' ≫ (D.u₁ ≫ D.tL) = D.f₀' ≫ D.tR := by
  calc
    _ = (D.u₀ ≫ D.iR) ≫ D.tL := by rw [← Category.assoc, D.u₀_iR]
    _ = D.u₀ ≫ (D.r₀ ≫ D.tR) := by rw [Category.assoc, D.tPushout.w]
    _ = _ := by rw [← Category.assoc, D.u₀_r₀]

private def toNext {C : Type u} [Category.{v} C] (D : CornerCube C) : D.D₁ ⟶ D.T :=
  IsPushout.desc D.d₁Pushout (D.u₁ ≫ D.tL) D.tR (next_condition D)

private def fromMiddle {C : Type u} [Category.{v} C] (D : CornerCube C) : D.B₁ ⟶ D.T :=
  D.v₁ ≫ D.tL

private theorem toNext_left {C : Type u} [Category.{v} C] (D : CornerCube C) :
    D.d₁L ≫ toNext D = D.u₁ ≫ D.tL :=
  IsPushout.inl_desc D.d₁Pushout _ _ _

private theorem toNext_right {C : Type u} [Category.{v} C] (D : CornerCube C) :
    D.d₁R ≫ toNext D = D.tR :=
  IsPushout.inr_desc D.d₁Pushout _ _ _

private theorem condition {C : Type u} [Category.{v} C] (D : CornerCube C) :
    D.ρ ≫ toNext D = D.d₀ ≫ fromMiddle D := by
  apply IsPushout.hom_ext D.d₀Pushout
  · calc
      D.d₀L ≫ (D.ρ ≫ toNext D) = D.a₁ ≫ (D.u₁ ≫ D.tL) := by
        rw [← Category.assoc, D.d₀L_ρ, Category.assoc, toNext_left D]
      _ = D.f₁ ≫ (D.v₁ ≫ D.tL) := by
        rw [← Category.assoc, D.r₁Pushout.w, Category.assoc]
      _ = D.d₀L ≫ (D.d₀ ≫ fromMiddle D) := by
        simp only [fromMiddle, ← Category.assoc, D.d₀L_d₀]
  · calc
      D.d₀R ≫ (D.ρ ≫ toNext D) = D.b₀ ≫ D.tR := by
        rw [← Category.assoc, D.d₀R_ρ, Category.assoc, toNext_right D]
      _ = (D.v₀ ≫ D.r₀) ≫ D.tR := by rw [D.v₀_r₀]
      _ = (D.v₀ ≫ D.iR) ≫ D.tL := by rw [Category.assoc, ← D.tPushout.w,
        ← Category.assoc]
      _ = D.iB ≫ (D.v₁ ≫ D.tL) := by rw [D.v₀_iR, Category.assoc]
      _ = D.d₀R ≫ (D.d₀ ≫ fromMiddle D) := by
        simp only [fromMiddle, ← Category.assoc, D.d₀R_d₀]

private theorem hom_ext {C : Type u} [Category.{v} C] (D : CornerCube C)
    {Z : C} {p q : D.T ⟶ Z} (h₁ : toNext D ≫ p = toNext D ≫ q)
    (h₂ : fromMiddle D ≫ p = fromMiddle D ≫ q) : p = q := by
  apply IsPushout.hom_ext D.tPushout
  · apply IsPushout.hom_ext D.r₁Pushout
    · have h := congrArg (fun f => D.d₁L ≫ f) h₁
      simpa only [← Category.assoc, toNext_left D] using h
    · simpa only [fromMiddle, Category.assoc] using h₂
  · have h := congrArg (fun f => D.d₁R ≫ f) h₁
    simpa only [← Category.assoc, toNext_right D] using h

private theorem exists_desc {C : Type u} [Category.{v} C] (D : CornerCube C)
    {Z : C} (p : D.D₁ ⟶ Z) (q : D.B₁ ⟶ Z)
    (w : D.ρ ≫ p = D.d₀ ≫ q) :
    ∃ z : D.T ⟶ Z, toNext D ≫ z = p ∧ fromMiddle D ≫ z = q := by
  have w₁ : D.a₁ ≫ (D.d₁L ≫ p) = D.f₁ ≫ q := by
    have h := congrArg (fun f => D.d₀L ≫ f) w
    simpa only [← Category.assoc, D.d₀L_ρ, D.d₀L_d₀] using h
  have w₀ : D.b₀ ≫ (D.d₁R ≫ p) = D.iB ≫ q := by
    have h := congrArg (fun f => D.d₀R ≫ f) w
    simpa only [← Category.assoc, D.d₀R_ρ, D.d₀R_d₀] using h
  let r := IsPushout.desc D.r₁Pushout (D.d₁L ≫ p) q w₁
  have hu : D.u₁ ≫ r = D.d₁L ≫ p := IsPushout.inl_desc D.r₁Pushout _ _ _
  have hv : D.v₁ ≫ r = q := IsPushout.inr_desc D.r₁Pushout _ _ _
  have wr : D.iR ≫ r = D.r₀ ≫ (D.d₁R ≫ p) := by
    apply IsPushout.hom_ext D.r₀Pushout
    · calc
        D.u₀ ≫ (D.iR ≫ r) = D.iA' ≫ (D.d₁L ≫ p) := by
          rw [← Category.assoc, D.u₀_iR, Category.assoc, hu]
        _ = D.f₀' ≫ (D.d₁R ≫ p) := by
          rw [← Category.assoc, D.d₁Pushout.w, Category.assoc]
        _ = D.u₀ ≫ (D.r₀ ≫ (D.d₁R ≫ p)) := by
          simpa only [Category.assoc] using
            congrArg (fun f : D.A₀' ⟶ D.B₀' => f ≫ (D.d₁R ≫ p)) D.u₀_r₀.symm
    · calc
        D.v₀ ≫ (D.iR ≫ r) = D.iB ≫ q := by
          rw [← Category.assoc, D.v₀_iR, Category.assoc, hv]
        _ = D.b₀ ≫ (D.d₁R ≫ p) := w₀.symm
        _ = D.v₀ ≫ (D.r₀ ≫ (D.d₁R ≫ p)) := by
          simpa only [Category.assoc] using
            congrArg (fun f : D.B₀ ⟶ D.B₀' => f ≫ (D.d₁R ≫ p)) D.v₀_r₀.symm
  let z := IsPushout.desc D.tPushout r (D.d₁R ≫ p) wr
  have htL : D.tL ≫ z = r := IsPushout.inl_desc D.tPushout _ _ _
  have htR : D.tR ≫ z = D.d₁R ≫ p := IsPushout.inr_desc D.tPushout _ _ _
  refine ⟨z, ?_, ?_⟩
  · apply IsPushout.hom_ext D.d₁Pushout
    · rw [← Category.assoc, toNext_left D, Category.assoc, htL, hu]
    · rw [← Category.assoc, toNext_right D, htR]
  · change (D.v₁ ≫ D.tL) ≫ z = q
    rw [Category.assoc, htL, hv]

/-- The same actual relative corner supplies the stage base map's next corner. -/
private theorem isPushout {C : Type u} [Category.{v} C] (D : CornerCube C) :
    IsPushout D.ρ D.d₀ (toNext D) (fromMiddle D) :=
  IsPushout.mk' (condition D) (fun _ _ _ h₁ h₂ => hom_ext D h₁ h₂)
    (fun _ p q w => exists_desc D p q w)

private theorem toNext_dT {C : Type u} [Category.{v} C] (D : CornerCube C) :
    toNext D ≫ D.dT = D.d₁ := by
  apply IsPushout.hom_ext D.d₁Pushout
  · rw [← Category.assoc, toNext_left D, Category.assoc, D.tL_dT,
      D.u₁_r₁, D.d₁L_d₁]
  · rw [← Category.assoc, toNext_right D, D.tR_dT, D.d₁R_d₁]

private theorem fromMiddle_dT {C : Type u} [Category.{v} C] (D : CornerCube C) :
    fromMiddle D ≫ D.dT = D.b₁ := by
  change (D.v₁ ≫ D.tL) ≫ D.dT = D.b₁
  rw [Category.assoc, D.tL_dT, D.v₁_r₁]

end CornerCube

private theorem fullSubcategoryFunctor_eq
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    (P : ObjectProperty D) (F G : B ⥤ P.FullSubcategory)
    (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  have hobj (X : B) : F.obj X = G.obj X := by
    apply ObjectProperty.FullSubcategory.ext
    exact Functor.congr_obj h X
  refine Functor.ext hobj ?_
  intro X Y f
  apply P.fullyFaithfulι.map_injective
  simp only [Functor.map_comp, eqToHom_map]
  exact Functor.congr_hom h f

private theorem natTransHExt
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {F G F' G' : B ⥤ D} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (h : ∀ X : B, HEq (α.app X) (β.app X)) :
    HEq α β := by
  cases hF
  cases hG
  apply heq_of_eq
  apply NatTrans.ext
  funext X
  exact eq_of_heq (h X)

private theorem natTrans_app_heq
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {F G F' G' : B ⥤ D} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (h : HEq α β) (X : B) :
    HEq (α.app X) (β.app X) := by
  cases hF
  cases hG
  cases h
  rfl

private theorem fullSubcategoryHom_heq
    {D : Type uD} [Category.{vD} D] (P : ObjectProperty D)
    {X Y X' Y' : P.FullSubcategory} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') (h : HEq f.hom g.hom) : HEq f g := by
  cases hX
  cases hY
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  exact eq_of_heq h

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original relative Waldhausen value on the source cofiber category. -/
local instance originalRelativeWaldhausen : WaldhausenCategoryWithoutGluing
    (CofiberSequenceCategory C) :=
  relativeWaldhausenCategory C

local instance originalStageZero (n : ℕ) : HasZeroObject (Stage C n) :=
  generalStageHasZeroObject C n

/-- The original general Waldhausen value on each target finite stage. -/
local instance originalStageWaldhausen (n : ℕ) : WaldhausenCategoryWithoutGluing (Stage C n) :=
  generalStageWaldhausenCategory C n

local instance originalRelativeStageZero (n : ℕ) :
    HasZeroObject (Stage (CofiberSequenceCategory C) n) :=
  generalStageHasZeroObject (CofiberSequenceCategory C) n

/-- The original general stage value over the source relative cofiber category. -/
local instance originalRelativeStageWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (Stage (CofiberSequenceCategory C) n) :=
  generalStageWaldhausenCategory (CofiberSequenceCategory C) n

/-- The original relative cofiber value over the target general stage category. -/
local instance originalTargetRelativeWaldhausen (n : ℕ) :
    WaldhausenCategoryWithoutGluing (CofiberSequenceCategory (Stage C n)) :=
  relativeWaldhausenCategory (Stage C n)

private abbrev rowFunctor (n : ℕ) (t : Fin 3) :
    Stage (CofiberSequenceCategory C) n ⥤ Stage C n :=
  (evaluationIsRelativeWaldhausenExact C t).mapStage n

/-- A computed chart for the actual original stage-triangle arrow. -/
private def rowNatTrans (n : ℕ) {s t : Fin 3} (r : s ⟶ t) :
    rowFunctor C n s ⟶ rowFunctor C n t where
  app A := ObjectProperty.homMk
    (Functor.whiskerLeft A.obj (Functor.whiskerLeft (forget C)
      ((evaluation (Fin 3) C).map r)))
  naturality A B φ := by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext x
    change (φ.hom.app x).hom.app s ≫ (B.obj.obj x).obj.map r =
      (A.obj.obj x).obj.map r ≫ (φ.hom.app x).hom.app t
    exact ((φ.hom.app x).hom.naturality r).symm

private abbrev rowFirstArrow (n : ℕ) : rowFunctor C n 0 ⟶ rowFunctor C n 1 :=
  rowNatTrans C n (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))

private abbrev rowSecondArrow (n : ℕ) : rowFunctor C n 1 ⟶ rowFunctor C n 2 :=
  rowNatTrans C n (homOfLE (show (1 : Fin 3) ≤ 2 from by decide))

private theorem triangleFunctor_eq_row (n : ℕ) (t : Fin 3) :
    (stageEvaluationTriangle C n).obj t = rowFunctor C n t := by
  apply fullSubcategoryFunctor_eq (stageProperty C n)
  apply Functor.hext
  · intro A
    exact (stageEvaluationTriangle_obj_forget C t n A).trans
      ((evaluationIsRelativeWaldhausenExact C t).mapStage_obj n A).symm
  · intro A B φ
    exact (stageEvaluationTriangle_map_forget C t n φ).trans
      (heq_of_eq ((evaluationIsRelativeWaldhausenExact C t).mapStage_map n φ)).symm

private theorem triangleFirstArrow_heq (n : ℕ) :
    HEq (stageSourceToMiddle C n) (rowFirstArrow C n) := by
  apply natTransHExt (triangleFunctor_eq_row C n 0) (triangleFunctor_eq_row C n 1)
  intro A
  apply fullSubcategoryHom_heq (stageProperty C n)
    (Functor.congr_obj (triangleFunctor_eq_row C n 0) A)
    (Functor.congr_obj (triangleFunctor_eq_row C n 1) A)
  exact stageSourceToMiddle_app_hom C n A

private theorem triangleSecondArrow_heq (n : ℕ) :
    HEq (stageMiddleToQuotient C n) (rowSecondArrow C n) := by
  apply natTransHExt (triangleFunctor_eq_row C n 1) (triangleFunctor_eq_row C n 2)
  intro A
  apply fullSubcategoryHom_heq (stageProperty C n)
    (Functor.congr_obj (triangleFunctor_eq_row C n 1) A)
    (Functor.congr_obj (triangleFunctor_eq_row C n 2) A)
  exact stageMiddleToQuotient_app_hom C n A

/-- The original object triangle is a cofiber sequence for the actual
named general stage structure, through its actual zero-stage isomorphism. -/
theorem stageTriangle_isCofiberSequence (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) :
    IsCofiberSequence ((stageSourceToMiddle C n).app A)
      ((stageMiddleToQuotient C n).app A) := by
  obtain ⟨Z, hZ, z, q, hP⟩ := stageTriangle_exists_zeroPushout C n A
  let e : Z ≅ (0 : Stage C n) := hZ.isoZero
  refine ⟨(isCofibration_generalStageWaldhausenCategory_iff C n _).mpr
    (stageSourceToMiddle_isCofibration C n A), z ≫ e.hom, e.inv ≫ q, ?_⟩
  apply hP.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
  all_goals simp

private theorem cofiberSequence_of_heq
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    {A B Q A' B' Q' : D} (hA : A = A') (hB : B = B') (hQ : Q = Q')
    (i : A ⟶ B) (p : B ⟶ Q) (i' : A' ⟶ B') (p' : B' ⟶ Q')
    (hi : HEq i i') (hp : HEq p p') (h : IsCofiberSequence i p) :
    IsCofiberSequence i' p' := by
  cases hA
  cases hB
  cases hQ
  cases hi
  cases hp
  exact h

private theorem row_isCofiberSequence (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) :
    IsCofiberSequence ((rowFirstArrow C n).app A) ((rowSecondArrow C n).app A) := by
  exact cofiberSequence_of_heq
    (Functor.congr_obj (triangleFunctor_eq_row C n 0) A)
    (Functor.congr_obj (triangleFunctor_eq_row C n 1) A)
    (Functor.congr_obj (triangleFunctor_eq_row C n 2) A)
    ((stageSourceToMiddle C n).app A) ((stageMiddleToQuotient C n).app A)
    ((rowFirstArrow C n).app A) ((rowSecondArrow C n).app A)
    (natTrans_app_heq (triangleFunctor_eq_row C n 0) (triangleFunctor_eq_row C n 1)
      (stageSourceToMiddle C n) (rowFirstArrow C n) (triangleFirstArrow_heq C n) A)
    (natTrans_app_heq (triangleFunctor_eq_row C n 1) (triangleFunctor_eq_row C n 2)
      (stageMiddleToQuotient C n) (rowSecondArrow C n) (triangleSecondArrow_heq C n) A)
    (stageTriangle_isCofiberSequence C n A)

/-- The base map is the stock stage pushout descent. Each of its original
successive corners is the same actual scalar relative corner supplied by `φ`. -/
private theorem row_baseCofibration (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B)
    (hφ : stageCofibrations (CofiberSequenceCategory C) n φ)
    [HasPushout ((rowFirstArrow C n).app A) ((rowFunctor C n 0).map φ)] :
    stageCofibrations C n
      (pushout.desc ((rowFunctor C n 1).map φ) ((rowFirstArrow C n).app B)
        ((rowFirstArrow C n).naturality φ).symm) := by
  let A₀ := (rowFunctor C n 0).obj A
  let A₁ := (rowFunctor C n 1).obj A
  let B₀ := (rowFunctor C n 0).obj B
  let B₁ := (rowFunctor C n 1).obj B
  let i : A₀ ⟶ A₁ := (rowFirstArrow C n).app A
  let i' : B₀ ⟶ B₁ := (rowFirstArrow C n).app B
  let f : A₀ ⟶ B₀ := (rowFunctor C n 0).map φ
  let g : A₁ ⟶ B₁ := (rowFunctor C n 1).map φ
  let D : Stage C n := pushout i f
  let l : A₁ ⟶ D := pushout.inl i f
  let r : B₀ ⟶ D := pushout.inr i f
  let δ : D ⟶ B₁ := pushout.desc g i' ((rowFirstArrow C n).naturality φ).symm
  have hi : stageCofibrations C n i :=
    (isCofibration_generalStageWaldhausenCategory_iff C n i).mp
      (row_isCofiberSequence C n A).1
  have hD : IsPushout i f l r := IsPushout.of_hasPushout i f
  have hDx (x : Ar n) :
      IsPushout (i.hom.app x) (f.hom.app x) (l.hom.app x) (r.hom.app x) :=
    (GeneralStagePushoutPresentation.isPushout_app (C := C) hi hD.flip x).flip
  have hlδ : l ≫ δ = g := pushout.inl_desc _ _ _
  have hrδ : r ≫ δ = i' := pushout.inr_desc _ _ _
  intro j
  let x₀ := interval 0 j.castSucc (Fin.zero_le _)
  let x₁ := interval 0 j.succ (Fin.zero_le _)
  let h := horiz (Fin.zero_le j.castSucc) j.castSucc_le_succ
  obtain ⟨R, uR, vR, dR, hR, huR, hvR, hdR⟩ := hφ j
  have ha : IsCofibration (A.zeroRowSuccMap j) :=
    (A.property.cofiber_triple (Fin.zero_le j.castSucc) j.castSucc_le_succ).1
  have hR₀ :
      IsPushout (A₀.zeroRowSuccMap j) (Stage.zeroRowApp f j.castSucc)
        ((source C).map uR) ((source C).map vR) :=
    ((sourceIsRelativeWaldhausenExact C).map_pushout
      (A.zeroRowSuccMap j) (Stage.zeroRowApp φ j.castSucc) vR uR ha hR.flip).flip
  have hR₁ :
      IsPushout (A₁.zeroRowSuccMap j) (Stage.zeroRowApp g j.castSucc)
        ((middle C).map uR) ((middle C).map vR) :=
    ((middleIsRelativeWaldhausenExact C).map_pushout
      (A.zeroRowSuccMap j) (Stage.zeroRowApp φ j.castSucc) vR uR ha hR.flip).flip
  have hRelative : relativeCofibrations C dR :=
    (isCofibration_relativeWaldhausenCategory_iff C dR).mp hdR
  obtain ⟨_, T, tL, tR, dT, hT, htL, htR, hdT⟩ :=
    (mem_relativeCofibrations_raw_iff C dR).mp hRelative
  let K : CornerCube C :=
    { A₀ := A₀.zeroRowObj j.castSucc
      A₁ := A₁.zeroRowObj j.castSucc
      B₀ := B₀.zeroRowObj j.castSucc
      B₁ := B₁.zeroRowObj j.castSucc
      A₀' := A₀.zeroRowObj j.succ
      A₁' := A₁.zeroRowObj j.succ
      B₀' := B₀.zeroRowObj j.succ
      B₁' := B₁.zeroRowObj j.succ
      D₀ := D.zeroRowObj j.castSucc
      D₁ := D.zeroRowObj j.succ
      R₀ := (source C).obj R
      R₁ := (middle C).obj R
      T := T
      iA := Stage.zeroRowApp i j.castSucc
      iA' := Stage.zeroRowApp i j.succ
      iB := Stage.zeroRowApp i' j.castSucc
      iB' := Stage.zeroRowApp i' j.succ
      a₀ := A₀.zeroRowSuccMap j
      a₁ := A₁.zeroRowSuccMap j
      b₀ := B₀.zeroRowSuccMap j
      b₁ := B₁.zeroRowSuccMap j
      f₀ := Stage.zeroRowApp f j.castSucc
      f₁ := Stage.zeroRowApp g j.castSucc
      f₀' := Stage.zeroRowApp f j.succ
      f₁' := Stage.zeroRowApp g j.succ
      d₀L := Stage.zeroRowApp l j.castSucc
      d₀R := Stage.zeroRowApp r j.castSucc
      d₁L := Stage.zeroRowApp l j.succ
      d₁R := Stage.zeroRowApp r j.succ
      d₀Pushout := hDx x₀
      d₁Pushout := hDx x₁
      ρ := D.zeroRowSuccMap j
      d₀ := Stage.zeroRowApp δ j.castSucc
      d₁ := Stage.zeroRowApp δ j.succ
      d₀L_ρ := (l.hom.naturality h).symm
      d₀R_ρ := (r.hom.naturality h).symm
      d₀L_d₀ := congrArg (fun ψ : A₁ ⟶ B₁ => ψ.hom.app x₀) hlδ
      d₀R_d₀ := congrArg (fun ψ : B₀ ⟶ B₁ => ψ.hom.app x₀) hrδ
      d₁L_d₁ := congrArg (fun ψ : A₁ ⟶ B₁ => ψ.hom.app x₁) hlδ
      d₁R_d₁ := congrArg (fun ψ : B₀ ⟶ B₁ => ψ.hom.app x₁) hrδ
      u₀ := (source C).map uR
      v₀ := (source C).map vR
      u₁ := (middle C).map uR
      v₁ := (middle C).map vR
      r₀Pushout := hR₀
      r₁Pushout := hR₁
      iR := R.obj.map' 0 1
      r₀ := (source C).map dR
      r₁ := (middle C).map dR
      u₀_iR := (uR.hom.naturality
        (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))).symm
      v₀_iR := (vR.hom.naturality
        (homOfLE (show (0 : Fin 3) ≤ 1 from by decide))).symm
      u₀_r₀ := by
        simp only [A₀, B₀, f, rowFunctor, source, Stage.zeroRowObj, Stage.zeroRowApp,
          Functor.IsWaldhausenExact.mapStage_obj, Functor.IsWaldhausenExact.mapStage_map,
          Functor.comp_obj, Functor.comp_map, Functor.whiskerRight_app]
        let E := (evaluation (Fin 3) C).obj (0 : Fin 3)
        change E.map ((forget C).map uR) ≫ E.map ((forget C).map dR) =
          E.map ((forget C).map (Stage.zeroRowApp φ j.succ))
        calc
          _ = E.map ((forget C).map uR ≫ (forget C).map dR) := (E.map_comp _ _).symm
          _ = E.map ((forget C).map (uR ≫ dR)) :=
            congrArg E.map ((forget C).map_comp uR dR).symm
          _ = _ := congrArg
            (fun ψ : A.zeroRowObj j.succ ⟶ B.zeroRowObj j.succ =>
              E.map ((forget C).map ψ)) huR
      v₀_r₀ := by
        simp only [B₀, rowFunctor, source, Stage.zeroRowObj, Stage.zeroRowSuccMap,
          Functor.IsWaldhausenExact.mapStage_obj, Functor.comp_map,
          Functor.comp_obj]
        let E := (evaluation (Fin 3) C).obj (0 : Fin 3)
        change E.map ((forget C).map vR) ≫ E.map ((forget C).map dR) =
          E.map ((forget C).map (B.zeroRowSuccMap j))
        calc
          _ = E.map ((forget C).map vR ≫ (forget C).map dR) := (E.map_comp _ _).symm
          _ = E.map ((forget C).map (vR ≫ dR)) :=
            congrArg E.map ((forget C).map_comp vR dR).symm
          _ = _ := congrArg
            (fun ψ : B.zeroRowObj j.castSucc ⟶ B.zeroRowObj j.succ =>
              E.map ((forget C).map ψ)) hvR
      u₁_r₁ := by
        simp only [A₁, B₁, g, rowFunctor, middle, Stage.zeroRowObj, Stage.zeroRowApp,
          Functor.IsWaldhausenExact.mapStage_obj, Functor.IsWaldhausenExact.mapStage_map,
          Functor.comp_obj, Functor.comp_map, Functor.whiskerRight_app]
        let E := (evaluation (Fin 3) C).obj (1 : Fin 3)
        change E.map ((forget C).map uR) ≫ E.map ((forget C).map dR) =
          E.map ((forget C).map (Stage.zeroRowApp φ j.succ))
        calc
          _ = E.map ((forget C).map uR ≫ (forget C).map dR) := (E.map_comp _ _).symm
          _ = E.map ((forget C).map (uR ≫ dR)) :=
            congrArg E.map ((forget C).map_comp uR dR).symm
          _ = _ := congrArg
            (fun ψ : A.zeroRowObj j.succ ⟶ B.zeroRowObj j.succ =>
              E.map ((forget C).map ψ)) huR
      v₁_r₁ := by
        simp only [B₁, rowFunctor, middle, Stage.zeroRowObj, Stage.zeroRowSuccMap,
          Functor.IsWaldhausenExact.mapStage_obj, Functor.comp_map,
          Functor.comp_obj]
        let E := (evaluation (Fin 3) C).obj (1 : Fin 3)
        change E.map ((forget C).map vR) ≫ E.map ((forget C).map dR) =
          E.map ((forget C).map (B.zeroRowSuccMap j))
        calc
          _ = E.map ((forget C).map vR ≫ (forget C).map dR) := (E.map_comp _ _).symm
          _ = E.map ((forget C).map (vR ≫ dR)) :=
            congrArg E.map ((forget C).map_comp vR dR).symm
          _ = _ := congrArg
            (fun ψ : B.zeroRowObj j.castSucc ⟶ B.zeroRowObj j.succ =>
              E.map ((forget C).map ψ)) hvR
      tL := tL
      tR := tR
      tPushout := hT
      dT := dT
      tL_dT := htL
      tR_dT := htR }
  refine ⟨T, CornerCube.toNext K, CornerCube.fromMiddle K, dT, ?_, ?_, ?_, hdT⟩
  · exact CornerCube.isPushout K
  · exact CornerCube.toNext_dT K
  · exact CornerCube.fromMiddle_dT K

private theorem row_functor_sequence (n : ℕ) :
    IsWaldhausenCofiberFunctorSequence (rowFunctor C n 0) (rowFunctor C n 1)
      (rowFunctor C n 2) (rowFirstArrow C n) (rowSecondArrow C n) := by
  refine ⟨(evaluationIsRelativeWaldhausenExact C 0).mapStage_isWaldhausenExact n,
    (evaluationIsRelativeWaldhausenExact C 1).mapStage_isWaldhausenExact n,
    (evaluationIsRelativeWaldhausenExact C 2).mapStage_isWaldhausenExact n,
    row_isCofiberSequence C n, ?_⟩
  intro A B φ hφ
  let : HasPushout ((rowFirstArrow C n).app A) ((rowFunctor C n 0).map φ) := by
    obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
      (C := Stage C n) ((rowFirstArrow C n).app A) (row_isCofiberSequence C n A).1
      ((rowFunctor C n 0).obj B) ((rowFunctor C n 0).map φ)
    exact hP.flip.hasPushout
  exact (isCofibration_generalStageWaldhausenCategory_iff C n _).mpr
    (row_baseCofibration C n φ
      ((isCofibration_generalStageWaldhausenCategory_iff
        (CofiberSequenceCategory C) n φ).mp hφ))

private theorem functorSequence_of_heq
    {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    {F₀ F₁ F₂ G₀ G₁ G₂ : B ⥤ D}
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

/-- The SAME original stage evaluation triangle satisfies the full source
cofiber functor-sequence condition, including every relative base corner. -/
theorem stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence (n : ℕ) :
    IsWaldhausenCofiberFunctorSequence
      ((stageEvaluationTriangle C n).obj 0) ((stageEvaluationTriangle C n).obj 1)
      ((stageEvaluationTriangle C n).obj 2)
      (stageSourceToMiddle C n) (stageMiddleToQuotient C n) :=
  functorSequence_of_heq (triangleFunctor_eq_row C n 0).symm
    (triangleFunctor_eq_row C n 1).symm (triangleFunctor_eq_row C n 2).symm
    (rowFirstArrow C n) (rowSecondArrow C n)
    (stageSourceToMiddle C n) (stageMiddleToQuotient C n)
    (triangleFirstArrow_heq C n).symm (triangleSecondArrow_heq C n).symm
    (row_functor_sequence C n)

/-- The actual full transpose is the original stock cofiber lift of the
original stage evaluations and their original two natural transformations. -/
def relativeStageTranspose (n : ℕ) :
    Stage (CofiberSequenceCategory C) n ⥤ CofiberSequenceCategory (Stage C n) :=
  cofiberFunctorSequenceLift
    ((stageEvaluationTriangle C n).obj 0) ((stageEvaluationTriangle C n).obj 1)
    ((stageEvaluationTriangle C n).obj 2)
    (stageSourceToMiddle C n) (stageMiddleToQuotient C n)
    (stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n).objectwise

/-- Every exactness field is derived from the earned full functor-sequence
certificate for the original named relative/general stage structures. -/
theorem relativeStageTranspose_isWaldhausenExact (n : ℕ) :
    (relativeStageTranspose C n).IsWaldhausenExact :=
  (stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n).lift_isWaldhausenExact

/-- The whole original cofiber diagram is the original two-arrow stage triangle. -/
theorem relativeStageTranspose_forget (n : ℕ) :
    relativeStageTranspose C n ⋙ forget (Stage C n) =
      functorSequenceDiagram
        ((stageEvaluationTriangle C n).obj 0) ((stageEvaluationTriangle C n).obj 1)
        ((stageEvaluationTriangle C n).obj 2)
        (stageSourceToMiddle C n) (stageMiddleToQuotient C n) := rfl

/-- Source evaluation retains the full original first stage-evaluation functor. -/
theorem relativeStageTranspose_source (n : ℕ) :
    relativeStageTranspose C n ⋙ source (Stage C n) =
      (stageEvaluationTriangle C n).obj 0 :=
  cofiberFunctorSequenceLift_source
    ((stageEvaluationTriangle C n).obj 0) ((stageEvaluationTriangle C n).obj 1)
    ((stageEvaluationTriangle C n).obj 2)
    (stageSourceToMiddle C n) (stageMiddleToQuotient C n)
    (stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n).objectwise

/-- Middle evaluation retains the full original middle stage-evaluation functor. -/
theorem relativeStageTranspose_middle (n : ℕ) :
    relativeStageTranspose C n ⋙ middle (Stage C n) =
      (stageEvaluationTriangle C n).obj 1 :=
  cofiberFunctorSequenceLift_middle
    ((stageEvaluationTriangle C n).obj 0) ((stageEvaluationTriangle C n).obj 1)
    ((stageEvaluationTriangle C n).obj 2)
    (stageSourceToMiddle C n) (stageMiddleToQuotient C n)
    (stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n).objectwise

/-- Quotient evaluation retains the full original last stage-evaluation functor. -/
theorem relativeStageTranspose_quotient (n : ℕ) :
    relativeStageTranspose C n ⋙ quotient (Stage C n) =
      (stageEvaluationTriangle C n).obj 2 :=
  cofiberFunctorSequenceLift_quotient
    ((stageEvaluationTriangle C n).obj 0) ((stageEvaluationTriangle C n).obj 1)
    ((stageEvaluationTriangle C n).obj 2)
    (stageSourceToMiddle C n) (stageMiddleToQuotient C n)
    (stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n).objectwise

/-- Every original stage object is retained in its corresponding cofiber slot. -/
theorem relativeStageTranspose_obj_component (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) (t : Fin 3) :
    ((relativeStageTranspose C n).obj A).obj.obj t =
      ((stageEvaluationTriangle C n).obj t).obj A := by
  fin_cases t <;> rfl

/-- The original stage map is retained as a whole map in each cofiber slot. -/
theorem relativeStageTranspose_map_component_heq (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B) (t : Fin 3) :
    HEq (((relativeStageTranspose C n).map φ).hom.app t)
      (((stageEvaluationTriangle C n).obj t).map φ) := by
  fin_cases t <;> rfl

/-- The original first cofiber arrow is retained on the whole stage. -/
theorem relativeStageTranspose_firstArrow (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) :
    (((relativeStageTranspose C n).obj A).obj.map' 0 1) =
      (stageSourceToMiddle C n).app A := rfl

/-- The original quotient arrow is retained on the whole stage. -/
theorem relativeStageTranspose_secondArrow (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) :
    (((relativeStageTranspose C n).obj A).obj.map' 1 2) =
      (stageMiddleToQuotient C n).app A := rfl

/-- The original base condition uses the stock stage pushout and its
original full descent map, with existence derived from the original first arrow. -/
theorem stageTriangle_baseCofibration (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B) (hφ : IsCofibration φ) :
    letI : HasPushout ((stageSourceToMiddle C n).app A)
        (((stageEvaluationTriangle C n).obj 0).map φ) := (by
      obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
        (C := Stage C n) ((stageSourceToMiddle C n).app A)
        (stageTriangle_isCofiberSequence C n A).1
        (((stageEvaluationTriangle C n).obj 0).obj B)
        (((stageEvaluationTriangle C n).obj 0).map φ)
      exact hP.flip.hasPushout)
    IsCofibration (pushout.desc (((stageEvaluationTriangle C n).obj 1).map φ)
      ((stageSourceToMiddle C n).app B) ((stageSourceToMiddle C n).naturality φ).symm) :=
  (stageEvaluationTriangle_isWaldhausenCofiberFunctorSequence C n).baseCofibration φ hφ

/-- The complete transposed diagram is the original diagram with its two
indices flipped; every cofiber map and every interval map is retained. -/
theorem relativeStageTranspose_obj_forget (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) :
    ((relativeStageTranspose C n).obj A).obj ⋙ SConstruction.forget C n =
      (A.obj ⋙ forget C).flip := by
  let L : ComposableArrows (Ar n ⥤ C) 2 :=
    ((relativeStageTranspose C n).obj A).obj ⋙ SConstruction.forget C n
  let R : ComposableArrows (Ar n ⥤ C) 2 := (A.obj ⋙ forget C).flip
  have h₀ : L.obj' 0 = R.obj' 0 := stageEvaluationTriangle_obj_forget C 0 n A
  have h₁ : L.obj' 1 = R.obj' 1 := stageEvaluationTriangle_obj_forget C 1 n A
  have h₂ : L.obj' 2 = R.obj' 2 := stageEvaluationTriangle_obj_forget C 2 n A
  refine ComposableArrows.ext₂ (f := L) (g := R) h₀ h₁ h₂ ?_ ?_
  · apply (conj_eqToHom_iff_heq (L.map' 0 1) (R.map' 0 1) h₀ h₁).mpr
    exact stageSourceToMiddle_app_hom C n A
  · apply (conj_eqToHom_iff_heq (L.map' 1 2) (R.map' 1 2) h₁ h₂).mpr
    exact stageMiddleToQuotient_app_hom C n A

/-- The whole original map is flipped with the same original source and
target diagrams, before any component is selected. -/
theorem relativeStageTranspose_map_forget_heq (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B) :
    HEq (Functor.whiskerRight ((relativeStageTranspose C n).map φ).hom
      (SConstruction.forget C n))
      ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
        (Functor.whiskerRight φ.hom (forget C))) := by
  apply natTransHExt (relativeStageTranspose_obj_forget C n A)
    (relativeStageTranspose_obj_forget C n B)
  intro t
  fin_cases t
  · exact stageEvaluationTriangle_map_forget C 0 n φ
  · exact stageEvaluationTriangle_map_forget C 1 n φ
  · exact stageEvaluationTriangle_map_forget C 2 n φ

/-- The entire flipped map retains the actual original diagram transports. -/
theorem relativeStageTranspose_map_forget (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B) :
    eqToHom (relativeStageTranspose_obj_forget C n A).symm ≫
        Functor.whiskerRight ((relativeStageTranspose C n).map φ).hom
          (SConstruction.forget C n) ≫
        eqToHom (relativeStageTranspose_obj_forget C n B) =
      (CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
        (Functor.whiskerRight φ.hom (forget C)) :=
  ((conj_eqToHom_iff_heq
    ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
      (Functor.whiskerRight φ.hom (forget C)))
    (Functor.whiskerRight ((relativeStageTranspose C n).map φ).hom
      (SConstruction.forget C n))
    (relativeStageTranspose_obj_forget C n A).symm
    (relativeStageTranspose_obj_forget C n B).symm).mpr
      (relativeStageTranspose_map_forget_heq C n φ).symm).symm

/-- Every original coefficient is the same coefficient with its indices transposed. -/
theorem relativeStageTranspose_obj_app (n : ℕ)
    (A : Stage (CofiberSequenceCategory C) n) (t : Fin 3) (x : Ar n) :
    ((((relativeStageTranspose C n).obj A).obj.obj t).obj.obj x) =
      (A.obj.obj x).obj.obj t :=
  Functor.congr_obj
    (Functor.congr_obj (relativeStageTranspose_obj_forget C n A) t) x

/-- Every scalar map is the same original scalar map of the original stage. -/
theorem relativeStageTranspose_map_app_heq (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B)
    (t : Fin 3) (x : Ar n) :
    HEq ((((relativeStageTranspose C n).map φ).hom.app t).hom.app x)
      ((φ.hom.app x).hom.app t) := by
  have ht := natTrans_app_heq (relativeStageTranspose_obj_forget C n A)
    (relativeStageTranspose_obj_forget C n B)
    (Functor.whiskerRight ((relativeStageTranspose C n).map φ).hom
      (SConstruction.forget C n))
    ((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
      (Functor.whiskerRight φ.hom (forget C)))
    (relativeStageTranspose_map_forget_heq C n φ) t
  exact natTrans_app_heq
    (Functor.congr_obj (relativeStageTranspose_obj_forget C n A) t)
    (Functor.congr_obj (relativeStageTranspose_obj_forget C n B) t)
    ((Functor.whiskerRight ((relativeStageTranspose C n).map φ).hom
      (SConstruction.forget C n)).app t)
    (((CategoryTheory.flipFunctor (Ar n) (Fin 3) C).map
      (Functor.whiskerRight φ.hom (forget C))).app t) ht x

/-- The actual transpose preserves zero objects of the original source stage. -/
theorem relativeStageTranspose_map_isZero (n : ℕ)
    {A : Stage (CofiberSequenceCategory C) n} (hA : IsZero A) :
    IsZero ((relativeStageTranspose C n).obj A) :=
  (relativeStageTranspose_isWaldhausenExact C n).map_isZero hA

/-- Every original genuine source stage cofibration maps to the full
relative cofiber cofibration, including its actual stage pushout corner. -/
theorem relativeStageTranspose_map_relativeCofibration (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B)
    (hφ : stageCofibrations (CofiberSequenceCategory C) n φ) :
    relativeCofibrations (Stage C n) ((relativeStageTranspose C n).map φ) := by
  apply (isCofibration_relativeWaldhausenCategory_iff (Stage C n) _).mp
  exact (relativeStageTranspose_isWaldhausenExact C n).map_cofibration φ
    ((isCofibration_generalStageWaldhausenCategory_iff
      (CofiberSequenceCategory C) n φ).mpr hφ)

/-- Every original weak stage map is retained as a weak map of the same cofiber rows. -/
theorem relativeStageTranspose_map_weakEquivalence (n : ℕ)
    {A B : Stage (CofiberSequenceCategory C) n} (φ : A ⟶ B)
    (hφ : IsWeakEquivalence φ) :
    IsWeakEquivalence ((relativeStageTranspose C n).map φ) :=
  (relativeStageTranspose_isWaldhausenExact C n).map_weakEquivalence φ hφ

/-- The complete original source-stage pushout is preserved as a whole
pushout in the actual relative cofiber category over the original target stage. -/
theorem relativeStageTranspose_map_pushout (n : ℕ)
    {A B A' P : Stage (CofiberSequenceCategory C) n}
    (i : A ⟶ B) (f : A ⟶ A') (inl : A' ⟶ P) (inr : B ⟶ P)
    (hi : IsCofibration i) (hP : IsPushout f i inl inr) :
    IsPushout ((relativeStageTranspose C n).map f) ((relativeStageTranspose C n).map i)
      ((relativeStageTranspose C n).map inl) ((relativeStageTranspose C n).map inr) :=
  (relativeStageTranspose_isWaldhausenExact C n).map_pushout i f inl inr hi hP

private theorem triangle_reindex {a b : SimplexCategory} (f : a ⟶ b) (t : Fin 3) :
    reindexStage (C := CofiberSequenceCategory C) f ⋙ (stageEvaluationTriangle C a.len).obj t =
      (stageEvaluationTriangle C b.len).obj t ⋙ reindexStage (C := C) f := by
  rw [triangleFunctor_eq_row C a.len t, triangleFunctor_eq_row C b.len t]
  exact (evaluationIsRelativeWaldhausenExact C t).mapStage_reindex f

private theorem transpose_reindex_obj {a b : SimplexCategory} (f : a ⟶ b)
    (A : Stage (CofiberSequenceCategory C) b.len) :
    ((relativeStageTranspose C a.len).obj
      ((reindexStage (C := CofiberSequenceCategory C) f).obj A)).obj =
        ((relativeStageTranspose C b.len).obj A).obj ⋙ reindexStage (C := C) f := by
  let L : ComposableArrows (Stage C a.len) 2 :=
    ((relativeStageTranspose C a.len).obj
      ((reindexStage (C := CofiberSequenceCategory C) f).obj A)).obj
  let R : ComposableArrows (Stage C a.len) 2 :=
    ((relativeStageTranspose C b.len).obj A).obj ⋙ reindexStage (C := C) f
  have h₀ : L.obj' 0 = R.obj' 0 := stageEvaluationTriangle_obj_reindex C f A 0
  have h₁ : L.obj' 1 = R.obj' 1 := stageEvaluationTriangle_obj_reindex C f A 1
  have h₂ : L.obj' 2 = R.obj' 2 := stageEvaluationTriangle_obj_reindex C f A 2
  refine ComposableArrows.ext₂ (f := L) (g := R) h₀ h₁ h₂ ?_ ?_
  · apply (conj_eqToHom_iff_heq (L.map' 0 1) (R.map' 0 1) h₀ h₁).mpr
    exact fullSubcategoryHom_heq (stageProperty C a.len) h₀ h₁
      (L.map' 0 1) (R.map' 0 1)
      (stageSourceToMiddle_app_reindex_hom C f A).symm
  · apply (conj_eqToHom_iff_heq (L.map' 1 2) (R.map' 1 2) h₁ h₂).mpr
    exact fullSubcategoryHom_heq (stageProperty C a.len) h₁ h₂
      (L.map' 1 2) (R.map' 1 2)
      (stageMiddleToQuotient_app_reindex_hom C f A).symm

private theorem map_heq_of_functor_eq
    {B : Type uB} [Category.{vB} B] {D : Type uD} [Category.{vD} D]
    {F G : B ⥤ D} (h : F = G) {X Y : B} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  cases h
  rfl

private theorem transpose_reindex_map_heq {a b : SimplexCategory} (f : a ⟶ b)
    {A B : Stage (CofiberSequenceCategory C) b.len} (φ : A ⟶ B) :
    HEq ((relativeStageTranspose C a.len).map
      ((reindexStage (C := CofiberSequenceCategory C) f).map φ)).hom
      (Functor.whiskerRight ((relativeStageTranspose C b.len).map φ).hom
        (reindexStage (C := C) f)) := by
  apply natTransHExt (transpose_reindex_obj C f A) (transpose_reindex_obj C f B)
  intro t
  fin_cases t
  · exact map_heq_of_functor_eq (triangle_reindex C f 0) φ
  · exact map_heq_of_functor_eq (triangle_reindex C f 1) φ
  · exact map_heq_of_functor_eq (triangle_reindex C f 2) φ

/-- The actual whole transpose commutes with every original simplex
operator, using the original exact reindex functor on the target cofiber rows. -/
theorem relativeStageTranspose_reindex {a b : SimplexCategory} (f : a ⟶ b) :
    reindexStage (C := CofiberSequenceCategory C) f ⋙ relativeStageTranspose C a.len =
      relativeStageTranspose C b.len ⋙
        mapOfWaldhausenExact (reindexStage (C := C) f)
          (reindexStage_general_isWaldhausenExact C f) := by
  let R := reindexStage (C := C) f
  let hR := reindexStage_general_isWaldhausenExact C f
  let L := reindexStage (C := CofiberSequenceCategory C) f ⋙ relativeStageTranspose C a.len
  let M := relativeStageTranspose C b.len ⋙ mapOfWaldhausenExact R hR
  have hobj (A : Stage (CofiberSequenceCategory C) b.len) : L.obj A = M.obj A := by
    apply ObjectProperty.FullSubcategory.ext
    exact (transpose_reindex_obj C f A).trans
      (mapOfWaldhausenExact_obj R hR ((relativeStageTranspose C b.len).obj A)).symm
  change L = M
  apply Functor.hext
  · exact hobj
  · intro A B φ
    apply fullSubcategoryHom_heq (cofiberSequenceProperty (Stage C a.len))
      (hobj A) (hobj B)
    exact (transpose_reindex_map_heq C f φ).trans
      (mapOfWaldhausenExact_map_heq R hR ((relativeStageTranspose C b.len).map φ)).symm

/-- Degree zero retains the original relative zero stage and the original
cofiber category of actual zero stages. -/
@[no_expose]
def relativeStageTransposeZero :
    Stage (CofiberSequenceCategory C) 0 ⥤ CofiberSequenceCategory (Stage C 0) :=
  relativeStageTranspose C 0

/-- The same actual degree-zero functor satisfies the full relative exactness condition. -/
theorem relativeStageTransposeZero_isWaldhausenExact :
    (relativeStageTransposeZero C).IsWaldhausenExact :=
  relativeStageTranspose_isWaldhausenExact C 0

end CategoryTheory.Waldhausen.SConstruction.CofiberSequenceCategory

end
