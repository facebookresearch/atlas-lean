/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStage
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofiberTripleEvaluation
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeStageTransposeExact

/-!
# The actual interchange of the original double stages

The original curried interval diagram is flipped without changing any
cell or map. Original exact interval and cofiber-triple evaluations
admit its rows as stages in the other original axis.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open scoped ZeroObject

universe u v uD vD

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

private theorem cofiberSequenceProperty_of_iso
    {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
    {S T : ComposableArrows D 2} (e : S ≅ T) (hS : cofiberSequenceProperty D S) :
    cofiberSequenceProperty D T := by
  change IsCofiberSequence (S.map' 0 1) (S.map' 1 2) at hS
  change IsCofiberSequence (T.map' 0 1) (T.map' 1 2)
  obtain ⟨hi, z, q, hP⟩ := hS
  let e₀ := e.app (0 : Fin 3)
  let e₁ := e.app (1 : Fin 3)
  let e₂ := e.app (2 : Fin 3)
  have w₀ : S.map' 0 1 ≫ e₁.hom = e₀.hom ≫ T.map' 0 1 :=
    e.hom.naturality (homOfLE (show (0 : Fin 3) ≤ 1 by decide))
  have w₁ : S.map' 1 2 ≫ e₂.hom = e₁.hom ≫ T.map' 1 2 :=
    e.hom.naturality (homOfLE (show (1 : Fin 3) ≤ 2 by decide))
  have hi' : IsCofibration (T.map' 0 1) :=
    ((WaldhausenCategoryWithoutGluing.cofibrations (C := D)).arrow_mk_iso_iff
      (Arrow.isoMk e₀ e₁ w₀.symm)).mp hi
  refine ⟨hi', e₀.inv ≫ z, q ≫ e₂.hom, ?_⟩
  apply hP.of_iso e₀ (Iso.refl _) e₁ e₂
  · simp
  · exact w₀
  · simp
  · exact w₁

/-- The original curried diagram, with its scalar stages admitted in the other axis. -/
def doubleStageTransposeDiagram (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    Stage (Stage C n) m → (Ar n ⥤ Stage C m) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A
  exact (stageProperty C m).lift ((A.obj ⋙ forget C n).flip) (fun x => by
    change IsStage m (A.obj ⋙ eval C n x)
    exact (evalIsGeneralStageWaldhausenExact C n x).isStage_postcomp m A.obj A.property)

/-- Every original double morphism gives the same coefficient map between the flipped rows. -/
def doubleStageTransposeDiagramMap (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (_φ : A ⟶ B),
      doubleStageTransposeDiagram C m n A ⟶ doubleStageTransposeDiagram C m n B := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ
  exact {
    app x := ObjectProperty.homMk {
      app y := (φ.hom.app y).hom.app x
      naturality y y' f := congrArg (fun η => η.hom.app x) (φ.hom.naturality f) }
    naturality x x' f := by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext y
      exact (φ.hom.app y).hom.naturality f }

/-- Original cofiber-triple evaluation admits the full flipped diagram as an original stage. -/
theorem doubleStageTransposeDiagram_isStage (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ A : Stage (Stage C n) m, IsStage n (doubleStageTransposeDiagram C m n A) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A
  constructor
  · intro i
    apply IsZero.of_full_of_faithful_of_isZero (forget C m)
    apply Functor.isZero
    intro y
    change IsZero ((A.obj.obj y).obj.obj (diag i))
    exact (A.obj.obj y).property.diag_isZero i
  · intro i j k hij hjk
    let := CofiberSequenceCategory.relativeWaldhausenCategory C
    let := generalStageHasZeroObject (CofiberSequenceCategory C) m
    let := generalStageWaldhausenCategory (CofiberSequenceCategory C) m
    let hT := stageCofiberTripleEvaluation_isWaldhausenExact C n hij hjk
    let A' := (hT.mapStage m).obj A
    let S := (CofiberSequenceCategory.relativeStageTranspose C m).obj A'
    let D := doubleStageTransposeDiagram C m n A
    let Q : ComposableArrows (Stage C m) 2 :=
      ComposableArrows.mk₂ (D.map (horiz hij hjk)) (D.map (vert hij hjk))
    let L : ComposableArrows (Ar m ⥤ C) 2 :=
      (A'.obj ⋙ CofiberSequenceCategory.forget C).flip
    let R : ComposableArrows (Ar m ⥤ C) 2 := Q ⋙ forget C m
    have h₀ : L.obj' 0 = R.obj' 0 := rfl
    have h₁ : L.obj' 1 = R.obj' 1 := rfl
    have h₂ : L.obj' 2 = R.obj' 2 := rfl
    have hLR : L = R := by
      refine ComposableArrows.ext₂ h₀ h₁ h₂ ?_ ?_
      · apply NatTrans.ext
        funext y
        simp only [NatTrans.comp_app, eqToHom_app]
        change (A.obj.obj y).obj.map (horiz hij hjk) =
          𝟙 _ ≫ (A.obj.obj y).obj.map (horiz hij hjk) ≫ 𝟙 _
        simp
      · apply NatTrans.ext
        funext y
        simp only [NatTrans.comp_app, eqToHom_app]
        change (A.obj.obj y).obj.map (vert hij hjk) =
          𝟙 _ ≫ (A.obj.obj y).obj.map (vert hij hjk) ≫ 𝟙 _
        simp
    have hForget : S.obj ⋙ forget C m = Q ⋙ forget C m :=
      (CofiberSequenceCategory.relativeStageTranspose_obj_forget C m A').trans hLR
    let F := (Functor.whiskeringRight (Fin 3) (Stage C m) (Ar m ⥤ C)).obj (forget C m)
    let e : S.obj ≅ Q := F.preimageIso (eqToIso hForget)
    exact cofiberSequenceProperty_of_iso e S.property

/-- Interchange the two original stage axes, retaining every original interval cell and map. -/
def doubleStageTransposeFunctor (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    Stage (Stage C n) m ⥤ Stage (Stage C m) n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  exact {
    obj A := ⟨doubleStageTransposeDiagram C m n A, doubleStageTransposeDiagram_isStage C m n A⟩
    map φ := ObjectProperty.homMk (doubleStageTransposeDiagramMap C m n φ)
    map_id A := by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext x
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext y
      rfl
    map_comp φ ψ := by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext x
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext y
      rfl }

/-- Every target cell is the same original cell with the two indices interchanged. -/
theorem doubleStageTransposeFunctor_obj_cell (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ (A : Stage (Stage C n) m) (x : Ar n) (y : Ar m),
      (((doubleStageTransposeFunctor C m n).obj A).obj.obj x).obj.obj y =
        (A.obj.obj y).obj.obj x := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A x y
  rfl

/-- The target inner map is the original outer diagram coefficient at the given inner cell. -/
theorem doubleStageTransposeFunctor_obj_innerMap (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ (A : Stage (Stage C n) m) (x : Ar n) {y y' : Ar m} (f : y ⟶ y'),
      (((doubleStageTransposeFunctor C m n).obj A).obj.obj x).obj.map f =
        (A.obj.map f).hom.app x := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A x y y' f
  rfl

/-- The target outer map is the original inner diagram coefficient at the given outer cell. -/
theorem doubleStageTransposeFunctor_obj_outerMap (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ (A : Stage (Stage C n) m) {x x' : Ar n} (f : x ⟶ x') (y : Ar m),
      (((doubleStageTransposeFunctor C m n).obj A).obj.map f).hom.app y =
        (A.obj.obj y).obj.map f := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A x x' f y
  rfl

/-- The actual mapped morphism retains every original double-diagram coefficient. -/
theorem doubleStageTransposeFunctor_map_cell (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B) (x : Ar n) (y : Ar m),
      (((doubleStageTransposeFunctor C m n).map φ).hom.app x).hom.app y =
        (φ.hom.app y).hom.app x := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ x y
  rfl

/-- Interchanging the actual original axes twice recovers the whole original functor. -/
theorem doubleStageTransposeFunctor_involution (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    doubleStageTransposeFunctor C m n ⋙ doubleStageTransposeFunctor C n m =
      𝟭 (Stage (Stage C n) m) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  rfl


/-- The literal original axis swaps have the actual identity inverse families. -/
def doubleStageTransposeEquivalence (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    Stage (Stage C n) m ≌ Stage (Stage C m) n := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  exact {
    functor := doubleStageTransposeFunctor C m n
    inverse := doubleStageTransposeFunctor C n m
    unitIso := Iso.refl _
    counitIso := Iso.refl _
    functor_unitIso_comp := by
      intro A
      change (doubleStageTransposeFunctor C m n).map (𝟙 A) ≫
          𝟙 ((doubleStageTransposeFunctor C m n).obj A) =
        𝟙 ((doubleStageTransposeFunctor C m n).obj A)
      rw [Functor.map_id, Category.id_comp] }

/-- Every genuine original double-stage corner supplies the genuine corner in the other axis. -/
theorem doubleStageTransposeFunctor_stageCofibrations (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B),
      stageCofibrations (Stage C n) m φ →
        stageCofibrations (Stage C m) n ((doubleStageTransposeFunctor C m n).map φ) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  intro A B φ hφ
  have hφ' : IsCofibration φ :=
    (isCofibration_generalStageWaldhausenCategory_iff (Stage C n) m φ).mpr hφ
  intro s
  let hij := s.castSucc_le_succ
  let H := StageZeroRowCofiber.certificate C n hij
  let F₀ := H.sourceExact.mapStage m
  let F₁ := H.middleExact.mapStage m
  let i := H.sourceExact.mapStageNatTrans H.middleExact
    (StageZeroRowCofiber.inclusion C n hij) m
  let HS := H.mapStage m
  have hAi : i.app A = ((doubleStageTransposeFunctor C m n).obj A).zeroRowSuccMap s := by
    apply ObjectProperty.hom_ext
    exact H.mapStage_firstArrow_app_hom m A
  have hBi : i.app B = ((doubleStageTransposeFunctor C m n).obj B).zeroRowSuccMap s := by
    apply ObjectProperty.hom_ext
    exact H.mapStage_firstArrow_app_hom m B
  rw [← hAi, ← hBi]
  change ∃ (P : Stage C m) (l : F₁.obj A ⟶ P) (r : F₀.obj B ⟶ P) (d : P ⟶ F₁.obj B),
    IsPushout (i.app A) (F₀.map φ) l r ∧
      l ≫ d = F₁.map φ ∧ r ≫ d = i.app B ∧ IsCofibration d
  let : HasPushout (i.app A) (F₀.map φ) := by
    obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout
      (C := Stage C m) (i.app A) (HS.objectwise A).1 (F₀.obj B) (F₀.map φ)
    exact hP.flip.hasPushout
  refine ⟨pushout (i.app A) (F₀.map φ), pushout.inl _ _, pushout.inr _ _,
    pushout.desc (F₁.map φ) (i.app B) (i.naturality φ).symm,
    IsPushout.of_hasPushout _ _, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _, ?_⟩
  exact HS.baseCofibration φ hφ'

/-- The original double-stage weak predicate is retained after the two indices are swapped. -/
theorem doubleStageTransposeFunctor_stageWeak (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B),
      stageWeak (Stage C n) m φ →
        stageWeak (Stage C m) n ((doubleStageTransposeFunctor C m n).map φ) := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ hφ x
  apply (isWeakEquivalence_generalStageWaldhausenCategory_iff C m _).mpr
  intro y
  exact (isWeakEquivalence_generalStageWaldhausenCategory_iff C n (φ.hom.app y)).mp (hφ y) x

/-- The actual original axis-swap functor is Waldhausen exact for all named original values. -/
theorem doubleStageTransposeFunctor_isWaldhausenExact (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject (Stage C n) m;
    letI := generalStageWaldhausenCategory (Stage C n) m;
    letI := generalStageHasZeroObject (Stage C m) n;
    letI := generalStageWaldhausenCategory (Stage C m) n;
    (doubleStageTransposeFunctor C m n).IsWaldhausenExact := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  let := generalStageHasZeroObject (Stage C m) n
  let := generalStageWaldhausenCategory (Stage C m) n
  let F := doubleStageTransposeFunctor C m n
  let : F.IsEquivalence := (doubleStageTransposeEquivalence C m n).isEquivalence_functor
  constructor
  · intro A hA
    let : HasZeroMorphisms (Stage (Stage C n) m) := (isZero_zero _).hasZeroMorphisms
    let : HasZeroMorphisms (Stage (Stage C m) n) := (isZero_zero _).hasZeroMorphisms
    let := Functor.preservesZeroMorphisms_of_full F
    exact F.map_isZero hA
  · intro A B φ hφ
    exact (isCofibration_generalStageWaldhausenCategory_iff (Stage C m) n _).mpr
      (doubleStageTransposeFunctor_stageCofibrations C m n φ
        ((isCofibration_generalStageWaldhausenCategory_iff (Stage C n) m φ).mp hφ))
  · intro A B φ hφ
    exact (isWeakEquivalence_generalStageWaldhausenCategory_iff (Stage C m) n _).mpr
      (doubleStageTransposeFunctor_stageWeak C m n φ
        ((isWeakEquivalence_generalStageWaldhausenCategory_iff (Stage C n) m φ).mp hφ))
  · intro A B A' P i f l r _hi hP
    exact hP.map F


/-- Both original genuine corner predicates agree through the actual inverse axis swap. -/
theorem doubleStageTransposeFunctor_stageCofibrations_iff (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B),
      stageCofibrations (Stage C m) n ((doubleStageTransposeFunctor C m n).map φ) ↔
        stageCofibrations (Stage C n) m φ := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ
  constructor
  · exact doubleStageTransposeFunctor_stageCofibrations C n m
      ((doubleStageTransposeFunctor C m n).map φ)
  · exact doubleStageTransposeFunctor_stageCofibrations C m n φ

/-- Both original weak predicates agree through the actual inverse axis swap. -/
theorem doubleStageTransposeFunctor_stageWeak_iff (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ {A B : Stage (Stage C n) m} (φ : A ⟶ B),
      stageWeak (Stage C m) n ((doubleStageTransposeFunctor C m n).map φ) ↔
        stageWeak (Stage C n) m φ := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A B φ
  constructor
  · exact doubleStageTransposeFunctor_stageWeak C n m
      ((doubleStageTransposeFunctor C m n).map φ)
  · exact doubleStageTransposeFunctor_stageWeak C m n φ

/-- The inverse functor of the actual original equivalence is Waldhausen exact. -/
theorem doubleStageTransposeEquivalence_inverse_isWaldhausenExact (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    letI := generalStageHasZeroObject (Stage C n) m;
    letI := generalStageWaldhausenCategory (Stage C n) m;
    letI := generalStageHasZeroObject (Stage C m) n;
    letI := generalStageWaldhausenCategory (Stage C m) n;
    (doubleStageTransposeEquivalence C m n).inverse.IsWaldhausenExact := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  let := generalStageHasZeroObject (Stage C n) m
  let := generalStageWaldhausenCategory (Stage C n) m
  let := generalStageHasZeroObject (Stage C m) n
  let := generalStageWaldhausenCategory (Stage C m) n
  exact doubleStageTransposeFunctor_isWaldhausenExact C n m

/-- The actual original unit family has the identity whole double-stage component. -/
theorem doubleStageTransposeEquivalence_unitIso_hom_app (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ A : Stage (Stage C n) m,
      (doubleStageTransposeEquivalence C m n).unitIso.hom.app A = 𝟙 A := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A
  rfl

/-- The actual original counit family has the identity whole double-stage component. -/
theorem doubleStageTransposeEquivalence_counitIso_hom_app (m n : ℕ) :
    letI := generalStageHasZeroObject C n;
    letI := generalStageWaldhausenCategory C n;
    letI := generalStageHasZeroObject C m;
    letI := generalStageWaldhausenCategory C m;
    ∀ A : Stage (Stage C m) n,
      (doubleStageTransposeEquivalence C m n).counitIso.hom.app A = 𝟙 A := by
  let := generalStageHasZeroObject C n
  let := generalStageWaldhausenCategory C n
  let := generalStageHasZeroObject C m
  let := generalStageWaldhausenCategory C m
  intro A
  rfl

end CategoryTheory.Waldhausen.SConstruction

end

