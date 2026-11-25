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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FunctorSequenceLift
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.CofiberRelativeStageCriterion
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality

/-!
# Weibel's source cofibration sequence of exact functors

Weibel V.Definition1.1(b) requires objectwise cofiber sequences AND that the
induced map from the base pushout is a cofibration for each source cofibration.
V.Theorem1.2 uses a short exact sequence in that definition. This source
property yields relative cofibrations, exactness of the original cofiber
lift, and all actual finite-stage corners internally. It is not a caller
stage-corner or lift-exactness outcome.

Primary source: retained Weibel K-book OCR, lines8659 and8665.
-/

public section

noncomputable section

open CategoryTheory Limits ZeroObject

universe uB vB uC vC

namespace CategoryTheory.Waldhausen.SConstruction

variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategoryWithoutGluing B]
variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- A cofibration sequence of exact functors in Weibel V.Definition1.1(b).
The base pushout and its evident map are the stock constructions, with the
instance earned internally from the original objectwise first cofibration. -/
structure IsWaldhausenCofiberFunctorSequence (F₀ F₁ F₂ : B ⥤ C)
    (i : F₀ ⟶ F₁) (p : F₁ ⟶ F₂) : Prop where
  /-- The original first functor is Waldhausen exact. -/
  sourceExact : F₀.IsWaldhausenExact
  /-- The original middle functor is Waldhausen exact. -/
  middleExact : F₁.IsWaldhausenExact
  /-- The original quotient functor is Waldhausen exact. -/
  quotientExact : F₂.IsWaldhausenExact
  /-- Each original object retains its cofiber sequence. -/
  objectwise : ∀ X : B, IsCofiberSequence (i.app X) (p.app X)
  /-- Source V.1.1(b)'s base-cofibration condition, before any stage or loop:
  F1(A) union over F0(A) F0(A') maps by the original naturality square to F1(A'). -/
  baseCofibration : ∀ {A A' : B} (f : A ⟶ A'), IsCofibration f →
    letI : HasPushout (i.app A) (F₀.map f) := (by
      obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
        (i.app A) (objectwise A).1 (F₀.obj A') (F₀.map f)
      exact hP.flip.hasPushout);
    IsCofibration (pushout.desc (F₁.map f) (i.app A') (i.naturality f).symm)

namespace IsWaldhausenCofiberFunctorSequence

variable {F₀ F₁ F₂ : B ⥤ C} {i : F₀ ⟶ F₁} {p : F₁ ⟶ F₂}
variable (H : IsWaldhausenCofiberFunctorSequence F₀ F₁ F₂ i p)

/-- The genuine source base condition earns each relative map of the
unchanged original cofiber lift on a source cofibration. -/
theorem map_relativeCofibration {A A' : B} (f : A ⟶ A') (hf : IsCofibration f) :
    CofiberSequenceCategory.relativeCofibrations C
      ((cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise).map f) := by
  let : HasPushout (i.app A) (F₀.map f) := by
    obtain ⟨_, _, _, hP, _⟩ := WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C)
      (i.app A) (H.objectwise A).1 (F₀.obj A') (F₀.map f)
    exact hP.flip.hasPushout
  apply (CofiberSequenceCategory.mem_relativeCofibrations_raw_iff C _).mpr
  change IsCofibration (F₀.map f) ∧
    ∃ (P : C) (inMiddle : F₁.obj A ⟶ P) (inSource : F₀.obj A' ⟶ P)
      (d : P ⟶ F₁.obj A'),
      IsPushout (i.app A) (F₀.map f) inMiddle inSource ∧
        inMiddle ≫ d = F₁.map f ∧ inSource ≫ d = i.app A' ∧ IsCofibration d
  exact ⟨H.sourceExact.map_cofibration f hf, pushout (i.app A) (F₀.map f),
    pushout.inl (i.app A) (F₀.map f), pushout.inr (i.app A) (F₀.map f),
    pushout.desc (F₁.map f) (i.app A') (i.naturality f).symm,
    IsPushout.of_hasPushout (i.app A) (F₀.map f),
    pushout.inl_desc _ _ _, pushout.inr_desc _ _ _, H.baseCofibration f hf⟩

/-- All original horizontal first-triple stage corners are derived by
applying the source base condition to the original source-stage cofibration. -/
theorem stage_corners (n : ℕ) (A : Stage B n)
    (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c) :
    CofiberSequenceCategory.relativeCofibrations C
      ((A.obj ⋙ cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise).map (horiz hab hbc)) :=
  H.map_relativeCofibration (A.obj.map (horiz hab hbc))
    (A.property.cofiber_triple hab hbc).1

/-- The original cofiber lift sends every original finite source stage
to a genuine relative stage, with all three evaluations and corners earned. -/
theorem isStage_lift (n : ℕ) (A : Stage B n) :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      CofiberSequenceCategory.relativeWaldhausenCategory C;
    IsStage n (A.obj ⋙ cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise) := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
    CofiberSequenceCategory.relativeWaldhausenCategory C
  let L := cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise
  apply (CofiberSequenceCategory.isStage_relative_iff_evaluations C n (A.obj ⋙ L)).mpr
  refine ⟨?_, ?_⟩
  · intro r
    fin_cases r
    · have hStage := H.sourceExact.isStage_postcomp n A.obj A.property
      have hEval : (A.obj ⋙ L) ⋙ CofiberSequenceCategory.source C = A.obj ⋙ F₀ :=
        (Functor.assoc _ _ _).trans
          (congrArg (fun F => A.obj ⋙ F)
            (cofiberFunctorSequenceLift_source F₀ F₁ F₂ i p H.objectwise))
      exact hEval.symm ▸ hStage
    · have hStage := H.middleExact.isStage_postcomp n A.obj A.property
      have hEval : (A.obj ⋙ L) ⋙ CofiberSequenceCategory.middle C = A.obj ⋙ F₁ :=
        (Functor.assoc _ _ _).trans
          (congrArg (fun F => A.obj ⋙ F)
            (cofiberFunctorSequenceLift_middle F₀ F₁ F₂ i p H.objectwise))
      exact hEval.symm ▸ hStage
    · have hStage := H.quotientExact.isStage_postcomp n A.obj A.property
      have hEval : (A.obj ⋙ L) ⋙ CofiberSequenceCategory.quotient C = A.obj ⋙ F₂ :=
        (Functor.assoc _ _ _).trans
          (congrArg (fun F => A.obj ⋙ F)
            (cofiberFunctorSequenceLift_quotient F₀ F₁ F₂ i p H.objectwise))
      exact hEval.symm ▸ hStage
  · intro a b c hab hbc
    exact H.stage_corners n A a b c hab hbc

/-- Source Definition1.1(b) internally gives the actual original exact
functor B to E(C); no lift-exactness outcome is supplied by a caller. -/
theorem lift_isWaldhausenExact :
    letI : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
      CofiberSequenceCategory.relativeWaldhausenCategory C;
    (cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise).IsWaldhausenExact := by
  let : WaldhausenCategoryWithoutGluing (CofiberSequenceCategory C) :=
    CofiberSequenceCategory.relativeWaldhausenCategory C
  let L := cofiberFunctorSequenceLift F₀ F₁ F₂ i p H.objectwise
  refine { map_isZero := ?_, map_cofibration := ?_, map_weakEquivalence := ?_, map_pushout := ?_ }
  · intro A hA
    apply IsZero.of_full_of_faithful_of_isZero (CofiberSequenceCategory.forget C)
    refine Functor.isZero _ (fun k => ?_)
    fin_cases k
    · change IsZero (F₀.obj A)
      exact H.sourceExact.map_isZero hA
    · change IsZero (F₁.obj A)
      exact H.middleExact.map_isZero hA
    · change IsZero (F₂.obj A)
      exact H.quotientExact.map_isZero hA
  · intro A A' f hf
    exact (CofiberSequenceCategory.isCofibration_relativeWaldhausenCategory_iff C (L.map f)).mpr
      (H.map_relativeCofibration f hf)
  · intro A A' f hf
    apply (CofiberSequenceCategory.isWeakEquivalence_relativeWaldhausenCategory_iff C (L.map f)).mpr
    apply (CofiberSequenceCategory.mem_levelwiseWeakEquivalences_iff C (L.map f)).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact (cofiberFunctorSequenceLift_source_map F₀ F₁ F₂ i p H.objectwise f).symm ▸
        H.sourceExact.map_weakEquivalence f hf
    · exact (cofiberFunctorSequenceLift_middle_map F₀ F₁ F₂ i p H.objectwise f).symm ▸
        H.middleExact.map_weakEquivalence f hf
    · exact (cofiberFunctorSequenceLift_quotient_map F₀ F₁ F₂ i p H.objectwise f).symm ▸
        H.quotientExact.map_weakEquivalence f hf
  · intro A A₁ A₂ A₃ iA f inl inr hi hP
    let : (CofiberSequenceCategory.forget C).Full := by infer_instance
    let : (CofiberSequenceCategory.forget C).Faithful := by infer_instance
    let : ReflectsColimit (span (L.map f) (L.map iA)) (CofiberSequenceCategory.forget C) :=
      by infer_instance
    apply IsPushout.of_map_of_faithful (CofiberSequenceCategory.forget C)
    apply IsPushout.of_forall_isPushout_app
    intro k
    fin_cases k
    · change IsPushout (F₀.map f) (F₀.map iA) (F₀.map inl) (F₀.map inr)
      exact H.sourceExact.map_pushout iA f inl inr hi hP
    · change IsPushout (F₁.map f) (F₁.map iA) (F₁.map inl) (F₁.map inr)
      exact H.middleExact.map_pushout iA f inl inr hi hP
    · change IsPushout (F₂.map f) (F₂.map iA) (F₂.map inl) (F₂.map inr)
      exact H.quotientExact.map_pushout iA f inl inr hi hP

end IsWaldhausenCofiberFunctorSequence

end CategoryTheory.Waldhausen.SConstruction

end
