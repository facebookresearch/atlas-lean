/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionSmithComparisonData
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSmithCSSDerivedMapping

/-!
# Natural spans between completion-derived mapping ends

The units of diagonal completion and Smith replacement induce natural spans of Smith-derived
mapping ends while retaining their native replacement choices. All five ends are Kan, all four
legs are natural in source, target and inner simplicial operators, and the Smith replacement
legs are realization weak equivalences.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite

namespace SimplicialSpace.RezkCompletionSmithComparison
open OriginalSmithCSS

/-- The middle retains Q of the SAME completion source and R of the original target. -/
def completionMiddleEnd : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  RezkCompletionData.completion.op ⋙ derivedEnd

/-- The native derived end evaluated at SAME completion in both variables. -/
def completionEnd : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  RezkCompletionData.completion.op ⋙ derivedEnd ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u} SimplicialSpace.{u} SSet.{u}).obj
      RezkCompletionData.completion

/-- The other middle retains the independently constructed Smith replacement source. -/
def smithMiddleEnd : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  OriginalSmithCSS.replacement.op ⋙ derivedEnd

/-- The native derived end evaluated at full-E Smith replacement in both variables. -/
def smithEnd : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  OriginalSmithCSS.replacement.op ⋙ derivedEnd ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u} SimplicialSpace.{u} SSet.{u}).obj
      OriginalSmithCSS.replacement

private def sourceUnitSpan (F : SimplicialSpace.{u} ⥤ SimplicialSpace.{u})
    (η : 𝟭 SimplicialSpace.{u} ⟶ F) : F.op ⋙ derivedEnd ⟶ derivedEnd :=
  Functor.whiskerRight (NatTrans.op η) derivedEnd

private def targetUnitSpan (F : SimplicialSpace.{u} ⥤ SimplicialSpace.{u})
    (η : 𝟭 SimplicialSpace.{u} ⟶ F) :
    F.op ⋙ derivedEnd ⟶ F.op ⋙ derivedEnd ⋙
      (Functor.whiskeringLeft SimplicialSpace.{u} SimplicialSpace.{u} SSet.{u}).obj F where
  app A := Functor.whiskerRight η (derivedEnd.obj (F.op.obj A))
  naturality A B f := by
    apply NatTrans.ext
    funext Y
    exact ((derivedEnd.map (F.op.map f)).naturality (η.app Y)).symm

/-- The contravariant source span induced by the SAME completion unit. -/
def completionPreSpan : completionMiddleEnd.{u} ⟶ derivedEnd :=
  sourceUnitSpan RezkCompletionData.completion RezkCompletionData.unit

/-- The covariant target span induced by the SAME completion unit. -/
def completionPostSpan : completionMiddleEnd.{u} ⟶ completionEnd :=
  targetUnitSpan RezkCompletionData.completion RezkCompletionData.unit

/-- The contravariant source span induced by the full-E Smith replacement unit. -/
def smithPreSpan : smithMiddleEnd.{u} ⟶ derivedEnd :=
  sourceUnitSpan OriginalSmithCSS.replacement OriginalSmithCSS.unit

/-- The covariant target span induced by the full-E Smith replacement unit. -/
def smithPostSpan : smithMiddleEnd.{u} ⟶ smithEnd :=
  targetUnitSpan OriginalSmithCSS.replacement OriginalSmithCSS.unit

/-- All four legs are actions on the actual units, with their native Q/R values. -/
theorem span_components (A B : SimplicialSpace.{u}) :
    (completionPreSpan.app (op A)).app B =
      derivedPrecomp (RezkCompletionData.unit.app A) B ∧
    (completionPostSpan.app (op A)).app B =
      derivedPostcomp (RezkCompletionData.completion.obj A) (RezkCompletionData.unit.app B) ∧
    (smithPreSpan.app (op A)).app B = derivedPrecomp (OriginalSmithCSS.unit.app A) B ∧
    (smithPostSpan.app (op A)).app B =
      derivedPostcomp (OriginalSmithCSS.replacement.obj A) (OriginalSmithCSS.unit.app B) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The Smith comparison already gives a genuine natural weak span. -/
theorem smithSpans_weak (A B : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences ((smithPreSpan.app (op A)).app B) ∧
      SSet.realizationWeakEquivalences ((smithPostSpan.app (op A)).app B) :=
  ⟨derivedPrecomp_rezkWeak (OriginalSmithCSS.unit.app A) (OriginalSmithCSS.unit_rezkWeak A) B,
    derivedPostcomp_rezkWeak (OriginalSmithCSS.replacement.obj A)
      (OriginalSmithCSS.unit.app B) (OriginalSmithCSS.unit_rezkWeak B)⟩

theorem allEnds_kan (A B : SimplicialSpace.{u}) :
    SSet.KanComplex ((derivedEnd.obj (op A)).obj B) ∧
    SSet.KanComplex ((completionMiddleEnd.obj (op A)).obj B) ∧
    SSet.KanComplex ((completionEnd.obj (op A)).obj B) ∧
    SSet.KanComplex ((smithMiddleEnd.obj (op A)).obj B) ∧
    SSet.KanComplex ((smithEnd.obj (op A)).obj B) :=
  ⟨derivedEnd_kan A B,
    derivedEnd_kan (RezkCompletionData.completion.obj A) B,
    derivedEnd_kan (RezkCompletionData.completion.obj A) (RezkCompletionData.completion.obj B),
    derivedEnd_kan (OriginalSmithCSS.replacement.obj A) B,
    derivedEnd_kan (OriginalSmithCSS.replacement.obj A) (OriginalSmithCSS.replacement.obj B)⟩

theorem spans_source_naturality {A A' : SimplicialSpace.{u}}
    (f : A ⟶ A') (B : SimplicialSpace.{u}) :
    (completionMiddleEnd.map f.op).app B ≫ (completionPreSpan.app (op A)).app B =
      (completionPreSpan.app (op A')).app B ≫ (derivedEnd.map f.op).app B ∧
    (completionMiddleEnd.map f.op).app B ≫ (completionPostSpan.app (op A)).app B =
      (completionPostSpan.app (op A')).app B ≫ (completionEnd.map f.op).app B ∧
    (smithMiddleEnd.map f.op).app B ≫ (smithPreSpan.app (op A)).app B =
      (smithPreSpan.app (op A')).app B ≫ (derivedEnd.map f.op).app B ∧
    (smithMiddleEnd.map f.op).app B ≫ (smithPostSpan.app (op A)).app B =
      (smithPostSpan.app (op A')).app B ≫ (smithEnd.map f.op).app B :=
  ⟨NatTrans.congr_app (completionPreSpan.naturality f.op) B,
    NatTrans.congr_app (completionPostSpan.naturality f.op) B,
    NatTrans.congr_app (smithPreSpan.naturality f.op) B,
    NatTrans.congr_app (smithPostSpan.naturality f.op) B⟩

theorem spans_target_naturality (A : SimplicialSpace.{u})
    {B B' : SimplicialSpace.{u}} (g : B ⟶ B') :
    (completionMiddleEnd.obj (op A)).map g ≫ (completionPreSpan.app (op A)).app B' =
      (completionPreSpan.app (op A)).app B ≫ (derivedEnd.obj (op A)).map g ∧
    (completionMiddleEnd.obj (op A)).map g ≫ (completionPostSpan.app (op A)).app B' =
      (completionPostSpan.app (op A)).app B ≫ (completionEnd.obj (op A)).map g ∧
    (smithMiddleEnd.obj (op A)).map g ≫ (smithPreSpan.app (op A)).app B' =
      (smithPreSpan.app (op A)).app B ≫ (derivedEnd.obj (op A)).map g ∧
    (smithMiddleEnd.obj (op A)).map g ≫ (smithPostSpan.app (op A)).app B' =
      (smithPostSpan.app (op A)).app B ≫ (smithEnd.obj (op A)).map g :=
  ⟨(completionPreSpan.app (op A)).naturality g,
    (completionPostSpan.app (op A)).naturality g,
    (smithPreSpan.app (op A)).naturality g,
    (smithPostSpan.app (op A)).naturality g⟩

theorem spans_inner_naturality (A B : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((completionMiddleEnd.obj (op A)).obj B).map θ ≫ ((completionPreSpan.app (op A)).app B).app m =
      ((completionPreSpan.app (op A)).app B).app n ≫ ((derivedEnd.obj (op A)).obj B).map θ ∧
    ((completionMiddleEnd.obj (op A)).obj B).map θ ≫ ((completionPostSpan.app (op A)).app B).app m =
      ((completionPostSpan.app (op A)).app B).app n ≫ ((completionEnd.obj (op A)).obj B).map θ ∧
    ((smithMiddleEnd.obj (op A)).obj B).map θ ≫ ((smithPreSpan.app (op A)).app B).app m =
      ((smithPreSpan.app (op A)).app B).app n ≫ ((derivedEnd.obj (op A)).obj B).map θ ∧
    ((smithMiddleEnd.obj (op A)).obj B).map θ ≫ ((smithPostSpan.app (op A)).app B).app m =
      ((smithPostSpan.app (op A)).app B).app n ≫ ((smithEnd.obj (op A)).obj B).map θ :=
  ⟨((completionPreSpan.app (op A)).app B).naturality θ,
    ((completionPostSpan.app (op A)).app B).naturality θ,
    ((smithPreSpan.app (op A)).app B).naturality θ,
    ((smithPostSpan.app (op A)).app B).naturality θ⟩

end SimplicialSpace.RezkCompletionSmithComparison
