/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalSmithCSSReplacement

/-!
# Derived mapping ends for the Smith Rezk localization

The Smith localization replacements define Kan derived mapping ends for arbitrary simplicial
spaces. Precomposition and postcomposition by Rezk weak equivalences induce realization weak
equivalences, and natural weak spans compare the localized and baseline derived choices through
a common raw end at the localized fibrant replacement.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite

namespace SimplicialSpace.OriginalSmithCSS
open SimplicialPresheaf.OriginalLocalDerived

/-- The actual original-family derived end, using its stored native Q and R. -/
def derivedEnd : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  forget.op ⋙ localDerivedEnd SSet.Rezk.localizingMap.{u} ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u}
      (SimplicialPresheaf.{u} SimplexCategory) SSet.{u}).obj forget

/-- The common raw end first uses the original Smith R. -/
def rawEndAtR : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  forget.op ⋙ rawAfterR SSet.Rezk.localizingMap.{u} ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u}
      (SimplicialPresheaf.{u} SimplexCategory) SSet.{u}).obj forget

/-- The baseline derived choice is retained at that actual Smith R target. -/
def baselineEndAtR : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  forget.op ⋙ baselineAfterR SSet.Rezk.localizingMap.{u} ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u}
      (SimplicialPresheaf.{u} SimplexCategory) SSet.{u}).obj forget

/-- The natural map from the raw end at Smith R to the localized derived end. -/
def localSpan : rawEndAtR.{u} ⟶ derivedEnd :=
  Functor.whiskerRight (Functor.whiskerLeft forget.op
    (localEndSpan SSet.Rezk.localizingMap.{u}))
      ((Functor.whiskeringLeft SimplicialSpace.{u}
        (SimplicialPresheaf.{u} SimplexCategory) SSet.{u}).obj forget)

/-- The natural map from the raw end at Smith R to the baseline derived end. -/
def baselineSpan : rawEndAtR.{u} ⟶ baselineEndAtR :=
  Functor.whiskerRight (Functor.whiskerLeft forget.op
    (baselineEndSpan SSet.Rezk.localizingMap.{u}))
      ((Functor.whiskeringLeft SimplicialSpace.{u}
        (SimplicialPresheaf.{u} SimplexCategory) SSet.{u}).obj forget)

/-- Both original factors remain the native choices from the localization package. -/
theorem derivedEnd_native (A B : SimplicialSpace.{u}) :
    (derivedEnd.obj (op A)).obj B =
      SimplicialPresheaf.innerHom
        ((localQ SSet.Rezk.localizingMap.{u}).obj A.diagram)
        ((localR SSet.Rezk.localizingMap.{u}).obj B.diagram) := rfl

/-- Contravariant action of the native derived end on a source map. -/
def derivedPrecomp {A B : SimplicialSpace.{u}} (f : A ⟶ B) (Y : SimplicialSpace.{u}) :
    (derivedEnd.obj (op B)).obj Y ⟶ (derivedEnd.obj (op A)).obj Y :=
  (derivedEnd.map f.op).app Y

/-- Covariant action of the native derived end on a target map. -/
def derivedPostcomp (A : SimplicialSpace.{u}) {X Y : SimplicialSpace.{u}} (g : X ⟶ Y) :
    (derivedEnd.obj (op A)).obj X ⟶ (derivedEnd.obj (op A)).obj Y :=
  (derivedEnd.obj (op A)).map g

theorem derivedEnd_kan (A B : SimplicialSpace.{u}) :
    SSet.KanComplex ((derivedEnd.obj (op A)).obj B) :=
  localDerivedEnd_isKan SSet.Rezk.localizingMap.{u} A.diagram B.diagram

/-- Global all-CSS weakness acts on the actual Q map in the source variable. -/
theorem derivedPrecomp_rezkWeak {A B : SimplicialSpace.{u}}
    (f : A ⟶ B) (hf : rezkWeakEquivalences f) (Y : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences (derivedPrecomp f Y) :=
  localDerivedPrecomp_localWeak SSet.Rezk.localizingMap.{u} f.hom
    ((SimplicialPresheaf.OriginalRezkLocalizer.coefficientLocalWeak_iff_rezkWeak f.hom).mpr hf)
    Y.diagram

/-- Covariance uses the actual R map and the original global local Whitehead theorem. -/
theorem derivedPostcomp_rezkWeak (A : SimplicialSpace.{u})
    {X Y : SimplicialSpace.{u}} (g : X ⟶ Y) (hg : rezkWeakEquivalences g) :
    SSet.realizationWeakEquivalences (derivedPostcomp A g) :=
  localDerivedPostcomp_localWeak SSet.Rezk.localizingMap.{u} A.diagram g.hom
    ((SimplicialPresheaf.OriginalRezkLocalizer.coefficientLocalWeak_iff_rezkWeak g.hom).mpr hg)

/-- The original raw-to-local and raw-to-baseline legs are both weak. Their
native Q/R choices are related by these maps and are not identified. -/
theorem spans_weak (A B : SimplicialSpace.{u}) :
    SSet.realizationWeakEquivalences ((localSpan.app (op A)).app B) ∧
      SSet.realizationWeakEquivalences ((baselineSpan.app (op A)).app B) :=
  localEndSpans_weak SSet.Rezk.localizingMap.{u} A.diagram B.diagram

/-- Source and target naturality belong to the actual two span transformations. -/
theorem spans_naturality {A B : SimplicialSpace.{u}} (f : A ⟶ B)
    {X Y : SimplicialSpace.{u}} (g : X ⟶ Y) :
    (∀ Z : SimplicialSpace.{u},
      (rawEndAtR.map f.op).app Z ≫ (localSpan.app (op A)).app Z =
        (localSpan.app (op B)).app Z ≫ derivedPrecomp f Z) ∧
    (∀ Z : SimplicialSpace.{u},
      (rawEndAtR.map f.op).app Z ≫ (baselineSpan.app (op A)).app Z =
        (baselineSpan.app (op B)).app Z ≫ (baselineEndAtR.map f.op).app Z) ∧
    (∀ Z : SimplicialSpace.{u},
      (rawEndAtR.obj (op Z)).map g ≫ (localSpan.app (op Z)).app Y =
        (localSpan.app (op Z)).app X ≫ derivedPostcomp Z g) ∧
    (∀ Z : SimplicialSpace.{u},
      (rawEndAtR.obj (op Z)).map g ≫ (baselineSpan.app (op Z)).app Y =
        (baselineSpan.app (op Z)).app X ≫ (baselineEndAtR.obj (op Z)).map g) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Z
    exact NatTrans.congr_app (localSpan.naturality f.op) Z
  · intro Z
    exact NatTrans.congr_app (baselineSpan.naturality f.op) Z
  · intro Z
    exact (localSpan.app (op Z)).naturality g
  · intro Z
    exact (baselineSpan.app (op Z)).naturality g

/-- Each span leg commutes with every original inner simplicial operator. -/
theorem spans_inner_naturality (A B : SimplicialSpace.{u})
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) :
    ((rawEndAtR.obj (op A)).obj B).map θ ≫ ((localSpan.app (op A)).app B).app m =
      ((localSpan.app (op A)).app B).app n ≫ ((derivedEnd.obj (op A)).obj B).map θ ∧
    ((rawEndAtR.obj (op A)).obj B).map θ ≫ ((baselineSpan.app (op A)).app B).app m =
      ((baselineSpan.app (op A)).app B).app n ≫ ((baselineEndAtR.obj (op A)).obj B).map θ :=
  ⟨((localSpan.app (op A)).app B).naturality θ,
    ((baselineSpan.app (op A)).app B).naturality θ⟩

end SimplicialSpace.OriginalSmithCSS
