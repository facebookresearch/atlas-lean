/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.BaselineConstantCoreComparison
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.ScalarCoreReplacementSpans
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.NatIso

/-!
# The natural derived universal mapping comparison for the original zero core

The actual groupoidal-source derived mapping functor has a natural weak
cospan to every independently fixed scalar replacement presentation. The
target category here consists of genuinely original-local-fibrant objects.
After localizing the scalar mapping-space values, the two actual weak legs
give a natural isomorphism. This is not a strict isomorphism of raw simplicial
sets and does not select a reverse weak representative.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra MonoidalClosed Opposite
open SimplicialPresheaf.InjectiveKan SimplicialPresheaf.OriginalLocalDerived
open scoped SSet.modelCategoryQuillen

namespace SimplicialPresheaf.CoreUniversalMapping

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D] {I : Type i}

/-- The actual original local-fibrant predicate, without a universal-property field. -/
def localObjectProperty (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    ObjectProperty (SimplicialPresheaf.{u} D) :=
  isOriginalLocalFibrant S

/-- The full category of actual original-local-fibrant targets. -/
abbrev LocalTargets (S : I → Arrow (SimplicialPresheaf.{u} D)) :=
  (localObjectProperty S).FullSubcategory

variable [Small.{u} I]

/-- The actual derived mapping functor from the existing baseline groupoidal source. -/
def groupoidalMapping (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    SSet.{u}ᵒᵖ ⥤ SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  (BaselineConstantCoreComparison.constantReplacement (D := D)).op ⋙ localDerivedEnd S

/-- Package the already proved source and target equations for the actual baseline unit and gamma. -/
def baselineComparison (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D) :
    groupoidalMapping S ⟶ ScalarCoreReplacementSpans.transferredMapping S z where
  app K :=
    { app C := BaselineConstantCoreComparison.comparison S z K.unop C
      naturality C C' f := BaselineConstantCoreComparison.comparison_target S z K.unop f }
  naturality K L k := by
    apply NatTrans.ext
    funext C
    exact BaselineConstantCoreComparison.comparison_source S z k.unop C

/-- The full comparison into the common scalar presentation keeps every actual forward leg. -/
def toCommon (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    groupoidalMapping S ⟶ ScalarCoreReplacementSpans.commonMapping S z e :=
  baselineComparison S z ≫ ScalarCoreReplacementSpans.transferredToCommon S z e

/-- The groupoidal comparison is the actual baseline-unit map followed by the actual scalar span. -/
theorem toCommon_app (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) (K : SSet.{u})
    (C : SimplicialPresheaf.{u} D) :
    ((toCommon S z e).app (op K)).app C =
      BaselineConstantCoreComparison.comparison S z K C ≫
        ((ScalarCoreReplacementSpans.transferredToCommon S z e).app (op K)).app C := rfl

/-- Both original forward parts of the universal comparison are weak. -/
theorem toCommon_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C : SimplicialPresheaf.{u} D) :
    SSet.realizationWeakEquivalences (((toCommon S z e).app (op K)).app C) :=
  SSet.realizationWeakEquivalences.comp_mem _ _
    (BaselineConstantCoreComparison.comparison_weak S hz K C)
    (ScalarCoreReplacementSpans.transferredToCommon_weak S hz e K C)

/-- Restrict only the target variable to genuine original-local-fibrant objects. -/
def restrictTargets (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (SimplicialPresheaf.{u} D ⥤ SSet.{u}) ⥤ (LocalTargets S ⥤ SSet.{u}) :=
  (Functor.whiskeringLeft (LocalTargets S) (SimplicialPresheaf.{u} D) SSet.{u}).obj
    (localObjectProperty S).ι

/-- The actual local-target groupoidal mapping spaces. -/
def originalSpaces (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets S ⥤ SSet.{u} :=
  groupoidalMapping S ⋙ restrictTargets S

/-- The fixed scalar derived presentation of maps into the actual zero core. -/
def scalarSpaces (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets S ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.fixedMapping z e ⋙ restrictTargets S

/-- The common mapping spaces use precisely the prescribed P and T. -/
def commonSpaces (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    SSet.{u}ᵒᵖ ⥤ LocalTargets S ⥤ SSet.{u} :=
  ScalarCoreReplacementSpans.commonMapping S z e ⋙ restrictTargets S

/-- The left leg of the natural weak cospan on actual local-fibrant targets. -/
def originalToCommon (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    originalSpaces S ⟶ commonSpaces S z e :=
  Functor.whiskerRight (toCommon S z e) (restrictTargets S)

/-- The fixed scalar leg of the same natural weak cospan. -/
def scalarToCommon (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    scalarSpaces S z e ⟶ commonSpaces S z e :=
  Functor.whiskerRight (ScalarCoreReplacementSpans.fixedToCommon S z e) (restrictTargets S)

/-- Every left component is weak, with no universal-property premise. -/
theorem originalToCommon_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C : LocalTargets S) :
    SSet.realizationWeakEquivalences (((originalToCommon S z e).app (op K)).app C) :=
  toCommon_weak S hz e K C.obj

/-- Every fixed-side component is weak by the actual local-fibrant property of its target. -/
theorem scalarToCommon_weak (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u})
    (K : SSet.{u}) (C : LocalTargets S) :
    SSet.realizationWeakEquivalences (((scalarToCommon S z e).app (op K)).app C) :=
  ScalarCoreReplacementSpans.fixedToCommon_weak S hz e K C.obj C.property

/-- Scalar mapping-space values are localized at their actual realization weak equivalences. -/
def localizeValues (S : I → Arrow (SimplicialPresheaf.{u} D)) :
    (LocalTargets S ⥤ SSet.{u}) ⥤
      (LocalTargets S ⥤ SSet.realizationWeakEquivalences.{u}.Localization) :=
  (Functor.whiskeringRight (LocalTargets S) SSet.{u}
    SSet.realizationWeakEquivalences.{u}.Localization).obj SSet.realizationWeakEquivalences.Q

/-- The localized actual original derived mapping spaces. -/
def originalHoSpaces (S : I → Arrow (SimplicialPresheaf.{u} D)) :=
  originalSpaces S ⋙ localizeValues S

/-- The localized independently fixed scalar mapping presentation. -/
def scalarHoSpaces (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :=
  scalarSpaces S z e ⋙ localizeValues S

/-- The localized common mapping presentation. -/
def commonHoSpaces (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :=
  commonSpaces S z e ⋙ localizeValues S

/-- Localize the actual original-side weak leg, without selecting another representative. -/
def originalHoToCommon (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    originalHoSpaces S ⟶ commonHoSpaces S z e :=
  Functor.whiskerRight (originalToCommon S z e) (localizeValues S)

/-- Localize the actual fixed scalar weak leg. -/
def scalarHoToCommon (S : I → Arrow (SimplicialPresheaf.{u} D)) (z : D)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    scalarHoSpaces S z e ⟶ commonHoSpaces S z e :=
  Functor.whiskerRight (scalarToCommon S z e) (localizeValues S)

/-- Every original-side localized component is an isomorphism because its prescribed map is weak. -/
theorem originalHoToCommon_isIso (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    IsIso (originalHoToCommon S z e) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro C
  change IsIso (SSet.realizationWeakEquivalences.Q.map
    (((originalToCommon S z e).app K).app C))
  exact Localization.inverts SSet.realizationWeakEquivalences.Q SSet.realizationWeakEquivalences
    _ (originalToCommon_weak S hz e K.unop C)

/-- The fixed-side localized components invert only the already proved actual weak maps. -/
theorem scalarHoToCommon_isIso (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    IsIso (scalarHoToCommon S z e) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro C
  change IsIso (SSet.realizationWeakEquivalences.Q.map
    (((scalarToCommon S z e).app K).app C))
  exact Localization.inverts SSet.realizationWeakEquivalences.Q SSet.realizationWeakEquivalences
    _ (scalarToCommon_weak S hz e K.unop C)

/-- The derived core mapping comparison is a natural iso of localized mapping-space values. -/
def mappingIso (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D} (hz : IsTerminal z)
    (e : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    originalHoSpaces S ≅ scalarHoSpaces S z e := by
  let _ : IsIso (originalHoToCommon S z e) := originalHoToCommon_isIso S hz e
  let _ : IsIso (scalarHoToCommon S z e) := scalarHoToCommon_isIso S hz e
  exact asIso (originalHoToCommon S z e) ≪≫ (asIso (scalarHoToCommon S z e)).symm

/-- Changing scalar conventions is implemented by the two actual natural mapping comparisons. -/
def changeScalarConventions (S : I → Arrow (SimplicialPresheaf.{u} D)) {z : D}
    (hz : IsTerminal z) (e e' : ScalarCoreReplacementSpans.ScalarConventions.{u}) :
    scalarHoSpaces S z e ≅ scalarHoSpaces S z e' :=
  (mappingIso S hz e).symm ≪≫ mappingIso S hz e'

end SimplicialPresheaf.CoreUniversalMapping
