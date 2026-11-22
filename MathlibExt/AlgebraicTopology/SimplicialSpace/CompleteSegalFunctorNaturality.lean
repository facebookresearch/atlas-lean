/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorReplacement

/-!
# The natural one-fold functor-core comparison

The specified closed comparison is a natural transformation of the actual
source-contravariant, target-covariant functor objects. On genuine complete
CSS endpoints its core map is weak, so the actual scalar localization gives
one natural Iso of both variables. No replacement factor is changed.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.FirstProjection

/-- The right image of the full CSS internal functor object, in both variables. -/
def cssFunctorObjects : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  MonoidalClosed.internalHom ⋙
    (Functor.whiskeringRight SimplicialSpace.{u} SimplicialSpace.{u} SSet.{u}).obj right

/-- The actual native Joyal functor objects of the same first right images. -/
def nativeFunctorObjects : SimplicialSpace.{u}ᵒᵖ ⥤ SimplicialSpace.{u} ⥤ SSet.{u} :=
  right.op ⋙ MonoidalClosed.internalHom ⋙
    (Functor.whiskeringLeft SimplicialSpace.{u} SSet.{u} SSet.{u}).obj right

/-- The canonical closed comparison is natural in the entire source and target diagram. -/
def comparisonNatTrans : cssFunctorObjects.{u} ⟶ nativeFunctorObjects.{u} where
  app W :=
    { app V := comparison W.unop V
      naturality V U g := comparison_target W.unop g }
  naturality W V f := by
    apply NatTrans.ext
    funext U
    exact comparison_source f.unop U

/-- Both variables keep their exact literal comparison maps. -/
theorem comparisonNatTrans_app (W V : SimplicialSpace.{u}) :
    (comparisonNatTrans.app (op W)).app V = comparison W V := rfl

private def postCore : (SimplicialSpace.{u} ⥤ SSet.{u}) ⥤ (SimplicialSpace.{u} ⥤ SSet.{u}) :=
  (Functor.whiskeringRight SimplicialSpace.{u} SSet.{u} SSet.{u}).obj SSet.coreFunctor

/-- The actual CSS functor cores form the same two-variable diagram. -/
def cssFunctorCores := cssFunctorObjects.{u} ⋙ postCore.{u}

/-- Native functor cores use the equivalence-edge core of the actual Joyal powers. -/
def nativeFunctorCores := nativeFunctorObjects.{u} ⋙ postCore.{u}

/-- The original categorical comparison restricts to its literal two-variable core map. -/
def comparisonCoreNatTrans : cssFunctorCores.{u} ⟶ nativeFunctorCores.{u} :=
  Functor.whiskerRight comparisonNatTrans postCore

private abbrev Complete := OnefoldCoreComparison.CompleteTargets.{u}
private abbrev H : SSet.{u} ⥤ SSet.realizationWeakEquivalences.{u}.Localization :=
  SSet.realizationWeakEquivalences.Q

private def restrictAndLocalize :
    (SimplicialSpace.{u} ⥤ SSet.{u}) ⥤ (Complete.{u} ⥤ SSet.realizationWeakEquivalences.{u}.Localization) :=
  (Functor.whiskeringLeft Complete.{u} SimplicialSpace.{u} SSet.{u}).obj completeSegalSpaces.ι ⋙
    (Functor.whiskeringRight Complete.{u} SSet.{u} SSet.realizationWeakEquivalences.{u}.Localization).obj H

/-- The same CSS power-core diagram in the actual scalar homotopy category. -/
def cssFunctorCoreHo := completeSegalSpaces.{u}.ι.op ⋙ cssFunctorCores.{u} ⋙ restrictAndLocalize.{u}

/-- The same native Joyal functor-core diagram in the actual scalar homotopy category. -/
def nativeFunctorCoreHo := completeSegalSpaces.{u}.ι.op ⋙ nativeFunctorCores.{u} ⋙ restrictAndLocalize.{u}

/-- Localize the exact comparison, restricted only to genuinely complete endpoints. -/
def comparisonCoreHo : cssFunctorCoreHo.{u} ⟶ nativeFunctorCoreHo.{u} :=
  Functor.whiskerLeft completeSegalSpaces.ι.op
    (Functor.whiskerRight comparisonCoreNatTrans restrictAndLocalize)

/-- Every original core component is inverted by its proved weakness. -/
theorem comparisonCoreHo_isIso : IsIso comparisonCoreHo.{u} := by
  let _ : ∀ W : Complete.{u}ᵒᵖ, IsIso (comparisonCoreHo.app W) := fun W => by
    let _ : ∀ V : Complete.{u}, IsIso ((comparisonCoreHo.app W).app V) := fun V => by
      change IsIso (H.{u}.map (SSet.coreFunctor.map (comparison W.unop.obj V.obj)))
      exact Localization.inverts H.{u} SSet.realizationWeakEquivalences _
        (comparison_coreWeak W.unop.obj V.obj W.unop.property V.property)
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- A single natural Ho Iso identifies both entire one-fold functor-core diagrams. -/
def comparisonCoreNatIso : cssFunctorCoreHo.{u} ≅ nativeFunctorCoreHo.{u} := by
  let _ : IsIso comparisonCoreHo.{u} := comparisonCoreHo_isIso
  exact asIso comparisonCoreHo

/-- The natural Iso keeps the original localized weak comparison as its forward map. -/
theorem comparisonCoreNatIso_hom (W V : OnefoldCoreComparison.CompleteTargets.{u}) :
    (comparisonCoreNatIso.hom.app (op W)).app V =
      H.{u}.map (SSet.coreFunctor.map (comparison W.obj V.obj)) := rfl

private abbrev J : SSet.{u} ⥤ SSet.categoricalEquivalences.{u}.Localization :=
  SSet.categoricalEquivalences.Q

private def restrictAndLocalizeJoyal :
    (SimplicialSpace.{u} ⥤ SSet.{u}) ⥤ (Complete.{u} ⥤ SSet.categoricalEquivalences.{u}.Localization) :=
  (Functor.whiskeringLeft Complete.{u} SimplicialSpace.{u} SSet.{u}).obj completeSegalSpaces.ι ⋙
    (Functor.whiskeringRight Complete.{u} SSet.{u} SSet.categoricalEquivalences.{u}.Localization).obj J

/-- The actual CSS functor presentation, localized by the literal categorical weak class. -/
def cssFunctorHo := completeSegalSpaces.{u}.ι.op ⋙ cssFunctorObjects.{u} ⋙ restrictAndLocalizeJoyal.{u}

/-- The actual native Joyal functor quasicategories in that same localization. -/
def nativeFunctorHo := completeSegalSpaces.{u}.ι.op ⋙ nativeFunctorObjects.{u} ⋙ restrictAndLocalizeJoyal.{u}

private def comparisonHo : cssFunctorHo.{u} ⟶ nativeFunctorHo.{u} :=
  Functor.whiskerLeft completeSegalSpaces.ι.op
    (Functor.whiskerRight comparisonNatTrans restrictAndLocalizeJoyal)

/-- The categorical comparison identifies both full functor-category presentations naturally. -/
def comparisonNatIso : cssFunctorHo.{u} ≅ nativeFunctorHo.{u} := by
  let _ : ∀ W : Complete.{u}ᵒᵖ, IsIso (comparisonHo.app W) := fun W => by
    let _ : ∀ V : Complete.{u}, IsIso ((comparisonHo.app W).app V) := fun V => by
      change IsIso (J.{u}.map (comparison W.unop.obj V.obj))
      exact Localization.inverts J.{u} SSet.categoricalEquivalences _
        (comparison_categoricalEquivalence W.unop.obj V.obj W.unop.property V.property)
    exact NatIso.isIso_of_isIso_app _
  let _ : IsIso comparisonHo.{u} := NatIso.isIso_of_isIso_app _
  exact asIso comparisonHo

/-- Its forward arrow is precisely the original closed comparison in the Joyal localization. -/
theorem comparisonNatIso_hom (W V : OnefoldCoreComparison.CompleteTargets.{u}) :
    (comparisonNatIso.hom.app (op W)).app V = J.{u}.map (comparison W.obj V.obj) := rfl

end SimplicialSpace.FirstProjection
