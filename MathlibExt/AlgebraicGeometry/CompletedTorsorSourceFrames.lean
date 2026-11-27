/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AffinoidTorsorAlgebraizationModels

/-!
# Source integral frames and their actual completed pullbacks

An algebraized frame is an equivariant isomorphism of the original
algebraized action sheaf. Its normalization fixes every analytic test
through the source algebraization comparison. The formal frame is then
computed by native fpqc pullback along the original completion unit.
The generic frame uses the original parameter localization.

Source: Fargues--Scholze, arXiv:2102.13459v4, Sections III.3 and VI.1.
Native represented group sheaves and restriction are reused. Existence
of source frames is a separate construction request.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CompletedTorsorSourceFrames

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open AnalyticGroupTorsorSites AnalyticBundlePrestackModels AnalyticBundleModifications
open AnalyticMeromorphicCoordinates MeromorphicHeckeModels AffinoidTorsorAlgebraizationModels
open AnalyticTateAdicModels
open MathlibExt.CategoryTheory.SheafTorsorGroupoids

variable (p : ℕ) [Fact p.Prime] (E : Type) [Field E]
  (G : Over (Spec (.of E))) [GrpObj G]
  (H : ∀ V : ESpace p E, GroupDescent p E G V)
  (P : PullbackPreservation p E G H)
  {X D : ESpace p E} (d : D ⟶ X) (U : Puncture p E d)
  (Q : PoleChart p E d U)
  (A : Algebraization p E G H Q.space)
  (B : FpqcPreservesTorsors E G (completionBaseMap p E d U Q))

/-- An `eqToHom` of valued spaces identifies the topological section rings. -/
theorem sectionsHomeomorphic_eqToHom {A B : AnalyticTateAdicModels.ValuedSpace}
    (h : A = B) : AnalyticTateAdicModels.SectionsHomeomorphic (eqToHom h).val := by
  subst h
  intro U _
  change @IsHomeomorph _ _ (A.sectionTopology U) (A.sectionTopology U) id
  exact @IsHomeomorph.id _ (A.sectionTopology U)

/-- The actual whole affinoid chart, obtained from the displayed source model equality. -/
def wholePoleChart : AnalyticDiamondEtaleSites.Chart p Q.space.left where
  pair := Q.pair
  model := Q.model
  map := eqToHom Q.model_same.symm
  open_embedding :=
    (TopCat.homeoOfIso ((forgetValuations ⋙ LocallyRingedSpace.forgetToTop).mapIso
      (eqToIso Q.model_same.symm))).isOpenEmbedding
  stalk_iso x := by
    have : IsIso (forgetValuations.map (eqToHom Q.model_same.symm)) := by infer_instance
    change IsIso ((forgetValuations.map (eqToHom Q.model_same.symm)).stalkMap x)
    unfold LocallyRingedSpace.Hom.stalkMap
    infer_instance
  sections := sectionsHomeomorphic_eqToHom _

instance wholePoleChart_isIso : IsIso (wholePoleChart p E d U Q).map := by
  dsimp [wholePoleChart]
  infer_instance

/-- A frame is fixed on every original analytic coefficient test. -/
structure AlgebraizedFrame (N : Bundles p E G H X)
    (f : IntegralFrame p E G H d U Q N) where
  frame :
    (WittDiscTorsorModels.torsorActions E G (coefficientScheme p E Q.space)).obj
      (A.functor.obj ((bundlePullback p E G H P Q.map).obj N)) ≅
        WittDiscTorsorModels.regularAction E G (coefficientScheme p E Q.space)
  normalized : ∀ (T : Site p E Q.space)
    (x : (algebraicPresheaf p E G Q.space
      (A.functor.obj ((bundlePullback p E G H P Q.map).obj N))).obj (op T)),
    frame.hom.val.hom.app (op ((coefficientTests p E Q.space).obj T)) x =
      ULift.up (f.hom.val.hom.app (op T)
        (((A.comparison ((bundlePullback p E G H P Q.map).obj N)).hom.app (op T) x).down))

/-- Native represented regular actions restrict to the same regular action. -/
def regularPullback {V W : Over (Spec (.of E))} (f : V ⟶ W) :
    (WittDiscTorsorModels.actionPullback G f).obj
      (WittDiscTorsorModels.regularAction E G W) ≅
        WittDiscTorsorModels.regularAction E G V := Iso.refl _

/-- Completion of an original integral frame uses the actual source action map. -/
def formalFrame {N : Bundles p E G H X}
    {f : IntegralFrame p E G H d U Q N}
    (F : AlgebraizedFrame p E G H P d U Q A N f) :
    (WittDiscTorsorModels.torsorActions E G (positiveScheme p E d U Q)).obj
      ((completedTorsors p E G H P d U Q A B).obj N) ≅
        WittDiscTorsorModels.regularAction E G (positiveScheme p E d U Q) :=
  (WittDiscTorsorModels.actionPullback G (completionBaseMap p E d U Q)).mapIso F.frame ≪≫
    regularPullback E G (completionBaseMap p E d U Q)

/-- The generic frame is that same frame restricted along the actual localization. -/
def genericFrame {N : Bundles p E G H X}
    {f : IntegralFrame p E G H d U Q N}
    (F : AlgebraizedFrame p E G H P d U Q A N f) :
    (genericActions p E G d U Q).obj ((completedTorsors p E G H P d U Q A B).obj N) ≅
      WittDiscTorsorModels.regularAction E G (genericScheme p E d U Q) :=
  (WittDiscTorsorModels.actionPullback G (localization p E d U Q)).mapIso
      (formalFrame p E G H P d U Q A B F) ≪≫
    regularPullback E G (localization p E d U Q)

omit [Fact p.Prime] in
/-- Every formal test uses the original algebraized frame at its actual completion pullback. -/
theorem formalFrame_sections {N : Bundles p E G H X}
    {f : IntegralFrame p E G H d U Q N}
    (F : AlgebraizedFrame p E G H P d U Q A N f)
    (T : WittDiscTorsorModels.Site E (positiveScheme p E d U Q)) :
    (formalFrame p E G H P d U Q A B F).hom.val.hom.app (op T) =
      F.frame.hom.val.hom.app
        (op ((Over.map (completionBaseMap p E d U Q)).obj T)) := rfl

omit [Fact p.Prime] in
/-- Every generic test uses that same frame and the actual two coefficient maps. -/
theorem genericFrame_sections {N : Bundles p E G H X}
    {f : IntegralFrame p E G H d U Q N}
    (F : AlgebraizedFrame p E G H P d U Q A N f)
    (T : WittDiscTorsorModels.Site E (genericScheme p E d U Q)) :
    (genericFrame p E G H P d U Q A B F).hom.val.hom.app (op T) =
      F.frame.hom.val.hom.app
        (op ((Over.map (completionBaseMap p E d U Q)).obj
          ((Over.map (localization p E d U Q)).obj T))) := rfl

end MathlibExt.AlgebraicGeometry.CompletedTorsorSourceFrames
