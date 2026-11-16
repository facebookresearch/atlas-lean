/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRegularizedHiggsModels
public import MathlibExt.AlgebraicGeometry.CameralRamificationTensorModels

/-!
# Native incidence action and cameral G descent

The universal action is the actual adjoint action on both the centralizer
plane and the Borel plane. A regularizer's cameral cover is fixed by its
Cartesian pull to the actual incidence cover along sigma and G descent.
Both projections fix every pullback group/deck action. Reindex maps use
the actual torsor original map and the actual universal incidence point,
on every coefficient scheme.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 2 and 17.1--17.5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralCoverDescentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralIncidenceModels CameralRamificationReindexing
open CameralRamificationTensorModels CameralRegularizedHiggsModels
open GroupTorsorGeometry SchemeLieJetFamilies ExpansionParameterModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

abbrev incidenceTotal
    (C : UniversalCover F.borel F.centralizers F.flag F.chevalley.chevalley) := total F C.cameral
abbrev incidenceProjection
    (C : UniversalCover F.borel F.centralizers F.flag F.chevalley.chevalley) :=
  projection F C.cameral

structure IncidenceAction where
  incidence : UniversalCover F.borel F.centralizers F.flag F.chevalley.chevalley
  value : CartanValueMap incidence
  reuse : incidenceTotal F incidence ≅ total F F.universalCover.cameral
  reuse_projection : reuse.hom ≫ projection F F.universalCover.cameral =
    incidenceProjection F incidence
  reuse_points : ∀ (A : CommAlgCat.{0} ℂ) (z : affine A ⟶ incidenceTotal F incidence),
    incidence.points A z = F.universalCover.points A (z ≫ reuse.hom)
  action : ModObj G (incidenceTotal F incidence)
  parameter : action.smul ≫ incidenceProjection F incidence =
    (G ◁ incidenceProjection F incidence) ≫ (centralizerGroupAction F).smul
  coefficients : ∀ (A : CommAlgCat.{0} ℂ) (g : affine A ⟶ G)
      (z : affine A ⟶ incidenceTotal F incidence),
    (incidence.points A
      (CartesianMonoidalCategory.lift g z ≫ action.smul)).val.snd.plane.toSubmodule =
      (incidence.points A z).val.snd.plane.toSubmodule.map (F.adjoint.adjoint A g).toLinearMap
  weyl : ∀ w : F.Weyl,
    action.smul ≫ (CameralRamificationTensorModels.coverIso F incidence.cameral w).hom =
      (G ◁ (CameralRamificationTensorModels.coverIso F incidence.cameral w).hom) ≫ action.smul
  normalizer_weyl : ∀ (A : CommAlgCat.{0} ℂ) (g : affine A ⟶ G)
      (n : affine A ⟶ F.normalizer.scheme) (w : F.Weyl)
      (_hw : ∀ x : (affine A).left, F.weyl.points (affine A) (n ≫ F.normalizer.quotient) x = w)
      (z : affine A ⟶ incidenceTotal F incidence)
      (_hc : (incidence.points A z).val.fst.plane.toSubmodule =
        ((LinearMap.range F.source.cartan).baseChange A).map (F.adjoint.adjoint A g).toLinearMap)
      (_hb : (incidence.points A z).val.snd.plane.toSubmodule =
        (borelAt F.borel A).map (F.adjoint.adjoint A g).toLinearMap),
    (incidence.points A
      (z ≫ (coverIso F incidence.cameral w).hom)).val.snd.plane.toSubmodule =
      (borelAt F.borel A).map (F.adjoint.adjoint A
        (CartesianMonoidalCategory.lift g (n ≫ F.normalizer.inclusion ≫ ι[G]) ≫ μ[G])).toLinearMap

variable (I : IncidenceAction F) {X : Over (Spec (.of ℂ))} (P : Regularizer F X)

abbrev universalTotal := incidenceTotal F I.incidence
abbrev universalProjection := incidenceProjection F I.incidence

structure CoverDescent where
  cameral : Cover F X
  comparison : pullback (projection F cameral) P.torsor.projection ≅
    pullback (universalProjection F I) P.map
  over_torsor : comparison.hom ≫ pullback.snd (universalProjection F I) P.map =
    pullback.snd (projection F cameral) P.torsor.projection
  sourceAction : ModObj G (pullback (projection F cameral) P.torsor.projection)
  source_cover : sourceAction.smul ≫ pullback.fst (projection F cameral) P.torsor.projection =
    snd G (pullback (projection F cameral) P.torsor.projection) ≫
      pullback.fst (projection F cameral) P.torsor.projection
  source_torsor : sourceAction.smul ≫ pullback.snd (projection F cameral) P.torsor.projection =
    (G ◁ pullback.snd (projection F cameral) P.torsor.projection) ≫ P.torsor.action.smul
  targetAction : ModObj G (pullback (universalProjection F I) P.map)
  target_cover : targetAction.smul ≫ pullback.fst (universalProjection F I) P.map =
    (G ◁ pullback.fst (universalProjection F I) P.map) ≫ I.action.smul
  target_torsor : targetAction.smul ≫ pullback.snd (universalProjection F I) P.map =
    (G ◁ pullback.snd (universalProjection F I) P.map) ≫ P.torsor.action.smul
  equivariant : sourceAction.smul ≫ comparison.hom = (G ◁ comparison.hom) ≫ targetAction.smul
  sourceDeck : F.Weyl →* Aut (pullback (projection F cameral) P.torsor.projection)
  source_deck_cover : ∀ w : F.Weyl,
    (sourceDeck w).asIso.hom ≫ pullback.fst (projection F cameral) P.torsor.projection =
    pullback.fst (projection F cameral) P.torsor.projection ≫
      (CameralRamificationTensorModels.coverIso F cameral w).hom
  source_deck_torsor : ∀ w : F.Weyl,
    (sourceDeck w).asIso.hom ≫ pullback.snd (projection F cameral) P.torsor.projection =
      pullback.snd (projection F cameral) P.torsor.projection
  targetDeck : F.Weyl →* Aut (pullback (universalProjection F I) P.map)
  target_deck_cover : ∀ w : F.Weyl,
    (targetDeck w).asIso.hom ≫ pullback.fst (universalProjection F I) P.map =
    pullback.fst (universalProjection F I) P.map ≫
      (CameralRamificationTensorModels.coverIso F I.incidence.cameral w).hom
  target_deck_torsor : ∀ w : F.Weyl,
    (targetDeck w).asIso.hom ≫ pullback.snd (universalProjection F I) P.map =
      pullback.snd (universalProjection F I) P.map
  weyl : ∀ w : F.Weyl,
    (sourceDeck w).asIso.hom ≫ comparison.hom = comparison.hom ≫ (targetDeck w).asIso.hom

def incidenceMap (D : CoverDescent F I P) :
    pullback (projection F D.cameral) P.torsor.projection ⟶ universalTotal F I :=
  D.comparison.hom ≫ pullback.fst (universalProjection F I) P.map

def reindexedRegularizer {Y : Over (Spec (.of ℂ))} (f : Y ⟶ X)
    (r : GroupTorsorGeometry.Reindex G P.torsor f) : Regularizer F Y :=
  reindexObject G F.centralizers.scheme P f r

structure ReindexCover (D : CoverDescent F I P) {Y : Over (Spec (.of ℂ))} (f : Y ⟶ X)
    (r : GroupTorsorGeometry.Reindex G P.torsor f) where
  pulled : CoverDescent F I (reindexedRegularizer F P f r)
  arrow : CameralArrow F pulled.cameral D.cameral
  base : arrow.base = f
  equivariant : ∀ w : F.Weyl,
    (CameralRamificationTensorModels.coverIso F pulled.cameral w).hom ≫ arrow.total =
      arrow.total ≫ (CameralRamificationTensorModels.coverIso F D.cameral w).hom
  normalized : ∀ (V : Over (Spec (.of ℂ))) (c : V ⟶ total F pulled.cameral)
      (p : V ⟶ r.torsor.total) (h : c ≫ projection F pulled.cameral = p ≫ r.torsor.projection)
      (h' : (c ≫ arrow.total) ≫ projection F D.cameral =
        (p ≫ r.original G) ≫ P.torsor.projection),
    pullback.lift c p h ≫ incidenceMap F I (reindexedRegularizer F P f r) pulled =
      pullback.lift (c ≫ arrow.total) (p ≫ r.original G) h' ≫ incidenceMap F I P D

end MathlibExt.AlgebraicGeometry.CameralCoverDescentModels
