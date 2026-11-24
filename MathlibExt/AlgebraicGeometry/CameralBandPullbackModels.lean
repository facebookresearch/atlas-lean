/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralCentralizerBandModels
public import MathlibExt.AlgebraicGeometry.CameralMarkedRegularizers

/-!
# Native cameral band pullback and regularizer evaluation

The band is pulled to the actual G torsor. Its comparison is with the
actual sigma pullback of the universal pointwise centralizer group.
Evaluation is the literal map into G through that same scheme pullback.
The induced regularizer map is the original G action evaluated there.
All coefficient comparisons are imposed on actual marked incidence
points and Borel quotients, including nonreduced scheme tests.
Source: Donagi--Gaitsgory math/0005132v3, Sections11--12/14.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralBandPullbackModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRamificationReindexing CameralRegularizedHiggsModels
open CameralCoverDescentModels CameralBorelReductionModels CameralCentralizerBandModels
open CameralTorusBands GroupTorsorGeometry ExpansionParameterModels SchemeLieJetFamilies
open CameralIncidenceModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
  {X : Over (Spec (.of ℂ))} (C : Cover F X) (H : CameralMarkedRegularizers.Object F I C)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

abbrev band := F.band X C

/-- The same original total G torsor as a scheme over X. -/
def relativeTotal : Over X.left := Over.mk H.regularizer.torsor.projection.left

/-- Forgetting its relative view preserves the whole original total scheme. -/
def totalIso : (Over.map X.hom).obj (relativeTotal F I C H) ≅ H.regularizer.torsor.total :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 H.regularizer.torsor.total.left) ≫ H.regularizer.torsor.total.hom =
      H.regularizer.torsor.projection.left ≫ X.hom
    simpa only [Category.id_comp] using H.regularizer.torsor.projection.w.symm)

/-- The actual band and universal centralizer after the two prescribed pullbacks. -/
abbrev pulledBand := (Over.pullback H.regularizer.torsor.projection.left).obj (band F C).scheme
abbrev pulledCentralizer := (Over.pullback H.regularizer.map.left).obj J.scheme

/-- The original universal centralizer point after the sigma base change. -/
def centralizerOriginal : (Over.map H.regularizer.torsor.total.hom).obj
    (pulledCentralizer F I J C H) ⟶ (Over.map F.centralizers.scheme.hom).obj J.scheme :=
  Over.homMk (pullback.fst J.scheme.hom H.regularizer.map.left) (by
    change pullback.fst J.scheme.hom H.regularizer.map.left ≫
      (J.scheme.hom ≫ F.centralizers.scheme.hom) =
      pullback.snd J.scheme.hom H.regularizer.map.left ≫ H.regularizer.torsor.total.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, H.regularizer.map.w])

/-- The original total torsor map of the band pullback. -/
def bandPoint : (Over.map H.regularizer.torsor.total.hom).obj
    (pulledBand F I C H) ⟶ H.regularizer.torsor.total :=
  Over.homMk (pullback.snd (band F C).scheme.hom H.regularizer.torsor.projection.left) rfl

/-- Evaluation is the actual G element represented by the same centralizer pullback. -/
def bandElement (e : pulledBand F I C H ≅ pulledCentralizer F I J C H) :
    (Over.map H.regularizer.torsor.total.hom).obj (pulledBand F I C H) ⟶ G :=
  (Over.map H.regularizer.torsor.total.hom).map e.hom ≫
    centralizerOriginal F I J C H ≫ J.inclusion

/-- An actual band section and original torsor point form their literal pullback point. -/
def bandPairPoint (U : Over X.left) (s : U ⟶ (band F C).scheme)
    (p : (Over.map X.hom).obj U ⟶ H.regularizer.torsor.total)
    (hp : p ≫ H.regularizer.torsor.projection = Over.homMk U.hom rfl) :
    (Over.map X.hom).obj U ⟶
      (Over.map H.regularizer.torsor.total.hom).obj (pulledBand F I C H) :=
  Over.homMk (pullback.lift s.left p.left (by
    rw [s.w]
    exact (congrArg Over.Hom.left hp).symm)) (by
      change pullback.lift s.left p.left _ ≫
        (pullback.snd (band F C).scheme.hom H.regularizer.torsor.projection.left ≫
          H.regularizer.torsor.total.hom) = _
      rw [← Category.assoc, pullback.lift_snd]
      exact p.w)

/-- The actual point projection from the locally pulled cameral cover. -/
def localBase (U : Over X.left) : CameralTorusBands.pulled F.Weyl C.cover U ⟶
    (Over.map X.hom).obj U := Over.homMk (pullback.snd C.cover.scheme.hom U.hom) rfl

/-- The other projection retains the original cameral incidence point. -/
def localCover (U : Over X.left) : CameralTorusBands.pulled F.Weyl C.cover U ⟶ total F C :=
  Over.homMk (pullback.fst C.cover.scheme.hom U.hom) (by
    change pullback.fst C.cover.scheme.hom U.hom ≫ (C.cover.scheme.hom ≫ X.hom) = _
    rw [← Category.assoc, pullback.condition, Category.assoc]
    rfl)

theorem local_square (U : Over X.left) : localBase F C U ≫ Over.homMk U.hom rfl =
    localCover F C U ≫ projection F C := by
  apply Over.OverMorphism.ext
  exact (pullback.condition (f := C.cover.scheme.hom) (g := U.hom)).symm

/-- The comparison is fixed by every actual incidence/Borel coefficient map. -/
structure BandPullbackComparison where
  iso : pulledBand F I C H ≅ pulledCentralizer F I J C H
  coefficients : ∀ (U : Over X.left) (s : U ⟶ (band F C).scheme)
      (p : (Over.map X.hom).obj U ⟶ H.regularizer.torsor.total)
      (hp : p ≫ H.regularizer.torsor.projection = Over.homMk U.hom rfl)
      (A : CommAlgCat.{0} ℂ) (f : affine A ⟶ CameralTorusBands.pulled F.Weyl C.cover U)
      (a : affine A ⟶ G)
      (_hb : (I.incidence.points A
        (CameralMarkedRegularizers.incidencePoint F I C H (affine A)
          (f ≫ localCover F C U) (f ≫ localBase F C U ≫ p) (by
            rw [Category.assoc, Category.assoc, hp]
            simpa only [Category.assoc] using
              congrArg (fun q => f ≫ q) (local_square F C U)))).val.snd.plane.toSubmodule =
        (borelAt F.borel A).map (F.adjoint.adjoint A a).toLinearMap),
    ∃ b : affine A ⟶ B.scheme,
      b ≫ B.inclusion = SchemeLieJetFamilies.conjugate G (a ≫ ι[G])
        (f ≫ localBase F C U ≫ bandPairPoint F I C H U s p hp ≫
          bandElement F I J C H iso) ∧
      f ≫ ((band F C).points U s).val = b ≫ B.quotient

end MathlibExt.AlgebraicGeometry.CameralBandPullbackModels
