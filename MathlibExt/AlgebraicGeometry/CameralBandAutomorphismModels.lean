/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBandPullbackModels

/-!
# The native centralizer action of a cameral band section

A band section is paired with the original torsor point by the actual
scheme pullback. Its G element is evaluated through the normalized
universal-centralizer comparison. The resulting torsor map is the
original G action. The actual marked-regularizer automorphism and its
composition laws are fixed to these same maps.
Source: DG math/0005132v3, Theorem4.4/Corollary4.6/Section14.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralBandAutomorphismModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRamificationReindexing CameralRegularizedHiggsModels
open CameralCoverDescentModels CameralBorelReductionModels CameralCentralizerBandModels
open CameralBandPullbackModels CameralTorusBands GroupTorsorGeometry ExpansionParameterModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
  {X : Over (Spec (.of ℂ))} (C : Cover F X) (H : CameralMarkedRegularizers.Object F I C)
  (V : BandPullbackComparison F I B J C H)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

/-- The actual global base test for band sections. -/
abbrev baseTest : Over X.left := Over.mk (𝟙 X.left)

/-- Actual global sections of the prescribed cameral band. -/
abbrev BandSections := baseTest (X := X) ⟶ (band F C).scheme

/-- Every original torsor point is paired with the pullback of that same band section. -/
def sectionPair (s : BandSections F C) : H.regularizer.torsor.total ⟶
    (Over.map H.regularizer.torsor.total.hom).obj (pulledBand F I C H) :=
  Over.homMk
    (pullback.lift (H.regularizer.torsor.projection.left ≫ s.left) (𝟙 _) (by
      rw [Category.assoc, s.w]
      simp only [baseTest, Over.mk_hom, Category.comp_id, Category.id_comp]))
    (by
      change pullback.lift _ _ _ ≫
        (pullback.snd (band F C).scheme.hom H.regularizer.torsor.projection.left ≫
          H.regularizer.torsor.total.hom) = _
      rw [← Category.assoc, pullback.lift_snd, Category.id_comp])

/-- Its actual G element depends on the original torsor point through the fixed comparison. -/
def sectionElement (s : BandSections F C) : H.regularizer.torsor.total ⟶ G :=
  sectionPair F I C H s ≫ bandElement F I J C H V.iso

/-- The torsor map is the literal native G action by that element. -/
def sectionAction (s : BandSections F C) :
    H.regularizer.torsor.total ⟶ H.regularizer.torsor.total :=
  CartesianMonoidalCategory.lift (sectionElement F I B J C H V s) (𝟙 _) ≫
    H.regularizer.torsor.action.smul

/-- The original marked-regularizer arrow is exactly this actual centralizer evaluation. -/
structure AutomorphismSource where
  arrow : ∀ s : BandSections F C, H ⟶ H
  normalized : ∀ s : BandSections F C,
    (arrow s).map.iso.hom = sectionAction F I B J C H V s

/-- The band operation remains the native group law on the original represented scheme. -/
def multiplySections (s t : BandSections F C) : BandSections F C := by
  letI := (band F C).group
  exact CartesianMonoidalCategory.lift s t ≫ μ[(band F C).scheme]

/-- Its identity is the original group-scheme identity at the actual base test. -/
def identitySection : BandSections F C := by
  letI := (band F C).group
  exact toUnit (baseTest (X := X)) ≫ η[(band F C).scheme]

/-- The group-action laws concern only the fixed native section and torsor maps. -/
structure AutomorphismLaws (A : AutomorphismSource F I B J C H V) : Prop where
  identity : A.arrow (identitySection F C) = 𝟙 H
  multiply : ∀ s t : BandSections F C,
    A.arrow (multiplySections F C s t) = A.arrow t ≫ A.arrow s

end MathlibExt.AlgebraicGeometry.CameralBandAutomorphismModels
