/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBorelReductionModels

/-!
# Actual universal centralizer groups and the cameral band

The group represents actual G elements fixing every coefficient of the
actual regular-centralizer plane. Its group law is the native G law.
The band comparison is fixed at every incidence point by conjugating
into the actual Borel subgroup and taking its actual B-to-T quotient.
This identifies the root-unit cameral band with the actual centralizer,
including its disconnected fibres, without an arbitrary group action.
Source: DG arXiv:math/0005132v3, Sections 11--12 and Theorem 4.4.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralCentralizerBandModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralIncidenceModels CameralTorusBands
open CameralCoverDescentModels CameralBorelReductionModels CameralRegularizedHiggsModels
open SchemeLieJetFamilies RegularCentralizerAffineModels ExpansionParameterModels
open TorusLineFrameModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

def FixesPlane (U : Over F.centralizers.scheme.left)
    (g : testScheme F.centralizers.scheme U ⟶ G) : Prop :=
  ∀ (A : CommAlgCat.{0} ℂ) (f : affine A ⟶ testScheme F.centralizers.scheme U)
    (v : LieAt F.lie.carrier A),
    v ∈ (F.centralizers.points A (f ≫ testMap F.centralizers.scheme U)).plane.toSubmodule →
      F.adjoint.adjoint A (f ≫ g) v = v

structure CentralizerGroup where
  scheme : Over F.centralizers.scheme.left
  [group : GrpObj scheme]
  [smooth : Smooth scheme.hom]
  commutative : μ[scheme] = (β_ scheme scheme).hom ≫ μ[scheme]
  points : ∀ U : Over F.centralizers.scheme.left, (U ⟶ scheme) ≃
    {g : testScheme F.centralizers.scheme U ⟶ G // FixesPlane F U g}
  inclusion : (Over.map F.centralizers.scheme.hom).obj scheme ⟶ G
  normalized : ∀ (U : Over F.centralizers.scheme.left) (g : U ⟶ scheme),
    (points U g).val = (Over.map F.centralizers.scheme.hom).map g ≫ inclusion
  identity : ∀ U : Over F.centralizers.scheme.left,
    (points U (toUnit U ≫ η[scheme])).val = toUnit (testScheme F.centralizers.scheme U) ≫ η[G]
  multiply : ∀ (U : Over F.centralizers.scheme.left) (g h : U ⟶ scheme),
    (points U (CartesianMonoidalCategory.lift g h ≫ μ[scheme])).val =
      SchemeLieJetFamilies.multiply G (points U g).val (points U h).val

variable (B : BorelGeometry F) (I : IncidenceAction F) (J : CentralizerGroup F)

@[instance_reducible] def centralizerGroup : GrpObj J.scheme := J.group
attribute [local instance] centralizerGroup

abbrev universalBand := F.band F.centralizers.scheme I.incidence.cameral

@[instance_reducible] def universalBandGroup : GrpObj (universalBand F I).scheme :=
  (universalBand F I).group
attribute [local instance] universalBandGroup

def coverBase (U : Over F.centralizers.scheme.left) :
    CameralTorusBands.pulled F.Weyl I.incidence.cameral.cover U ⟶
      testScheme F.centralizers.scheme U :=
  Over.homMk (pullback.snd I.incidence.cameral.cover.scheme.hom U.hom) rfl

def coverIncidence (U : Over F.centralizers.scheme.left) :
    CameralTorusBands.pulled F.Weyl I.incidence.cameral.cover U ⟶
      CameralRamificationReindexing.total F I.incidence.cameral := by
  refine Over.homMk (pullback.fst I.incidence.cameral.cover.scheme.hom U.hom) ?_
  change pullback.fst I.incidence.cameral.cover.scheme.hom U.hom ≫
      (I.incidence.cameral.cover.scheme.hom ≫ F.centralizers.scheme.hom) = _
  rw [← Category.assoc, pullback.condition, Category.assoc]
  rfl

structure UniversalBandComparison where
  iso : J.scheme ≅ (universalBand F I).scheme
  hom : IsMonHom iso.hom
  coefficients : ∀ (U : Over F.centralizers.scheme.left) (q : U ⟶ J.scheme)
      (A : CommAlgCat.{0} ℂ)
      (f : affine A ⟶ CameralTorusBands.pulled F.Weyl I.incidence.cameral.cover U)
      (a : affine A ⟶ G)
      (_hb : (I.incidence.points A (f ≫ coverIncidence F I U)).val.snd.plane.toSubmodule =
        (borelAt F.borel A).map (F.adjoint.adjoint A a).toLinearMap),
    ∃ b : affine A ⟶ B.scheme,
      b ≫ B.inclusion = SchemeLieJetFamilies.conjugate G (a ≫ ι[G])
        ((f ≫ coverBase F I U) ≫ (J.points U q).val) ∧
      f ≫ ((universalBand F I).points U (q ≫ iso.hom)).val = b ≫ B.quotient

end MathlibExt.AlgebraicGeometry.CameralCentralizerBandModels
