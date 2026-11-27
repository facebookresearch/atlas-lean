/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralCartanValueModels

/-!
# Actual Borel reductions and their torus abelianization

B is the scheme stabilizer of the actual Borel Lie subalgebra on every
coefficient scheme. Its T quotient is the group abelianization, fixed on
the Cartan subgroup and every native Borel Lie jet. The flag torsor uses
the native left B action and inversion to identify B backslash G with
G slash B. A regularizer's B reduction is the actual standard-Borel fibre
of its pulled incidence flag. Its torus bundle is the literal contracted
pushout along B to T, whose target is commutative.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 7.2 and 16.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralBorelReductionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralIncidenceModels CameralRamificationReindexing
open CameralRamificationTensorModels CameralRegularizedHiggsModels CameralCoverDescentModels
open CameralCartanValueModels GroupTorsorGeometry SchemeLieJetFamilies
open ContractedTorsorModels NormalizedTorsorOperations ExpansionParameterModels
open TorusInfinitesimalPoints

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralRamificationTensorModels.torusGroup

def StabilizesBorel {U : Over (Spec (.of ℂ))} (g : U ⟶ G) : Prop :=
  ∀ (A : CommAlgCat.{0} ℂ) (f : affine A ⟶ U),
    (borelAt F.borel A).map (F.adjoint.adjoint A (f ≫ g)).toLinearMap = borelAt F.borel A

structure BorelGeometry where
  scheme : Over (Spec (.of ℂ))
  [group : GrpObj scheme]
  [affine_scheme : IsAffine scheme.left]
  [smooth : Smooth scheme.hom]
  [finiteType : LocallyOfFiniteType scheme.hom]
  [connected : ConnectedSpace scheme.left]
  inclusion : scheme ⟶ G
  [mono : Mono inclusion]
  [inclusionHom : IsMonHom inclusion]
  points : ∀ U : Over (Spec (.of ℂ)), (U ⟶ scheme) ≃ {g : U ⟶ G // StabilizesBorel F g}
  points_normalized : ∀ (U : Over (Spec (.of ℂ))) (b : U ⟶ scheme), (points U b).val = b ≫ inclusion
  torus : Torus F ⟶ scheme
  [torusHom : IsMonHom torus]
  torus_normalized : torus ≫ inclusion = F.source.torus
  quotient : scheme ⟶ Torus F
  [quotientHom : IsMonHom quotient]
  [quotientFlat : Flat quotient.left]
  [quotientPresentation : LocallyOfFinitePresentation quotient.left]
  [quotientSurjective : Surjective quotient.left]
  quotient_torus : torus ≫ quotient = 𝟙 (Torus F)
  abelianization : ∀ (H : Over (Spec (.of ℂ))) [GrpObj H],
    μ[H] = (β_ H H).hom ≫ μ[H] → ∀ f : scheme ⟶ H, IsMonHom f →
      ∃! q : Torus F ⟶ H, IsMonHom q ∧ quotient ≫ q = f
  jet : ∀ (A : CommAlgCat.{0} ℂ) (_b : borelAt F.borel A),
    doubled A ⟶ scheme
  jet_inclusion : ∀ (A : CommAlgCat.{0} ℂ) (b : borelAt F.borel A),
    jet A b ≫ inclusion = jetPoint G F.lie.carrier F.lie.model F.jets A b.val
  jet_quotient : ∀ (A : CommAlgCat.{0} ℂ) (b : borelAt F.borel A),
    jet A b ≫ quotient = CameralChevalleyModels.firstOrderPoint (tori F.rank) A
      (F.value.standardQuotient A b)
  standardFlag : 𝟙_ (Over (Spec (.of ℂ))) ⟶ F.flag.scheme
  standard_borel : ∀ A : CommAlgCat.{0} ℂ,
    (F.flag.points A (toUnit (affine A) ≫ standardFlag)).plane.toSubmodule = borelAt F.borel A
  flagProjection : G ⟶ F.flag.scheme
  flag_points : ∀ (A : CommAlgCat.{0} ℂ) (g : affine A ⟶ G),
    (F.flag.points A (g ≫ flagProjection)).plane.toSubmodule =
      (borelAt F.borel A).map (F.adjoint.adjoint A (g ≫ ι[G])).toLinearMap
  flagTorsor : GroupTorsorGeometry.Torsor scheme F.flag.scheme
  flagTotal : flagTorsor.total ≅ G
  flag_projection : flagTotal.hom ≫ flagProjection = flagTorsor.projection
  flag_action : flagTorsor.action.smul ≫ flagTotal.hom = tensorHom inclusion flagTotal.hom ≫ μ[G]

variable (B : BorelGeometry F)

@[instance_reducible] def borelGroup : GrpObj B.scheme := B.group
attribute [local instance] borelGroup

theorem quotientHom : IsMonHom B.quotient := B.quotientHom
attribute [local instance] quotientHom

variable (I : IncidenceAction F) {X : Over (Spec (.of ℂ))} (P : Regularizer F X)
  (D : CoverDescent F I P)

def incidenceFlag : pullback (projection F D.cameral) P.torsor.projection ⟶ F.flag.scheme :=
  incidenceMap F I P D ≫ I.incidence.flag

structure BorelReduction where
  torsor : GroupTorsorGeometry.Torsor B.scheme (total F D.cameral)
  fibre : torsor.total ≅ pullback (incidenceFlag F I P D) B.standardFlag
  projection_normalized : fibre.hom ≫ pullback.fst (incidenceFlag F I P D) B.standardFlag ≫
      pullback.fst (projection F D.cameral) P.torsor.projection = torsor.projection
  toTorsor : torsor.total ⟶ P.torsor.total
  toTorsor_normalized : toTorsor = fibre.hom ≫
    pullback.fst (incidenceFlag F I P D) B.standardFlag ≫
      pullback.snd (projection F D.cameral) P.torsor.projection
  equivariant : torsor.action.smul ≫ toTorsor =
    tensorHom B.inclusion toTorsor ≫ P.torsor.action.smul

def reductionBundle (R : BorelReduction F B I P D) : Bundle B.scheme (total F D.cameral) where
  torsor := R.torsor
  map := toUnit R.torsor.total
  equivariant := Subsingleton.elim _ _

structure BorelTorusOperations where
  pushout : PushoutFunctor B.scheme (Torus F) B.quotient

variable (O : BorelTorusOperations F B) (R : BorelReduction F B I P D)

def abelianizationBundle : Bundle (Torus F) (total F D.cameral) :=
  (O.pushout.map (total F D.cameral)).obj (reductionBundle F B I P D R)

def abelianizationDiagram : Pushout (Torus F) B.quotient (reductionBundle F B I P D R)
    (abelianizationBundle F B I P D O R) :=
  O.pushout.diagram (total F D.cameral) (reductionBundle F B I P D R)

end MathlibExt.AlgebraicGeometry.CameralBorelReductionModels
