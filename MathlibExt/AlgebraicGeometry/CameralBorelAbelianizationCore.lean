/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBorelReductionModels
public import MathlibExt.AlgebraicGeometry.CameralMarkedRegularizers

/-!
# The actual raw Borel fibre functor

The marked cover pulls the actual incidence flag to C times_X P. The B
torsor is its literal standard-Borel fibre. Its arrows are actual B
torsor arrows fixed by the original G torsor map. The functor below is
the native B-to-T contracted pushout on those objects and arrows.
Normalizer/beta convention adaptation is a separate normalized map on
this concrete bundle; its underlying fibre functor is already fixed.
Source: DG arXiv:math/0005132v3, Sections 7.2 and 16.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralBorelAbelianizationCore

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRamificationReindexing CameralRegularizedHiggsModels
open CameralCoverDescentModels CameralBorelReductionModels GroupTorsorGeometry
open ContractedTorsorModels ExpansionParameterModels

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) (B : BorelGeometry F) (I : IncidenceAction F)
  {X : Over (Spec (.of ℂ))} (C : Cover F X)

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom
attribute [local instance] CameralRamificationTensorModels.torusGroup

abbrev Marked := CameralMarkedRegularizers.Object F I C

def markedIncidence (H : Marked F I C) :
    pullback (projection F C) H.regularizer.torsor.projection ⟶ universalTotal F I :=
  pullback.lift
    (pullback.fst (projection F C) H.regularizer.torsor.projection ≫
      (CameralMarkedRegularizers.markingTotal F I C H).hom)
    (pullback.snd (projection F C) H.regularizer.torsor.projection) (by
      rw [Category.assoc, CameralMarkedRegularizers.markingProjection]
      exact pullback.condition) ≫ incidenceMap F I H.regularizer H.descent

def markedFlag (H : Marked F I C) :
    pullback (projection F C) H.regularizer.torsor.projection ⟶ F.flag.scheme :=
  markedIncidence F I C H ≫ I.incidence.flag

structure MarkedReduction (H : Marked F I C) where
  torsor : GroupTorsorGeometry.Torsor B.scheme (total F C)
  fibre : torsor.total ≅ pullback (markedFlag F I C H) B.standardFlag
  projection_normalized : fibre.hom ≫ pullback.fst (markedFlag F I C H) B.standardFlag ≫
      pullback.fst (projection F C) H.regularizer.torsor.projection = torsor.projection
  toTorsor : torsor.total ⟶ H.regularizer.torsor.total
  toTorsor_normalized : toTorsor = fibre.hom ≫
    pullback.fst (markedFlag F I C H) B.standardFlag ≫
      pullback.snd (projection F C) H.regularizer.torsor.projection
  equivariant : torsor.action.smul ≫ toTorsor =
    tensorHom B.inclusion toTorsor ≫ H.regularizer.torsor.action.smul

def markedBundle {H : Marked F I C} (R : MarkedReduction F B I C H) :
    Bundle B.scheme (total F C) where
  torsor := R.torsor
  map := toUnit R.torsor.total
  equivariant := Subsingleton.elim _ _

structure ReductionArrow {H H' : Marked F I C} (R : MarkedReduction F B I C H)
    (R' : MarkedReduction F B I C H') (f : H ⟶ H') where
  bundle : markedBundle F B I C R ⟶ markedBundle F B I C R'
  toTorsor : bundle.iso.hom ≫ R'.toTorsor = R.toTorsor ≫ f.map.iso.hom

structure ReductionFamily where
  object : ∀ H : Marked F I C, MarkedReduction F B I C H
  arrow : ∀ {H H' : Marked F I C} (f : H ⟶ H'), ReductionArrow F B I C (object H) (object H') f
  unit : ∀ H : Marked F I C, (arrow (𝟙 H)).bundle = 𝟙 (markedBundle F B I C (object H))
  composition : ∀ {H H' H'' : Marked F I C} (f : H ⟶ H') (g : H' ⟶ H''),
    (arrow (f ≫ g)).bundle = (arrow f).bundle ≫ (arrow g).bundle

def rawBorelFunctor (R : ReductionFamily F B I C) (O : BorelTorusOperations F B) :
    Marked F I C ⥤ Bundle (CameralRamificationTensorModels.Torus F) (total F C) where
  obj H := (O.pushout.map (total F C)).obj (markedBundle F B I C (R.object H))
  map f := (O.pushout.map (total F C)).map (R.arrow f).bundle
  map_id H := by
    rw [R.unit]
    exact (O.pushout.map (total F C)).map_id _
  map_comp f g := by
    rw [R.composition]
    exact (O.pushout.map (total F C)).map_comp _ _

end MathlibExt.AlgebraicGeometry.CameralBorelAbelianizationCore
