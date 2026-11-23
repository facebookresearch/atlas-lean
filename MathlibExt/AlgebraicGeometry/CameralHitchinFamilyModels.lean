/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralHitchinFunctorModels
public import MathlibExt.AlgebraicGeometry.StackCycleGeometry

/-!
# Coefficient families of the actual regularized Hitchin map

The parameter scheme is X times U and K is the literal pulled module.
All source/adjoint/centralizer/section and incidence maps are retained
under every coefficient arrow. The Cartan total-space map is fixed by
its whole pulled tautological section. Native stack unit/composition
cells use these same original maps. Properness of X is part of the
algebraic Hitchin-base output of Section17.7.
Source: DG math/0005132v3, Sections17.1--17.8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralHitchinFamilyModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRegularizedHiggsModels CameralCoverDescentModels
open CameralRamificationReindexing CameralHiggsCategoryModels CameralCartanValueModels
open CameralHitchinFunctorModels GroupTorsorGeometry ExpansionParameterModels
open LineBundleTaskContracts AlgebraicLineBundleFamilies RelativeLambdaReindexing
open CoherentCurveLinearSeries
open StackCycleGeometry

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  (I : IncidenceAction F) {X : Over (Spec (.of ℂ))} (K : TwistLine X)

attribute [local instance] centralizerGroupAction

structure Parameters where
  line : ∀ U : Over (Spec (.of ℂ)),
    IsLineBundle ((Scheme.Modules.pullback (fst X U).left).obj K.module)
  tensor : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U),
    TensorPullbackComparison (tensorHom (𝟙 X) f).left
  coherence : ∀ U : Over (Spec (.of ℂ)),
    CategoryCoherence F (X := X ⊗ U) (K := pulledTwist (fst X U) (line U))
  space : ∀ U : Over (Spec (.of ℂ)), SectionSpace (X ⊗ U)
    (cartanKModule F (X ⊗ U) (pulledTwist (fst X U) (line U)))
  weyl : ∀ U : Over (Spec (.of ℂ)),
    CartanWeylAction F (X ⊗ U) (pulledTwist (fst X U) (line U)) (space U)

variable (P : Parameters F K)

abbrev twist (U : Over (Spec (.of ℂ))) := pulledTwist (fst X U) (P.line U)
abbrev HiggsFamily (U : Over (Spec (.of ℂ))) :=
  HiggsObject F I (twist F K P U) (P.space U) (P.weyl U)
abbrev ValueFamily (U : Over (Spec (.of ℂ))) :=
  ValueObject F (twist F K P U) (P.space U) (P.weyl U)

@[instance_reducible] def familyCategory (U : Over (Spec (.of ℂ))) :
    Category (HiggsFamily F I K P U) :=
  higgsCategory F I (twist F K P U) (P.space U) (P.weyl U) (P.coherence U)

attribute [local instance] familyCategory

def lineComparison {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) :
    (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj (twist F K P U).module ≅
      (twist F K P V).module :=
  (Scheme.Modules.pullbackComp (tensorHom (𝟙 X) f).left (fst X U).left).app K.module ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left
      (by simp : tensorHom (𝟙 X) f ≫ fst X U = fst X V))).app K.module

def cartanComparison {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) :
    (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj
      (cartanKModule F (X ⊗ U) (twist F K P U)) ≅
    cartanKModule F (X ⊗ V) (twist F K P V) :=
  (P.tensor f).iso (cartanModule F (X ⊗ U)) (twist F K P U).module ≪≫
    { hom := tensorMap (scalarPullback (tensorHom (𝟙 X) f) (.of ℂ (Fin F.rank → ℂ))).hom
        (lineComparison F K P f).hom
      inv := tensorMap (scalarPullback (tensorHom (𝟙 X) f) (.of ℂ (Fin F.rank → ℂ))).inv
        (lineComparison F K P f).inv
      hom_inv_id := by rw [← tensorMap_comp, Iso.hom_inv_id, Iso.hom_inv_id, tensorMap_id]
      inv_hom_id := by rw [← tensorMap_comp, Iso.inv_hom_id, Iso.inv_hom_id, tensorMap_id] }

structure ValueSpaceChange {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) where
  original : sectionTotal (P.space V) ⟶ sectionTotal (P.space U)
  over : original ≫ sectionProjection (P.space U) =
    sectionProjection (P.space V) ≫ tensorHom (𝟙 X) f
  cartesian : IsPullback original (sectionProjection (P.space V))
    (sectionProjection (P.space U)) (tensorHom (𝟙 X) f)
  tautological : pullbackSection original.left (tautological (P.space U)) ≫
      (Scheme.Modules.pullbackComp original.left (P.space U).total.hom).hom.app _ ≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left over)).hom.app _ ≫
      (Scheme.Modules.pullbackComp (P.space V).total.hom (tensorHom (𝟙 X) f).left).inv.app _ ≫
      (Scheme.Modules.pullback (P.space V).total.hom).map (cartanComparison F K P f).hom =
    tautological (P.space V)

def torsorModuleComparison {U V : Over (Spec (.of ℂ))} (f : V ⟶ U)
    (H : HiggsFamily F I K P V) (H' : HiggsFamily F I K P U)
    (p : H.bundle.regularizer.torsor.total ⟶ H'.bundle.regularizer.torsor.total)
    (hp : p ≫ H'.bundle.regularizer.torsor.projection =
      H.bundle.regularizer.torsor.projection ≫ tensorHom (𝟙 X) f)
    (M : (X ⊗ U).left.Modules) :
    (Scheme.Modules.pullback H.bundle.regularizer.torsor.projection.left).obj
      ((Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj M) ≅
    (Scheme.Modules.pullback p.left).obj
      ((Scheme.Modules.pullback H'.bundle.regularizer.torsor.projection.left).obj M) :=
  (Scheme.Modules.pullbackComp H.bundle.regularizer.torsor.projection.left
    (tensorHom (𝟙 X) f).left).app M ≪≫
    (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hp.symm)).app M ≪≫
    (Scheme.Modules.pullbackComp p.left H'.bundle.regularizer.torsor.projection.left).symm.app M

/-- The centralizer isomorphism carries the section to the pulled-back section. -/
def IsSectionCompatible {U V : Over (Spec (.of ℂ))} (f : V ⟶ U)
    (H : HiggsFamily F I K P V) (H' : HiggsFamily F I K P U)
    (centralizer : H.bundle.centralizer.module ≅
      (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj H'.bundle.centralizer.module) :
    Prop :=
  H.bundle.sectionMap ≫ tensorMap centralizer.hom (lineComparison F K P f).inv =
    pullbackSection (tensorHom (𝟙 X) f).left H'.bundle.sectionMap ≫
      ((P.tensor f).iso H'.bundle.centralizer.module (twist F K P U).module).hom

/-- The adjoint isomorphism is compatible with the torsor trivializations of both families. -/
def IsAdjointTrivializationCompatible {U V : Over (Spec (.of ℂ))} (f : V ⟶ U)
    (H : HiggsFamily F I K P V) (H' : HiggsFamily F I K P U)
    (original : H.bundle.regularizer.torsor.total ⟶ H'.bundle.regularizer.torsor.total)
    (over : original ≫ H'.bundle.regularizer.torsor.projection =
      H.bundle.regularizer.torsor.projection ≫ tensorHom (𝟙 X) f)
    (sigma : original ≫ H'.bundle.regularizer.map = H.bundle.regularizer.map)
    (adjoint : H.bundle.adjoint.module ≅
      (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj H'.bundle.adjoint.module) :
    Prop :=
  (Scheme.Modules.pullback H.bundle.regularizer.torsor.projection.left).map adjoint.hom ≫
      (torsorModuleComparison F I K P f H H' original over H'.bundle.adjoint.module).hom ≫
      (Scheme.Modules.pullback original.left).map H'.bundle.adjoint.trivialization.hom =
    H.bundle.adjoint.trivialization.hom ≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left sigma.symm)).hom.app _ ≫
      (Scheme.Modules.pullbackComp original.left H'.bundle.regularizer.map.left).inv.app _

/-- The centralizer isomorphism is compatible with the torsor trivializations of both
families. -/
def IsCentralizerTrivializationCompatible {U V : Over (Spec (.of ℂ))} (f : V ⟶ U)
    (H : HiggsFamily F I K P V) (H' : HiggsFamily F I K P U)
    (original : H.bundle.regularizer.torsor.total ⟶ H'.bundle.regularizer.torsor.total)
    (over : original ≫ H'.bundle.regularizer.torsor.projection =
      H.bundle.regularizer.torsor.projection ≫ tensorHom (𝟙 X) f)
    (sigma : original ≫ H'.bundle.regularizer.map = H.bundle.regularizer.map)
    (centralizer : H.bundle.centralizer.module ≅
      (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj H'.bundle.centralizer.module) :
    Prop :=
  (Scheme.Modules.pullback H.bundle.regularizer.torsor.projection.left).map centralizer.hom ≫
      (torsorModuleComparison F I K P f H H' original over H'.bundle.centralizer.module).hom ≫
      (Scheme.Modules.pullback original.left).map H'.bundle.centralizer.trivialization.hom =
    H.bundle.centralizer.trivialization.hom ≫
      (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left sigma.symm)).hom.app _ ≫
      (Scheme.Modules.pullbackComp original.left H'.bundle.regularizer.map.left).inv.app _

/-- The cameral cover arrow and the torsor map send incidence points to incidence points. -/
def IsIncidenceCompatible {U V : Over (Spec (.of ℂ))}
    (H : HiggsFamily F I K P V) (H' : HiggsFamily F I K P U)
    (original : H.bundle.regularizer.torsor.total ⟶ H'.bundle.regularizer.torsor.total)
    (cover : CameralArrow F H.descent.cameral H'.descent.cameral) : Prop :=
  ∀ (Z : Over (Spec (.of ℂ))) (c : Z ⟶ total F H.descent.cameral)
      (p : Z ⟶ H.bundle.regularizer.torsor.total)
      (hp : c ≫ projection F H.descent.cameral = p ≫ H.bundle.regularizer.torsor.projection)
      (hq : (c ≫ cover.total) ≫ projection F H'.descent.cameral =
        (p ≫ original) ≫ H'.bundle.regularizer.torsor.projection),
    CameralHitchinFunctorModels.incidencePoint F I (twist F K P V) (P.space V) (P.weyl V)
        H Z c p hp =
      CameralHitchinFunctorModels.incidencePoint F I (twist F K P U) (P.space U) (P.weyl U)
        H' Z (c ≫ cover.total) (p ≫ original) hq

/-- The value maps of both families commute with the value-space change and the cover arrow. -/
def IsValueCompatible {U V : Over (Spec (.of ℂ))} {f : V ⟶ U}
    (H : HiggsFamily F I K P V) (H' : HiggsFamily F I K P U)
    (S : ValueSpaceChange F K P f)
    (cover : CameralArrow F H.descent.cameral H'.descent.cameral) : Prop :=
  valueMap F I H.bundle H.descent H.quotient H.tensor (P.space V) ≫ S.original =
    cover.total ≫ valueMap F I H'.bundle H'.descent H'.quotient H'.tensor (P.space U)

structure FamilyBaseChange {U V : Over (Spec (.of ℂ))} (f : V ⟶ U)
    (H : HiggsFamily F I K P V) (H' : HiggsFamily F I K P U)
    (S : ValueSpaceChange F K P f) where
  original : H.bundle.regularizer.torsor.total ⟶ H'.bundle.regularizer.torsor.total
  over : original ≫ H'.bundle.regularizer.torsor.projection =
    H.bundle.regularizer.torsor.projection ≫ tensorHom (𝟙 X) f
  cartesian : IsPullback original H.bundle.regularizer.torsor.projection
    H'.bundle.regularizer.torsor.projection (tensorHom (𝟙 X) f)
  group : H.bundle.regularizer.torsor.action.smul ≫ original =
    (G ◁ original) ≫ H'.bundle.regularizer.torsor.action.smul
  sigma : original ≫ H'.bundle.regularizer.map = H.bundle.regularizer.map
  adjoint : H.bundle.adjoint.module ≅
    (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj H'.bundle.adjoint.module
  centralizer : H.bundle.centralizer.module ≅
    (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).obj H'.bundle.centralizer.module
  inclusion : H.bundle.centralizer.inclusion ≫ adjoint.hom =
    centralizer.hom ≫ (Scheme.Modules.pullback (tensorHom (𝟙 X) f).left).map
      H'.bundle.centralizer.inclusion
  sectionMap : IsSectionCompatible F I K P f H H' centralizer
  adjoint_trivialization :
    IsAdjointTrivializationCompatible F I K P f H H' original over sigma adjoint
  centralizer_trivialization :
    IsCentralizerTrivializationCompatible F I K P f H H' original over sigma centralizer
  cover : CameralArrow F H.descent.cameral H'.descent.cameral
  base : cover.base = tensorHom (𝟙 X) f
  incidence : IsIncidenceCompatible F I K P H H' original cover
  value : IsValueCompatible F I K P H H' S cover

/-- Both actual stack family presentations use the computed Hitchin functor. -/
structure HitchinStacks where
  proper : IsProper X.hom
  higgs : Stack (Spec (.of ℂ))
  base : Stack (Spec (.of ℂ))
  higgs_artin : higgs.IsArtinStack
  base_artin : base.IsArtinStack
  higgsFamily : ∀ U : Over (Spec (.of ℂ)),
    letI := higgsCategory F I (twist F K P U) (P.space U) (P.weyl U) (P.coherence U)
    higgs.Fibre U ⥤ HiggsFamily F I K P U
  baseFamily : ∀ U : Over (Spec (.of ℂ)), base.Fibre U ⥤ ValueFamily F K P U
  higgs_equivalence : ∀ U : Over (Spec (.of ℂ)), (higgsFamily U).IsEquivalence
  base_equivalence : ∀ U : Over (Spec (.of ℂ)), (baseFamily U).IsEquivalence
  hitchin : StackHom higgs base
  normalized : ∀ U : Over (Spec (.of ℂ)),
    component hitchin U ⋙ baseFamily U = higgsFamily U ⋙
      hitchinFunctor F I (twist F K P U) (P.space U) (P.weyl U) (P.coherence U)
  space : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U), ValueSpaceChange F K P f
  reindex : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (x : higgs.Fibre U),
    FamilyBaseChange F I K P f ((higgsFamily V).obj ((pull higgs f).obj x))
      ((higgsFamily U).obj x) (space f)
  arrows : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) {x y : higgs.Fibre U} (a : x ⟶ y),
    (((higgsFamily V).map ((pull higgs f).map a)).map.regularizer).iso.hom ≫
        (reindex f y).original =
      (reindex f x).original ≫ (((higgsFamily U).map a).map.regularizer).iso.hom
  unit : ∀ (U : Over (Spec (.of ℂ))) (x : higgs.Fibre U),
    (((higgsFamily U).map
      ((higgs.toPseudofunctor.mapId (.mk (op U))).hom.toNatTrans.app x)).map.regularizer).iso.hom =
        (reindex (𝟙 U) x).original
  composition : ∀ {U V Z : Over (Spec (.of ℂ))} (f : V ⟶ U) (g : Z ⟶ V)
      (x : higgs.Fibre U),
    (((higgsFamily Z).map
      ((higgs.toPseudofunctor.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app
        x)).map.regularizer).iso.hom ≫ (reindex (g ≫ f) x).original =
    (reindex g ((pull higgs f).obj x)).original ≫ (reindex f x).original

end MathlibExt.AlgebraicGeometry.CameralHitchinFamilyModels
