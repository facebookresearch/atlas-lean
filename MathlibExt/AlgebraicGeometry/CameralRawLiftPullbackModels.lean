/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralBorelLiftModels

/-!
# All-coefficient raw gamma and beta pullback diagrams

The torus comparison is normalized on the literal B-to-T quotient,
using the original G-torsor map and the original cameral projection.
Its parameter maps use the whole Cartesian base-change square.
Gamma uses the native Weyl and root-tensor comparisons; beta uses the
entire native character line and ramification symbol pullbacks.
Source: DG math/0005132v3, Sections7/15/16.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralRawLiftPullbackModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations
open CameralNormalizerShifts CameralLiftedNormalizerModels CameralLiftedRamificationData
open CameralCoverDescentModels CameralBorelReductionModels CameralBorelAbelianizationCore
open CameralRawAbelianizationData CameralBorelLiftModels
open ContractedTorsorModels NormalizedTorsorOperations ExpansionParameterModels
open CameralRegularizedHiggsModels FiniteCoverLocalComparison
open CameralSimpleRootTrivializations

variable {G : Over (Spec (.of ℂ))} [GrpObj G]
  {tori : ∀ n : ℕ, TorusTheory ℂ n} (F : Foundation G tori)
  [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  (I : IncidenceAction F) (BB : BorelGeometry F)

attribute [local instance] CameralRamificationTensorModels.torusGroup
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom

structure RegularizerAlong {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} (m : CameralArrow F C C')
    (H : Marked F I C) (H' : Marked F I C') where
  original : H.regularizer.torsor.total ⟶ H'.regularizer.torsor.total
  base : original ≫ H'.regularizer.torsor.projection =
    H.regularizer.torsor.projection ≫ m.base
  target : original ≫ H'.regularizer.map = H.regularizer.map
  group : H.regularizer.torsor.action.smul ≫ original =
    (G ◁ original) ≫ H'.regularizer.torsor.action.smul
  incidence : ∀ (U : Over (Spec (.of ℂ))) (c : U ⟶ total F C)
      (p : U ⟶ H.regularizer.torsor.total)
      (hp : p ≫ H.regularizer.torsor.projection = c ≫ projection F C)
      (hq : (p ≫ original) ≫ H'.regularizer.torsor.projection =
        (c ≫ m.total) ≫ projection F C'),
    CameralMarkedRegularizers.incidencePoint F I C H U c p hp =
      CameralMarkedRegularizers.incidencePoint F I C' H' U (c ≫ m.total)
        (p ≫ original) hq

structure BorelTorusPullback {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} (m : CameralArrow F C C')
    (H : Marked F I C) (H' : Marked F I C')
    (a : RegularizerAlong F I m H H')
    (N : ReductionFamily F BB I C) (N' : ReductionFamily F BB I C')
    (O : BorelTorusOperations F BB) where
  borelOriginal : (N.object H).torsor.total ⟶ (N'.object H').torsor.total
  cover : borelOriginal ≫ (N'.object H').torsor.projection =
    (N.object H).torsor.projection ≫ m.total
  torsor : borelOriginal ≫ (N'.object H').toTorsor = (N.object H).toTorsor ≫ a.original
  comparison : (D.torus.baseChange.change m.total).obj
    ((rawBorelFunctor F BB I C' N' O).obj H') ≅
      (rawBorelFunctor F BB I C N O).obj H
  quotient : tensorHom borelOriginal (𝟙 (Torus F)) ≫
      (O.pushout.diagram (total F C') (markedBundle F BB I C' (N'.object H'))).quotient =
    (O.pushout.diagram (total F C) (markedBundle F BB I C (N.object H))).quotient ≫
      comparison.inv.iso.hom ≫
      original (D.torus.baseChange.pullback m.total
        ((rawBorelFunctor F BB I C' N' O).obj H'))

structure ParameterAlong {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} (m : CameralArrow F C C')
    (B : ParameterCovers F C) (B' : ParameterCovers F C') where
  arrow : ∀ U : Over (Spec (.of ℂ)),
    CameralArrow F (B.pulled U).cover (B'.pulled U).cover
  base : ∀ U, (arrow U).base = tensorHom m.base (𝟙 U)
  original : ∀ U, (arrow U).total ≫ (B'.pulled U).arrow.total =
    (B.pulled U).arrow.total ≫ m.total
  weyl : ∀ U w, (coverIso F (B.pulled U).cover w).hom ≫ (arrow U).total =
    (arrow U).total ≫ (coverIso F (B'.pulled U).cover w).hom
  reflections : ∀ U i, ReflectionCompatible F (arrow U) i i
  naturality : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U),
    (B.arrow f).total ≫ (arrow U).total = (arrow V).total ≫ (B'.arrow f).total

def parameterComparison {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} {m : CameralArrow F C C'}
    {B : ParameterCovers F C} {B' : ParameterCovers F C'}
    (M : ParameterAlong F m B B')
    {P : Bundle (Torus F) (total F C)} {P' : Bundle (Torus F) (total F C')}
    (e : (D.torus.baseChange.change m.total).obj P' ≅ P)
    (U : Over (Spec (.of ℂ))) :
    (D.torus.baseChange.change (M.arrow U).total).obj
      (parameterBundle F K D B' P' U) ≅ parameterBundle F K D B P U :=
  (D.torus.baseChange.composition (B'.pulled U).arrow.total (M.arrow U).total).app P' ≪≫
    eqToIso (congrArg (fun f => (D.torus.baseChange.change f).obj P') (M.original U)) ≪≫
    (D.torus.baseChange.composition m.total (B.pulled U).arrow.total).symm.app P' ≪≫
    (D.torus.baseChange.change (B.pulled U).arrow.total).mapIso e

def shiftedPullback {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} (m : CameralArrow F C C')
    (hW : ∀ w, (coverIso F C w).hom ≫ m.total = m.total ≫ (coverIso F C' w).hom)
    (hR : ∀ i, ReflectionCompatible F m i i) (w : F.Weyl)
    (P : Bundle (Torus F) (total F C')) :
    (D.torus.baseChange.change m.total).obj (shifted F K D C' w P) ≅
      shifted F K D C w ((D.torus.baseChange.change m.total).obj P) :=
  D.torus.baseTensor m.total (combined F K D C' w P) (ramificationTorsor F K D C' w) ≪≫
    tensorIso (Torus F) D.torus.tensor (R.baseWeyl m hW w P).iso
      (ramificationPullbackIso F K D R.symbols R.torsors m hR w)

def characterPullback {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} (m : CameralArrow F C C')
    (i : Fin F.roots.count) (h : ReflectionCompatible F m i i)
    {P : Bundle (Torus F) (total F C)} {P' : Bundle (Torus F) (total F C')}
    (e : (D.torus.baseChange.change m.total).obj P' ≅ P) :
    (Scheme.Modules.pullback (fixedMap F m i h).left).obj
      (higgsLine F K D A C' i P') ≅ higgsLine F K D A C i P :=
  (Scheme.Modules.pullbackComp (fixedMap F m i h).left (fixedInclusion F C' i).left).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (fixedMap_inclusion F m i h))).app _ ≪≫
    (Scheme.Modules.pullbackComp (fixedInclusion F C i).left m.total.left).symm.app _ ≪≫
    (Scheme.Modules.pullback (fixedInclusion F C i).left).mapIso
      ((A.pullback m.total i).app P' ≪≫ (A.line (total F C) i).mapIso e)

def ramificationLinePullback {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} (m : CameralArrow F C C')
    (i : Fin F.roots.count) (h : ReflectionCompatible F m i i) :
    (Scheme.Modules.pullback (fixedMap F m i h).left).obj
      (ramifiedLine F C' i) ≅ ramifiedLine F C i :=
  (Scheme.Modules.pullbackComp (fixedMap F m i h).left (fixedInclusion F C' i).left).app _ ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg Over.Hom.left (fixedMap_inclusion F m i h))).app _ ≪≫
    (Scheme.Modules.pullbackComp (fixedInclusion F C i).left m.total.left).symm.app _ ≪≫
    (Scheme.Modules.pullback (fixedInclusion F C i).left).mapIso (R.symbols.map m i i h).line

structure RawDataPullback {X Y : Over (Spec (.of ℂ))}
    {C : Cover F X} {C' : Cover F Y} {m : CameralArrow F C C'}
    {B : ParameterCovers F C} {B' : ParameterCovers F C'}
    (M : ParameterAlong F m B B')
    {P : Bundle (Torus F) (total F C)} {P' : Bundle (Torus F) (total F C')}
    (e : (D.torus.baseChange.change m.total).obj P' ≅ P)
    (S : RawNormalizerShift F K D R B P) (S' : RawNormalizerShift F K D R B' P')
    (β : RawBetaMaps F K D R A B P) (β' : RawBetaMaps F K D R A B' P') : Prop where
  gamma : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (hn : Label F n w),
    (D.torus.baseChange.change (M.arrow U).total).map (S'.gamma U n w hn).hom ≫
      (parameterComparison F K D M e U).hom =
    (shiftedPullback F K D R (M.arrow U) (M.weyl U) (M.reflections U) w
      (parameterBundle F K D B' P' U)).hom ≫
      (shiftFunctor F K D (B.pulled U).cover w).map
        (parameterComparison F K D M e U).hom ≫ (S.gamma U n w hn).hom
  beta : ∀ (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count)
      (hi : SimpleRoot G tori F i) (c : U ⟶ torusScheme ℂ 1),
    (Scheme.Modules.pullback (fixedMap F (M.arrow U) i (M.reflections U i)).left).map
      (β'.beta U i hi c).hom ≫
      (ramificationLinePullback F K D R (M.arrow U) i (M.reflections U i)).hom =
    (characterPullback F K D A (M.arrow U) i (M.reflections U i)
      (parameterComparison F K D M e U)).hom ≫ (β.beta U i hi c).hom

end MathlibExt.AlgebraicGeometry.CameralRawLiftPullbackModels
