/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StackBundleCones

/-!
# Relative rational virtual pullbacks on actual test families

Specialization is normalized on every projective/vector-bundle cycle
representative of the integral Kresch carrier, not merely on the image of
the naive cycle group. Each such representative uses its actual relative
intrinsic cone, the closed map into the pulled-back bundle stage, and its
atlas-normalized fundamental cycle. The map on rational Chow is then the
literal specialization, closed cone push, and inverse of the fixed bundle
projection pullback. Its bivariant laws are outputs.

All test families retain an actual 2-Cartesian square and the source
quotient stratification required by the construction. Finite-type scheme
tests are included: the DM-type pullback is DM and has the sourced quotient
stratification. Arbitrary Artin test sources are admitted only with that
explicit stratification. Cones use global normalized descent; embeddings
preserve the actual conical zero/scaling structure.

Sources: Manolache arXiv:0805.2065v2, Condition 3.3 p18,
Construction 3.6 p19, Theorems 4.1 and 4.4 pp23--28;
Kresch arXiv:math/9810166v1, Definition 2.1.11 and Section 5.
-/

@[expose] public noncomputable section
namespace AlgebraicGeometry.StackVirtualPullbacks

open CategoryTheory CategoryTheory.Limits Opposite
open GeneralStackGeometry StackCycleGeometry StackFibreModels StackAffineModules
open StackVectorBundles StackProjectiveModels StackCycleRelations StackChowGroups StackBundleCones
open scoped TensorProduct

variable {S : Scheme.{0}} {scope : Stack S → Prop}

def representative (D : CycleConstructionData S scope) (K : KreschPresentation D)
    (Y : Stack S) (hY : scope Y) (d : ℤ) (A : ProjectiveStage (scope := scope) Y)
    (E : BundleStage (scope := scope) A.source) :
    CycleGroup E.bundle.total (d + E.bundle.rank) →+ ChowGroup D K Y hY d :=
  (projectiveClass D K Y hY d A).comp
    ((bundleClass D K.bundle A.source A.inScope d E).comp
      (naiveCycleClass D E.bundle.total E.inScope (d + E.bundle.rank)))

/-- The literal geometric specialization of one Kresch cycle representative. -/
structure SpecializationRepresentativeData (D : CycleConstructionData S scope)
    (K : KreschPresentation D) {F G : Stack S} (f : StackHom F G)
    (C : IntrinsicConeModel f) (hC : scope C.total) (d : ℤ)
    (A : ProjectiveStage (scope := scope) G) (E : BundleStage (scope := scope) A.source)
    (Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank)) where
  coneStage : TwoCartesianSquare A.map (Pseudofunctor.StrongTrans.vcomp C.projection f)
  stageScope : scope coneStage.apex
  stageProjective : ProjectiveMorphism coneStage.snd
  test : TwoCartesianSquare
    (Pseudofunctor.StrongTrans.vcomp Z.val.inclusion
      (Pseudofunctor.StrongTrans.vcomp E.bundle.projection A.map)) f
  testScope : scope test.apex
  cone : IntrinsicConeModel test.fst
  coneScope : scope cone.total
  baseChange : ConeBaseChangeData test.fst f test.snd
    (Pseudofunctor.StrongTrans.vcomp Z.val.inclusion
      (Pseudofunctor.StrongTrans.vcomp E.bundle.projection A.map)) cone C
  /-- The cone base change uses the inverse of the test square's own cell (its square lists the
  two sides in the opposite order). -/
  baseChange_commutes : ∀ T : Over S, baseChange.commutes.app T = (test.commutes.app T).symm
  map : StackHom cone.total
    (K.restricted.pullback coneStage.apex A.source stageScope A.inScope coneStage.fst E).bundle.total
  closed : StackFibreModels.IsClosed map
  toCone : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp map
      (Pseudofunctor.StrongTrans.vcomp
        (K.restricted.pullback coneStage.apex A.source stageScope A.inScope coneStage.fst E).bundle.projection
        coneStage.snd)) baseChange.map
  toBundle : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp map
      (K.restricted.pullback coneStage.apex A.source stageScope A.inScope coneStage.fst E).map)
    (Pseudofunctor.StrongTrans.vcomp cone.projection
      (Pseudofunctor.StrongTrans.vcomp test.fst Z.val.inclusion))
  push : NaiveProjectivePushData D coneScope
    (K.restricted.inScope coneStage.apex A.source stageScope A.inScope coneStage.fst E) map
  fundamental : FundamentalCycleData D cone.total coneScope (d + E.bundle.rank)

def SpecializationRepresentativeData.value {D : CycleConstructionData S scope}
    {K : KreschPresentation D} {F G : Stack S} {f : StackHom F G}
    {C : IntrinsicConeModel f} {hC : scope C.total} {d : ℤ}
    {A : ProjectiveStage (scope := scope) G} {E : BundleStage (scope := scope) A.source}
    {Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank)}
    (V : SpecializationRepresentativeData D K f C hC d A E Z) : ChowGroup D K C.total hC d :=
  projectiveClass D K C.total hC d
    ⟨V.coneStage.apex, V.stageScope, V.coneStage.snd, V.stageProjective⟩
    (bundleClass D K.bundle V.coneStage.apex V.stageScope d
      (pulledStage K.restricted V.stageScope A.inScope V.coneStage.fst E)
      (naiveRegrade D
        (K.restricted.pullback V.coneStage.apex A.source V.stageScope A.inScope V.coneStage.fst E).bundle.total
        (K.restricted.inScope V.coneStage.apex A.source V.stageScope A.inScope V.coneStage.fst E)
        (by dsimp [pulledStage]; rw [(K.restricted.pullback V.coneStage.apex A.source
          V.stageScope A.inScope V.coneStage.fst E).rank_eq])
        (naiveCycleClass D _
          (K.restricted.inScope V.coneStage.apex A.source V.stageScope A.inScope V.coneStage.fst E)
          (d + E.bundle.rank) (V.push.cycle (d + E.bundle.rank) V.fundamental.cycle))))

structure SpecializationData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {F G : Stack S} (hF : scope F) (hG : scope G) {f : StackHom F G}
    (C : IntrinsicConeModel f) (hC : scope C.total) where
  stage : ∀ (d : ℤ) (A : ProjectiveStage (scope := scope) G)
    (E : BundleStage (scope := scope) A.source)
    (Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank)),
    SpecializationRepresentativeData D K f C hC d A E Z
  map : ∀ d : ℤ, RationalChowGroup D K G hG d →ₗ[ℚ] RationalChowGroup D K C.total hC d
  normalized : ∀ (d : ℤ) (A : ProjectiveStage (scope := scope) G)
    (E : BundleStage (scope := scope) A.source)
    (Z : IntegralClosedSubstack E.bundle.total (d + E.bundle.rank)),
    map d ((1 : ℚ) ⊗ₜ[ℤ] representative D K G hG d A E (cycleClass Z)) =
      (1 : ℚ) ⊗ₜ[ℤ] (stage d A E Z).value

structure VirtualPullbackRecipe (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {F G : Stack S} (hF : scope F) (hG : scope G) {f : StackHom F G}
    (E : VectorBundleStack F) (hE : scope E.total)
    (C : IntrinsicConeModel f) (hC : scope C.total) (i : ConeEmbedding C E) where
  specialization : SpecializationData D K hF hG C hC
  push : ProjectiveChowPushData D K hC hE i.map
  projection : FlatChowPullData D K hE hF E.projection E.virtualRank
  homotopy : BundleStackHomotopyData D K hF E hE projection

def virtualPullback {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {F G : Stack S} {hF : scope F} {hG : scope G} {f : StackHom F G}
    {E : VectorBundleStack F} {hE : scope E.total} {C : IntrinsicConeModel f}
    {hC : scope C.total} {i : ConeEmbedding C E}
    (R : VirtualPullbackRecipe D K hF hG E hE C hC i) (d : ℤ) :
    RationalChowGroup D K G hG d →ₗ[ℚ] RationalChowGroup D K F hF (d - E.virtualRank) :=
  (rationalMap (bundleStackZeroSectionInverse R.homotopy d)).comp
    ((rationalMap (R.push.map d)).comp (R.specialization.map d))

def virtualClass {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {F G : Stack S} {hF : scope F} {hG : scope G} {f : StackHom F G}
    {E : VectorBundleStack F} {hE : scope E.total} {C : IntrinsicConeModel f}
    {hC : scope C.total} {i : ConeEmbedding C E}
    (R : VirtualPullbackRecipe D K hF hG E hE C hC i) (d : ℤ)
    (M : FundamentalCycleData D G hG d) (classes : CycleClassData D K G hG) :
    RationalChowGroup D K F hF (d - E.virtualRank) :=
  virtualPullback R d (rationalCycleClass D K classes d M.cycle)

/-- The Construction 3.6 test scope: explicit quotient-stratified pullback
source. All finite-type scheme tests remain available by DM-type base
change and the sourced DM quotient-stratification theorem. -/
structure TestFamily {F G : Stack S} (f : StackHom F G) where
  target : Stack S
  targetScope : scope target
  map : StackHom target G
  square : TwoCartesianSquare f map
  sourceScope : scope square.apex
  stratification : QuotientStratification square.apex

structure RelativeVirtualPullbackData (D : CycleConstructionData S scope)
    (K : KreschPresentation D) {F G : Stack S} (hF : scope F) (hG : scope G)
    (f : StackHom F G) (E : VectorBundleStack F) (star : ConditionStar f E) where
  pullback : ∀ T : TestFamily (scope := scope) f, BundleStackPullback T.square.fst E
  bundleScope : ∀ T : TestFamily (scope := scope) f, scope (pullback T).bundle.total
  cone : ∀ T : TestFamily (scope := scope) f, IntrinsicConeModel T.square.snd
  coneScope : ∀ T : TestFamily (scope := scope) f, scope (cone T).total
  baseChange : ∀ T : TestFamily (scope := scope) f,
    ConeBaseChangeData T.square.snd f T.square.fst T.map (cone T) star.cone
  /-- The cone base change uses the test family's own square cell, not an independent one with
  the same four legs. -/
  baseChange_commutes : ∀ T : TestFamily (scope := scope) f,
    (baseChange T).commutes = T.square.commutes
  embedding : ∀ T : TestFamily (scope := scope) f, ConeEmbedding (cone T) (pullback T).bundle
  normalizedEmbedding : ∀ T : TestFamily (scope := scope) f, StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp (embedding T).map (pullback T).map)
    (Pseudofunctor.StrongTrans.vcomp (baseChange T).map star.embedding.map)
  recipe : ∀ T : TestFamily (scope := scope) f,
    VirtualPullbackRecipe D K T.sourceScope T.targetScope (pullback T).bundle
      (bundleScope T) (cone T) (coneScope T) (embedding T)

def relativeVirtualPullback {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {F G : Stack S} {hF : scope F} {hG : scope G} {f : StackHom F G}
    {E : VectorBundleStack F} {star : ConditionStar f E}
    (R : RelativeVirtualPullbackData D K hF hG f E star)
    (T : TestFamily (scope := scope) f) (d : ℤ) :
    RationalChowGroup D K T.target T.targetScope d →ₗ[ℚ]
      RationalChowGroup D K T.square.apex T.sourceScope (d - E.virtualRank) :=
  (rationalMap (chowRegrade D K T.square.apex T.sourceScope
    (by rw [(R.pullback T).rank_eq]))).comp (virtualPullback (R.recipe T) d)

/-- A pasted test square retains all native stack maps and both base 2-cells. -/
structure TestPasting {F G : Stack S} {f : StackHom F G}
    (P Q : TestFamily (scope := scope) f) where
  base : StackHom Q.target P.target
  source : StackHom Q.square.apex P.square.apex
  overG : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp base P.map) Q.map
  overF : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp source P.square.fst) Q.square.fst
  commutes : StackVectorBundles.TwoIso (Pseudofunctor.StrongTrans.vcomp source P.square.snd)
    (Pseudofunctor.StrongTrans.vcomp Q.square.snd base)
  cartesian : ∀ T : Over S,
    ((CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (StackCycleGeometry.component P.square.snd T) (StackCycleGeometry.component base T) _).obj
      ⟨StackCycleGeometry.component source T, StackCycleGeometry.component Q.square.snd T,
        commutes.app T⟩).IsEquivalence
  /-- The 2-cells paste: over `G`, the composite of `overF`, the cell of `P`'s square, `commutes`
  and `overG` is the cell of `Q`'s square, so the pasting is a morphism of the two fibre diagrams
  (an automorphism of the apex that only preserves the four legs does not qualify). -/
  pasting : ∀ (T : Over S) (x : Q.square.apex.Fibre T),
    (Q.square.commutes.app T).hom.app x =
      (StackCycleGeometry.component f T).map ((overF.app T).inv.app x) ≫
        (P.square.commutes.app T).hom.app ((StackCycleGeometry.component source T).obj x) ≫
        (StackCycleGeometry.component P.map T).map ((commutes.app T).hom.app x) ≫
        (overG.app T).hom.app ((StackCycleGeometry.component Q.square.snd T).obj x)

/-- The target has genuine rank-c normal bundle; its pullback fixes the
refined Gysin map on the source square, even when the base change is not regular. -/
structure GysinSquareData (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {F G : Stack S} {f : StackHom F G} {P Q : TestFamily (scope := scope) f}
    (p : TestPasting P Q) (c : ℕ) where
  normal : RegularNormalModel p.base c
  bundle : VectorBundleStack Q.target
  rank_eq : bundle.virtualRank = c
  normalComparison : StackEquivalence bundle.total normal.bundle.total
  normalOverBase : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp normalComparison.hom normal.bundle.projection) bundle.projection
  targetBundleScope : scope bundle.total
  targetConeScope : scope normal.cone.total
  targetEmbedding : ConeEmbedding normal.cone bundle
  normalizedTarget : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp targetEmbedding.map normalComparison.hom) normal.comparison.hom
  targetRecipe : VirtualPullbackRecipe D K Q.targetScope P.targetScope bundle
    targetBundleScope normal.cone targetConeScope targetEmbedding
  sourceBundle : BundleStackPullback Q.square.snd bundle
  sourceBundleScope : scope sourceBundle.bundle.total
  sourceCone : IntrinsicConeModel p.source
  sourceConeScope : scope sourceCone.total
  baseChange : ConeBaseChangeData p.source p.base Q.square.snd P.square.snd sourceCone normal.cone
  /-- The cone base change uses the inverse of the pasting's own cell (its square lists the two
  sides in the opposite order). -/
  baseChange_commutes : ∀ T : Over S, baseChange.commutes.app T = (p.commutes.app T).symm
  sourceEmbedding : ConeEmbedding sourceCone sourceBundle.bundle
  normalizedSource : StackVectorBundles.TwoIso
    (Pseudofunctor.StrongTrans.vcomp sourceEmbedding.map sourceBundle.map)
    (Pseudofunctor.StrongTrans.vcomp baseChange.map targetEmbedding.map)
  sourceRecipe : VirtualPullbackRecipe D K Q.sourceScope P.sourceScope sourceBundle.bundle
    sourceBundleScope sourceCone sourceConeScope sourceEmbedding

def GysinSquareData.targetMap {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {F G : Stack S} {f : StackHom F G} {P Q : TestFamily (scope := scope) f}
    {p : TestPasting P Q} {c : ℕ} (N : GysinSquareData D K p c) (d : ℤ) :
    RationalChowGroup D K P.target P.targetScope d →ₗ[ℚ]
      RationalChowGroup D K Q.target Q.targetScope (d - c) :=
  (rationalMap (chowRegrade D K Q.target Q.targetScope (by rw [N.rank_eq]))).comp
    (virtualPullback N.targetRecipe d)

def GysinSquareData.sourceMap {D : CycleConstructionData S scope} {K : KreschPresentation D}
    {F G : Stack S} {f : StackHom F G} {P Q : TestFamily (scope := scope) f}
    {p : TestPasting P Q} {c : ℕ} (N : GysinSquareData D K p c) (d : ℤ) :
    RationalChowGroup D K P.square.apex P.sourceScope d →ₗ[ℚ]
      RationalChowGroup D K Q.square.apex Q.sourceScope (d - c) :=
  (rationalMap (chowRegrade D K Q.square.apex Q.sourceScope
    (by rw [N.sourceBundle.rank_eq, N.rank_eq]))).comp (virtualPullback N.sourceRecipe d)

/-- `E` is a global quotient of two vector bundles on `F` (Manolache, arXiv:0805.2065v2,
Theorem 4.1, hypothesis (3)): it is the quotient, with coherent linear descent data, of a global
two-term complex of vector bundles on `F`. -/
def IsGlobalQuotient {F : Stack S} (E : VectorBundleStack F) : Prop :=
  ∃ (E₀ E₁ : VectorBundle F) (d : BundleMap E₀ E₁), IsQuotientOf E d

/-- The bivariant laws of a virtual pullback. The proper Deligne--Mumford pushforward law is only
asked under `properDMScope` (for virtual pullbacks: `E` is a global quotient, Manolache,
Theorem 4.1(i)); projective pushforward needs no such hypothesis (Remark 4.2). -/
structure BivariantLaws (D : CycleConstructionData S scope) (K : KreschPresentation D)
    {F G : Stack S} (f : StackHom F G) (n : ℤ) (properDMScope : Prop)
    (cap : ∀ T : TestFamily (scope := scope) f, ∀ d : ℤ,
      RationalChowGroup D K T.target T.targetScope d →ₗ[ℚ]
        RationalChowGroup D K T.square.apex T.sourceScope (d - n)) : Prop where
  projective : ∀ (P Q : TestFamily (scope := scope) f) (p : TestPasting P Q)
    (target : ProjectiveChowPushData D K Q.targetScope P.targetScope p.base)
    (source : ProjectiveChowPushData D K Q.sourceScope P.sourceScope p.source)
    (d : ℤ) (a : RationalChowGroup D K Q.target Q.targetScope d),
    cap P d (rationalMap (target.map d) a) = rationalMap (source.map (d - n)) (cap Q d a)
  properDM : properDMScope → ∀ (P Q : TestFamily (scope := scope) f) (p : TestPasting P Q)
    (targetModel : DMProperModel D K Q.targetScope P.targetScope p.base)
    (sourceModel : DMProperModel D K Q.sourceScope P.sourceScope p.source)
    (target : RationalPushData D K Q.targetScope P.targetScope p.base targetModel)
    (source : RationalPushData D K Q.sourceScope P.sourceScope p.source sourceModel)
    (d : ℤ) (a : RationalChowGroup D K Q.target Q.targetScope d),
    cap P d (target.map d a) = source.map (d - n) (cap Q d a)
  flat : ∀ (P Q : TestFamily (scope := scope) f) (p : TestPasting P Q) (e : ℤ)
    (target : FlatChowPullData D K Q.targetScope P.targetScope p.base e)
    (source : FlatChowPullData D K Q.sourceScope P.sourceScope p.source e)
    (d : ℤ) (a : RationalChowGroup D K P.target P.targetScope d),
    cap Q (d + e) (rationalMap (target.map d) a) =
      rationalMap (chowRegrade D K Q.square.apex Q.sourceScope (by omega))
        (rationalMap (source.map (d - n)) (cap P d a))
  gysin : ∀ (P Q : TestFamily (scope := scope) f) (p : TestPasting P Q) (c : ℕ)
    (normal : GysinSquareData D K p c) (d : ℤ)
    (a : RationalChowGroup D K P.target P.targetScope d),
    cap Q (d - c) (normal.targetMap d a) =
      rationalMap (chowRegrade D K Q.square.apex Q.sourceScope (by omega))
        (normal.sourceMap (d - n) (cap P d a))

end AlgebraicGeometry.StackVirtualPullbacks
