/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralLiftedNormalizerModels

/-!
# Lifted beta data and the three native ramification conditions

Beta is a native line isomorphism on the reflection equalizer for each
actual SL2 normalizer parameter c. It scales by c before mapping to G.
Condition two is the actual coroot-pushout quotient-point diagram for
gamma(n(c)). Condition three evaluates gamma, the Proposition 5.5
trivialization and the transported Borel-root ramification line, using
the inverse adjoint coefficient on the actual lifted SL2 parameter.
All equations use native modules and full scheme-valued frames.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Section 6.2(1)--(3).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralLiftedRamificationData

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralNormalizerShifts CameralLiftedNormalizerModels
open ContractedTorsorModels ExpansionParameterModels TorusLineFrameModels
open CoherentCurveLinearSeries FiniteCoverLocalComparison

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)

attribute [local instance] CameralRamificationTensorModels.torusGroup

abbrev higgsLine {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count)
    (L : Bundle (Torus F) (total F C)) : (fixedScheme F C i).left.Modules :=
  (Scheme.Modules.pullback (fixedInclusion F C i).left).obj ((A.line (total F C) i).obj L)

def ramifiedLine {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count) :
    (fixedScheme F C i).left.Modules :=
  (Scheme.Modules.pullback (fixedInclusion F C i).left).obj (line F C i)

variable {X : Over (Spec (.of ℂ))} {C : Cover F X} (B : ParameterCovers F C)
  (L : Bundle (Torus F) (total F C))

def higgsLinePullback {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (i : Fin F.roots.count) :
    (Scheme.Modules.pullback (fixedMap F (B.arrow f) i (B.reflections f i)).left).obj
      (higgsLine F K D A (B.pulled U).cover i (parameterBundle F K D B L U)) ≅
    higgsLine F K D A (B.pulled V).cover i (parameterBundle F K D B L V) :=
  (Scheme.Modules.pullbackComp (fixedMap F (B.arrow f) i (B.reflections f i)).left
    (fixedInclusion F (B.pulled U).cover i).left).app _ ≪≫
  (Scheme.Modules.pullbackCongr
    (congrArg (fun q : fixedScheme F (B.pulled V).cover i ⟶ total F (B.pulled U).cover => q.left)
      (fixedMap_inclusion F (B.arrow f) i (B.reflections f i)))).app _ ≪≫
  (Scheme.Modules.pullbackComp (fixedInclusion F (B.pulled V).cover i).left
    (B.arrow f).total.left).symm.app _ ≪≫
  (Scheme.Modules.pullback (fixedInclusion F (B.pulled V).cover i).left).mapIso
    ((A.pullback (B.arrow f).total i).app (parameterBundle F K D B L U) ≪≫
      (A.line (total F (B.pulled V).cover) i).mapIso (parameterBundleIso F K D B L f))

def ramifiedLinePullback {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (i : Fin F.roots.count) :
    (Scheme.Modules.pullback (fixedMap F (B.arrow f) i (B.reflections f i)).left).obj
      (ramifiedLine F (B.pulled U).cover i) ≅ ramifiedLine F (B.pulled V).cover i :=
  (Scheme.Modules.pullbackComp (fixedMap F (B.arrow f) i (B.reflections f i)).left
    (fixedInclusion F (B.pulled U).cover i).left).app _ ≪≫
  (Scheme.Modules.pullbackCongr
    (congrArg (fun q : fixedScheme F (B.pulled V).cover i ⟶ total F (B.pulled U).cover => q.left)
      (fixedMap_inclusion F (B.arrow f) i (B.reflections f i)))).app _ ≪≫
  (Scheme.Modules.pullbackComp (fixedInclusion F (B.pulled V).cover i).left
    (B.arrow f).total.left).symm.app _ ≪≫
  (Scheme.Modules.pullback (fixedInclusion F (B.pulled V).cover i).left).mapIso
    (R.symbols.map (B.arrow f) i i (B.reflections f i)).line

structure LiftedBetaMaps where
  beta : ∀ (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count)
      (_hi : SimpleRoot G tori F i) (_c : U ⟶ torusScheme ℂ 1),
    higgsLine F K D A (B.pulled U).cover i (parameterBundle F K D B L U) ≅
      ramifiedLine F (B.pulled U).cover i
  scaling : letI := (tori 1).group
    ∀ (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (hi : SimpleRoot G tori F i)
      (c : U ⟶ torusScheme ℂ 1),
    beta U i hi c = beta U i hi (toUnit U ≫ η[torusScheme ℂ 1]) ≪≫
      scalarIso (fixedScheme F (B.pulled U).cover i).left (ramifiedLine F (B.pulled U).cover i)
        ((tori 1).units (fixedScheme F (B.pulled U).cover i)
          (fixedInclusion F (B.pulled U).cover i ≫ parameterProjection F B U ≫ c) 0)
  base_change : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (i : Fin F.roots.count)
      (hi : SimpleRoot G tori F i) (c : U ⟶ torusScheme ℂ 1),
    (Scheme.Modules.pullback (fixedMap F (B.arrow f) i (B.reflections f i)).left).map
      (beta U i hi c).hom ≫ (ramifiedLinePullback F K D R B f i).hom =
    (higgsLinePullback F K D A B L f i).hom ≫ (beta V i hi (f ≫ c)).hom

variable (β : LiftedBetaMaps F K D R A B L)

def betaValue (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (hi : SimpleRoot G tori F i)
    (c : U ⟶ torusScheme ℂ 1) (V : Over (Spec (.of ℂ)))
    (y : V ⟶ fixedScheme F (B.pulled U).cover i)
    (p : V ⟶ (parameterBundle F K D B L U).torsor.total)
    (hp : p ≫ (parameterBundle F K D B L U).torsor.projection =
      y ≫ fixedInclusion F (B.pulled U).cover i) :
    structureModule V.left ⟶
      (Scheme.Modules.pullback (y ≫ fixedInclusion F (B.pulled U).cover i).left).obj
        (line F (B.pulled U).cover i) := by
  letI := (tori 1).group
  exact (frameBasis (tori 1) (total F (B.pulled U).cover)
    ((A.line (total F (B.pulled U).cover) i).obj (parameterBundle F K D B L U))
    (A.realization (total F (B.pulled U).cover) i (parameterBundle F K D B L U)).frames
    V (y ≫ fixedInclusion F (B.pulled U).cover i)
    (characterFrame F K D (A.realization (total F (B.pulled U).cover) i
      (parameterBundle F K D B L U)) p)
    ((characterFrame_over F K D _ p).trans hp)).hom ≫
    (Scheme.Modules.pullbackComp y.left (fixedInclusion F (B.pulled U).cover i).left).inv.app _ ≫
    (Scheme.Modules.pullback y.left).map (β.beta U i hi c).hom ≫
    (Scheme.Modules.pullbackComp y.left (fixedInclusion F (B.pulled U).cover i).left).hom.app _

omit [GeneralLinearFrameSchemes.FrameTheory 2] [RankTwoMatrixGroupModels.GL2MatrixTheory]
    [RankTwoMatrixGroupModels.SL2MatrixTheory] in
theorem fixedReflection {Y : Over (Spec (.of ℂ))} (C' : Cover F Y) (i : Fin F.roots.count) :
    fixedInclusion F C' i ≫ (coverIso F C' (F.roots.reflection i)).hom = fixedInclusion F C' i := by
  apply Over.OverMorphism.ext
  change equalizer.ι (reflection F C' i).hom (𝟙 (total F C').left) ≫ (reflection F C' i).hom = _
  rw [equalizer.condition]
  simp [fixedInclusion]

def fixedCombinedPoint {Y : Over (Spec (.of ℂ))} (C' : Cover F Y) (i : Fin F.roots.count)
    (P : Bundle (Torus F) (total F C')) (V : Over (Spec (.of ℂ))) (y : V ⟶ fixedScheme F C' i)
    (p : V ⟶ P.torsor.total) (hp : p ≫ P.torsor.projection = y ≫ fixedInclusion F C' i) :
    TorsorPoint F (combined F K D C' (F.roots.reflection i) P) (y ≫ fixedInclusion F C' i) := by
  let M := (R.weyl C').model (F.roots.reflection i) P
  have h : p ≫ P.torsor.projection =
      (y ≫ fixedInclusion F C' i) ≫ (coverIso F C' (F.roots.reflection i)).hom := by
    rw [Category.assoc, fixedReflection]
    exact hp
  refine ⟨pullback.lift p (y ≫ fixedInclusion F C' i) h ≫ M.comparison.inv, ?_⟩
  rw [← M.projection]
  simp

theorem rootReflection (E : RootWeylGeometry F K) {Y : Over (Spec (.of ℂ))} (C' : Cover F Y)
    (w : F.Weyl) (i j : Fin F.roots.count) (hij : K.permutations.index w i = j) :
    (reflection F C' i).hom ≫ (coverIso F C' w).hom.left =
      (coverIso F C' w).hom.left ≫ (reflection F C' j).hom := by
  have h := E.reflection C' w i j hij
  change (reflection F C' i).hom ≫ (E.arrow C' w).total.left =
    (E.arrow C' w).total.left ≫ (reflection F C' j).hom at h
  rw [E.total C' w] at h
  exact h

def rootLineTransport (E : RootWeylGeometry F K) {Y : Over (Spec (.of ℂ))} (C' : Cover F Y)
    (w : F.Weyl) (i j : Fin F.roots.count) (hij : K.permutations.index w i = j) :
    (Scheme.Modules.pullback (coverIso F C' w).hom.left).obj (line F C' j) ≅ line F C' i :=
  (Scheme.Modules.pullbackCongr
    (congrArg (fun f : total F C' ⟶ total F C' => f.left) (E.total C' w).symm)).app _ ≪≫
      (R.symbols.map (E.arrow C' w) i j (E.reflection C' w i j hij)).line

def transportedBetaValue (E : RootWeylGeometry F K) (U : Over (Spec (.of ℂ)))
    (i j : Fin F.roots.count) (_hi : SimpleRoot G tori F i) (hj : SimpleRoot G tori F j)
    (w : F.Weyl) (hij : K.permutations.index w i = j) (c : U ⟶ torusScheme ℂ 1)
    (V : Over (Spec (.of ℂ))) (y : V ⟶ fixedScheme F (B.pulled U).cover i)
    (q : V ⟶ (parameterBundle F K D B L U).torsor.total)
    (hq : q ≫ (parameterBundle F K D B L U).torsor.projection =
      (y ≫ fixedTransport F (B.pulled U).cover w i j (rootReflection F K E _ w i j hij)) ≫
        fixedInclusion F (B.pulled U).cover j) :
    structureModule V.left ⟶
      (Scheme.Modules.pullback (y ≫ fixedInclusion F (B.pulled U).cover i).left).obj
        (line F (B.pulled U).cover i) :=
  betaValue F K D R A B L β U j hj c V
    (y ≫ fixedTransport F (B.pulled U).cover w i j (rootReflection F K E _ w i j hij)) q hq ≫
  (Scheme.Modules.pullbackCongr (by
    have h : (y ≫ fixedTransport F (B.pulled U).cover w i j
        (rootReflection F K E _ w i j hij)) ≫ fixedInclusion F (B.pulled U).cover j =
        (y ≫ fixedInclusion F (B.pulled U).cover i) ≫ (coverIso F (B.pulled U).cover w).hom := by
      rw [Category.assoc, fixedTransport_inclusion, ← Category.assoc]
    simpa only [Over.comp_left] using
      congrArg (fun f : V ⟶ total F (B.pulled U).cover => f.left) h)).hom.app _ ≫
  (Scheme.Modules.pullbackComp (y ≫ fixedInclusion F (B.pulled U).cover i).left
    (coverIso F (B.pulled U).cover w).hom.left).inv.app _ ≫
  (Scheme.Modules.pullback (y ≫ fixedInclusion F (B.pulled U).cover i).left).map
    (rootLineTransport F K D R E _ w i j hij).hom

def twistFrameValue (T : CanonicalSimpleRootTrivializations F K D R A)
    (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (w : F.Weyl)
    (hi : SimpleRoot G tori F i) (hw : SimpleRoot G tori F (K.permutations.index w i))
    (V : Over (Spec (.of ℂ))) (y : V ⟶ fixedScheme F (B.pulled U).cover i)
    (t : V ⟶ (ramificationTorsor F K D (B.pulled U).cover w).torsor.total)
    (ht : t ≫ (ramificationTorsor F K D (B.pulled U).cover w).torsor.projection =
      y ≫ fixedInclusion F (B.pulled U).cover i) :
    structureModule V.left ⟶ structureModule V.left := by
  letI := (tori 1).group
  exact (frameBasis (tori 1) (total F (B.pulled U).cover)
    ((A.line (total F (B.pulled U).cover) i).obj (ramificationTorsor F K D (B.pulled U).cover w))
    (A.realization (total F (B.pulled U).cover) i
      (ramificationTorsor F K D (B.pulled U).cover w)).frames
    V (y ≫ fixedInclusion F (B.pulled U).cover i)
    (characterFrame F K D (A.realization (total F (B.pulled U).cover) i
      (ramificationTorsor F K D (B.pulled U).cover w)) t)
    ((characterFrame_over F K D _ t).trans ht)).hom ≫
    (Scheme.Modules.pullbackComp y.left (fixedInclusion F (B.pulled U).cover i).left).inv.app _ ≫
    (Scheme.Modules.pullback y.left).map (T.trivialization (B.pulled U).cover i w hi hw).hom ≫
    (pullbackStructureIso y.left).hom

variable (S : ConstantNormalizerShift F K D R B L) (Q : SimpleReflectionTorsors F K D R)
  (E : RootWeylGeometry F K) (T : CanonicalSimpleRootTrivializations F K D R A)

structure LiftedBetaCompatibility where
  coroot : letI := (tori 1).group
    ∀ (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (hi : SimpleRoot G tori F i)
      (c : U ⟶ torusScheme ℂ 1) (V : Over (Spec (.of ℂ)))
      (y : V ⟶ fixedScheme F (B.pulled U).cover i)
      (p : V ⟶ (parameterBundle F K D B L U).torsor.total)
      (hp : p ≫ (parameterBundle F K D B L U).torsor.projection =
        y ≫ fixedInclusion F (B.pulled U).cover i)
      (r : V ⟶ (frames F (B.pulled U).cover i).bundle.torsor.total)
      (hr : r ≫ (frames F (B.pulled U).cover i).bundle.torsor.projection =
        y ≫ fixedInclusion F (B.pulled U).cover i)
      (_hβ : (frameBasis (tori 1) (total F (B.pulled U).cover) (line F (B.pulled U).cover i)
        (frames F (B.pulled U).cover i) V (y ≫ fixedInclusion F (B.pulled U).cover i) r hr).hom =
        betaValue F K D R A B L β U i hi c V y p hp)
      (hprod : (fixedCombinedPoint F K D R (B.pulled U).cover i
        (parameterBundle F K D B L U) V y p hp).val ≫
        (combined F K D (B.pulled U).cover (F.roots.reflection i)
          (parameterBundle F K D B L U)).torsor.projection =
        (CartesianMonoidalCategory.lift r (toUnit V ≫ η[Torus F]) ≫
          (rootPushout F K D (B.pulled U).cover i).quotient ≫
          (Q.iso (B.pulled U).cover i hi).inv.iso.hom) ≫
          (ramificationTorsor F K D (B.pulled U).cover (F.roots.reflection i)).torsor.projection),
    tensorPoint (D.torus.tensor.model (total F (B.pulled U).cover)
      (combined F K D (B.pulled U).cover (F.roots.reflection i) (parameterBundle F K D B L U))
      (ramificationTorsor F K D (B.pulled U).cover (F.roots.reflection i)))
      (fixedCombinedPoint F K D R (B.pulled U).cover i
        (parameterBundle F K D B L U) V y p hp).val
      (CartesianMonoidalCategory.lift r (toUnit V ≫ η[Torus F]) ≫
        (rootPushout F K D (B.pulled U).cover i).quotient ≫
          (Q.iso (B.pulled U).cover i hi).inv.iso.hom)
      hprod ≫
      (S.gamma U (c ≫ (K.sl2 i).normalizer) (F.roots.reflection i)
        ((K.sl2 i).normalizer_weyl U c)).hom.iso.hom = p
  conjugation : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl)
      (hn : Label F n w) (i j : Fin F.roots.count) (hi : SimpleRoot G tori F i)
      (hj : SimpleRoot G tori F j) (hij : K.permutations.index w i = j) (c : U ⟶ torusScheme ℂ 1)
      (V : Over (Spec (.of ℂ))) (y : V ⟶ fixedScheme F (B.pulled U).cover i)
      (q : V ⟶ (combined F K D (B.pulled U).cover w (parameterBundle F K D B L U)).torsor.total)
      (t : V ⟶ (ramificationTorsor F K D (B.pulled U).cover w).torsor.total)
      (ht : t ≫ (ramificationTorsor F K D (B.pulled U).cover w).torsor.projection =
        y ≫ fixedInclusion F (B.pulled U).cover i)
      (hqt : q ≫ (combined F K D (B.pulled U).cover w
          (parameterBundle F K D B L U)).torsor.projection =
        t ≫ (ramificationTorsor F K D (B.pulled U).cover w).torsor.projection)
      (hp : (tensorPoint (D.torus.tensor.model (total F (B.pulled U).cover)
        (combined F K D (B.pulled U).cover w (parameterBundle F K D B L U))
        (ramificationTorsor F K D (B.pulled U).cover w)) q t hqt ≫ (S.gamma U n w hn).hom.iso.hom) ≫
        (parameterBundle F K D B L U).torsor.projection = y ≫ fixedInclusion F (B.pulled U).cover i)
      (hq : (q ≫ combinedOriginal F K D (B.pulled U).cover ((R.weyl (B.pulled U).cover).model w
        (parameterBundle F K D B L U))) ≫ (parameterBundle F K D B L U).torsor.projection =
        (y ≫ fixedTransport F (B.pulled U).cover w i j (rootReflection F K E _ w i j hij)) ≫
          fixedInclusion F (B.pulled U).cover j),
    betaValue F K D R A B L β U i hi (transportedParameter F K U n w hn i j hij c) V y
      (tensorPoint (D.torus.tensor.model (total F (B.pulled U).cover)
        (combined F K D (B.pulled U).cover w (parameterBundle F K D B L U))
        (ramificationTorsor F K D (B.pulled U).cover w)) q t hqt ≫
          (S.gamma U n w hn).hom.iso.hom) hp =
    twistFrameValue F K D R A B T U i w hi (by simpa only [hij] using hj) V y t ht ≫
      transportedBetaValue F K D R A B L β E U i j hi hj w hij c V y
        (q ≫ combinedOriginal F K D (B.pulled U).cover ((R.weyl (B.pulled U).cover).model w
          (parameterBundle F K D B L U))) hq

end MathlibExt.AlgebraicGeometry.CameralLiftedRamificationData
