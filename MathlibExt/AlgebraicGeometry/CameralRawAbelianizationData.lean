/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralChevalleyConventionModels

/-!
# Raw Borel shifts and their pinned convention adapter

The raw native Borel pushout has inverse torus gamma and inverse SL2
parameter beta. All quotients, native line maps, coroot and normalizer
conjugation diagrams stay explicit. The adapter precomposes gamma with
the actual pinned normalizer automorphism and beta with Gm inversion.
It retains the actual underlying torus bundle and the actual R_w data.
The reference simple-root lift is fixed, so its ramification divisor
and full computed-dual line comparison are retained.
Source: DG arXiv:math/0005132v3, Sections 6--8 and 15--16, interpreted
through the actual left-action group-torsor presentation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CameralRawAbelianizationData

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralNormalizerShifts CameralLiftedNormalizerModels CameralLiftedRamificationData
open CameralChevalleyConventionModels ContractedTorsorModels ExpansionParameterModels
open TorusLineFrameModels CoherentCurveLinearSeries FiniteCoverLocalComparison

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  {X : Over (Spec (.of ℂ))} {C : Cover F X} (B : ParameterCovers F C)

attribute [local instance] CameralRamificationTensorModels.torusGroup

variable (L : Bundle (Torus F) (total F C))

structure RawNormalizerShift where
  gamma : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (_hw : Label F n w),
    shifted F K D (B.pulled U).cover w (parameterBundle F K D B L U) ≅ parameterBundle F K D B L U
  torus : ∀ (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F), TorusTranslation F K D B L U t
  torus_label : ∀ (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F),
    Label F (t ≫ F.normalizer.torus) 1
  torus_restriction : ∀ (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F),
    (gamma U (t ≫ F.normalizer.torus) 1 (torus_label U t)).hom =
      (shiftUnit F K D R (B.pulled U).cover (parameterBundle F K D B L U)).hom ≫
        (torus U (t ≫ ι[Torus F])).iso.hom
  composition : ∀ (U : Over (Spec (.of ℂ))) (n m : U ⟶ F.normalizer.scheme)
      (u v : F.Weyl) (hn : Label F n u) (hm : Label F m v),
    (gamma U (normalizerProduct F n m) (u * v) (productLabel F n m u v hn hm)).hom =
      (shiftComposition F K D R (B.pulled U).cover u v (parameterBundle F K D B L U)).hom ≫
      (shiftFunctor F K D (B.pulled U).cover v).map (gamma U n u hn).hom ≫ (gamma U m v hm).hom
  naturality : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (hn : Label F n w) (hf : Label F (f ≫ n) w),
    (D.torus.baseChange.change (B.arrow f).total).map (gamma U n w hn).hom ≫
      (parameterBundleIso F K D B L f).hom =
    (shiftBaseIso F K D R B f w (parameterBundle F K D B L U)).hom ≫
      (shiftFunctor F K D (B.pulled V).cover w).map (parameterBundleIso F K D B L f).hom ≫
        (gamma V (f ≫ n) w hf).hom

structure RawBetaMaps where
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
          (fixedInclusion F (B.pulled U).cover i ≫ parameterProjection F B U ≫
            c ≫ ι[torusScheme ℂ 1]) 0)
  base_change : ∀ {U V : Over (Spec (.of ℂ))} (f : V ⟶ U) (i : Fin F.roots.count)
      (hi : SimpleRoot G tori F i) (c : U ⟶ torusScheme ℂ 1),
    (Scheme.Modules.pullback (fixedMap F (B.arrow f) i (B.reflections f i)).left).map
      (beta U i hi c).hom ≫ (ramifiedLinePullback F K D R B f i).hom =
    (higgsLinePullback F K D A B L f i).hom ≫ (beta V i hi (f ≫ c)).hom


variable (β : RawBetaMaps F K D R A B L)

def rawBetaValue (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count) (hi : SimpleRoot G tori F i)
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

def rawTransportedBetaValue (E : RootWeylGeometry F K) (U : Over (Spec (.of ℂ)))
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
  rawBetaValue F K D R A B L β U j hj c V
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


variable (S : RawNormalizerShift F K D R B L) (Q : SimpleReflectionTorsors F K D R)
  (E : RootWeylGeometry F K) (T : CanonicalSimpleRootTrivializations F K D R A)

structure RawBetaCompatibility where
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
        rawBetaValue F K D R A B L β U i hi c V y p hp)
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
    rawBetaValue F K D R A B L β U i hi (transportedParameter F K U n w hn i j hij c) V y
      (tensorPoint (D.torus.tensor.model (total F (B.pulled U).cover)
        (combined F K D (B.pulled U).cover w (parameterBundle F K D B L U))
        (ramificationTorsor F K D (B.pulled U).cover w)) q t hqt ≫
          (S.gamma U n w hn).hom.iso.hom) hp =
    twistFrameValue F K D R A B T U i w hi (by simpa only [hij] using hj) V y t ht ≫
      rawTransportedBetaValue F K D R A B L β E U i j hi hj w hij c V y
        (q ≫ combinedOriginal F K D (B.pulled U).cover ((R.weyl (B.pulled U).cover).model w
          (parameterBundle F K D B L U))) hq

variable (Θ : ChevalleyComparison F K)

def adaptedGamma (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
    (w : F.Weyl) (hn : Label F n w) :
    shifted F K D (B.pulled U).cover w (parameterBundle F K D B L U) ≅
      parameterBundle F K D B L U :=
  S.gamma U (n ≫ Θ.normalizer.hom) w (thetaLabel F K Θ n w hn)

def adaptedBeta (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count)
    (hi : SimpleRoot G tori F i) (c : U ⟶ torusScheme ℂ 1) :
    higgsLine F K D A (B.pulled U).cover i (parameterBundle F K D B L U) ≅
      ramifiedLine F (B.pulled U).cover i := by
  letI := (tori 1).group
  exact β.beta U i hi (c ≫ ι[torusScheme ℂ 1])

structure AdaptedRamificationData (J : RawBetaCompatibility F K D R A B L β S Q E T) where
  shift : ConstantNormalizerShift F K D R B L
  gamma_normalized : ∀ (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
      (w : F.Weyl) (hn : Label F n w),
    shift.gamma U n w hn = adaptedGamma F K D R B L S Θ U n w hn
  beta : LiftedBetaMaps F K D R A B L
  beta_normalized : ∀ (U : Over (Spec (.of ℂ))) (i : Fin F.roots.count)
      (hi : SimpleRoot G tori F i) (c : U ⟶ torusScheme ℂ 1),
    beta.beta U i hi c = adaptedBeta F K D R A B L β U i hi c
  compatibility : LiftedBetaCompatibility F K D R A B L beta shift Q E T
  full : FullNormalizerShift F K D R B L shift

end MathlibExt.AlgebraicGeometry.CameralRawAbelianizationData
