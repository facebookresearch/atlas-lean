/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairCochainTensorMaps

/-!
# Applying the actual universal Atiyah kernel

Kernel maps act by native pullback, derived tensor and direct image.
The diagonal comparison is a computed composite of their native
cochain units/counits, the all-degree projection-formula map, and
normalized direct-image pasting. Its identity specialization uses
the genuine cochain right unitor. Invertibility proofs are separate.

References: Huybrechts–Thomas, arXiv:0805.3527v2, Definition 2.6,
(2.12); Pandharipande–Thomas, arXiv:0707.2348v5, (2.12).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairFourierMukaiAtiyah

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open FourierMukai CoherentCurveLinearSeries StablePairDiagonalIdeals
open StablePairAtiyahKernels StablePairCochainTensorMaps NormalizedModuleTensorMaps
attribute [local instance] HasDerivedCategory.standard

abbrev cochainPullback {X Y : Scheme} (f : X ⟶ Y) :=
  (Scheme.Modules.pullback f).mapHomologicalComplex (.up ℤ)

abbrev cochainPushforward {X Y : Scheme} (f : X ⟶ Y) :=
  (Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)

def cochainPushforwardComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : Cochains X) :
    (cochainPushforward g).obj ((cochainPushforward f).obj K) ≅
      (cochainPushforward (f ≫ g)).obj K :=
  (Functor.mapHomologicalComplexCompIso (Scheme.Modules.pushforwardComp f g) (.up ℤ)).app K

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- The native pullback counit with its cochain target displayed. -/
def pullbackCounit {X Y : Scheme} (f : X ⟶ Y) (K : Cochains Y) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((cochainPullback f).obj K) := by
  simpa only [pullbackSource, Functor.comp_obj] using (derivedPullbackCounit f).app K

/-- The native pushforward unit with its cochain source displayed. -/
def pushforwardUnit {X Y : Scheme} (f : X ⟶ Y) (K : Cochains X) :
    DerivedCategory.Q.obj ((cochainPushforward f).obj K) ⟶
      (derivedPushforward f).obj (DerivedCategory.Q.obj K) := by
  simpa only [pushforwardSource, Functor.comp_obj] using (derivedPushforwardUnit f).app K

/-- Derived direct-image pasting fixed on every cochain source by its native units. -/
structure PushforwardPasting {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) where
  comparison : derivedPushforward f ⋙ derivedPushforward g ≅ derivedPushforward (f ≫ g)
  normalized : ∀ K : Cochains X,
    (derivedPushforwardUnit g).app ((cochainPushforward f).obj K) ≫
        (derivedPushforward g).map ((derivedPushforwardUnit f).app K) ≫
          comparison.hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map (cochainPushforwardComp f g K).hom ≫
        (derivedPushforwardUnit (f ≫ g)).app K

/-- The identity direct image fixed by the native cochain identity comparison. -/
structure PushforwardIdentity (X : Scheme) where
  comparison : derivedPushforward (𝟙 X) ≅ 𝟭 (D X)
  normalized : ∀ K : Cochains X,
    (derivedPushforwardUnit (𝟙 X)).app K ≫ comparison.hom.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (Scheme.Modules.pushforwardId X) (.up ℤ)).app K).hom ≫
          DerivedCategory.Q.map ((Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)).app K).hom

variable (Y : Over (Spec (.of ℂ)))

/-- Cancel the actual diagonal followed by second projection using native units and pasting. -/
def collapseDiagonal
    (P : PushforwardPasting (diagonal Y) (pullback.snd Y.hom Y.hom))
    (I : PushforwardIdentity Y.left) (K : Cochains Y.left) :
    (derivedPushforward (pullback.snd Y.hom Y.hom)).obj
      (DerivedCategory.Q.obj ((cochainPushforward (diagonal Y)).obj K)) ⟶
        DerivedCategory.Q.obj K :=
  (derivedPushforward (pullback.snd Y.hom Y.hom)).map
      ((derivedPushforwardUnit (diagonal Y)).app K) ≫
    P.comparison.hom.app (DerivedCategory.Q.obj K) ≫
      (eqToIso (congrArg derivedPushforward
        (show diagonal Y ≫ pullback.snd Y.hom Y.hom = 𝟙 Y.left by
          simp [diagonal]))).hom.app (DerivedCategory.Q.obj K) ≫
        I.comparison.hom.app (DerivedCategory.Q.obj K)

/-- A morphism of genuine kernels acts by the three actual derived operators. -/
def kernelMap {K L : D (pullback Y.hom Y.hom)} (a : K ⟶ L) (E : D Y.left) :
    (fourierMukai Y.hom Y.hom K).obj E ⟶ (fourierMukai Y.hom Y.hom L).obj E :=
  (derivedPushforward (pullback.snd Y.hom Y.hom)).map
    ((derivedTensorUncurried (pullback Y.hom Y.hom)).map
      (𝟙 ((derivedPullback (pullback.fst Y.hom Y.hom)).obj E), a))

/-- The computed diagonal/tensor map on actual cochain representatives. -/
def diagonalTensorMap (K L : Cochains Y.left)
    (T : PullbackTensor (diagonal Y)) (G : DiagonalCochainMap Y T K L)
    (P : PushforwardPasting (diagonal Y) (pullback.snd Y.hom Y.hom))
    (I : PushforwardIdentity Y.left)
    (hΔ : IsIso ((derivedPushforwardUnit (diagonal Y)).app L))
    (hTensor : IsIso (tensorCounit Y.left K L)) :
    (fourierMukai Y.hom Y.hom
      ((derivedPushforward (diagonal Y)).obj (DerivedCategory.Q.obj L))).obj
        (DerivedCategory.Q.obj K) ⟶
      (derivedTensorUncurried Y.left).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) := by
  letI := hΔ
  letI := hTensor
  exact (derivedPushforward (pullback.snd Y.hom Y.hom)).map
      ((derivedTensorUncurried (pullback Y.hom Y.hom)).map
        (pullbackCounit (pullback.fst Y.hom Y.hom) K,
          inv ((derivedPushforwardUnit (diagonal Y)).app L)) ≫
        tensorCounit (pullback Y.hom Y.hom)
          ((cochainPullback (pullback.fst Y.hom Y.hom)).obj K)
          ((cochainPushforward (diagonal Y)).obj L)) ≫
    (derivedPushforward (pullback.snd Y.hom Y.hom)).map (DerivedCategory.Q.map G.map) ≫
      collapseDiagonal Y P I ((cochainTensor Y.left).obj (K,L)) ≫
        inv (tensorCounit Y.left K L)

abbrev unitComplex := (CochainComplex.singleFunctor Y.left.Modules 0).obj (structureModule Y.left)

/-- The source kernel's actual single/pushforward comparison. -/
def sourceKernelComparison :
    DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (pullback Y.hom Y.hom).Modules 0).obj
        ((Scheme.Modules.pushforward (diagonal Y)).obj (structureModule Y.left))) ⟶
      (derivedPushforward (diagonal Y)).obj (DerivedCategory.Q.obj (unitComplex Y)) :=
  DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex (Scheme.Modules.pushforward (diagonal Y))
        (.up ℤ) 0).inv.app (structureModule Y.left)) ≫
    (derivedPushforwardUnit (diagonal Y)).app (unitComplex Y)

/-- The computed identity-kernel map, including the genuine unitor. -/
def identityKernelMap (K : Cochains Y.left)
    (T : PullbackTensor (diagonal Y)) (G : DiagonalCochainMap Y T K (unitComplex Y))
    (U : RightUnitCochainMap Y K)
    (P : PushforwardPasting (diagonal Y) (pullback.snd Y.hom Y.hom))
    (I : PushforwardIdentity Y.left)
    (hΔ : IsIso ((derivedPushforwardUnit (diagonal Y)).app (unitComplex Y)))
    (hTensor : IsIso (tensorCounit Y.left K (unitComplex Y))) :
    (fourierMukai Y.hom Y.hom
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (pullback Y.hom Y.hom).Modules 0).obj
          ((Scheme.Modules.pushforward (diagonal Y)).obj (structureModule Y.left))))).obj
        (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj K :=
  kernelMap Y (sourceKernelComparison Y) (DerivedCategory.Q.obj K) ≫
    diagonalTensorMap Y K (unitComplex Y) T G P I hΔ hTensor ≫
      tensorCounit Y.left K (unitComplex Y) ≫ DerivedCategory.Q.map U.map

/-- The actual truncated Atiyah class obtained from the source kernel diagram. -/
def truncatedAtiyah {Z : Over (Spec (.of ℂ))} (i : Y ⟶ Z)
    (S : IdealSquare (diagonal Z)) (A : ResolutionAugmentation i) (B : KernelProjection i S)
    (K : Cochains Y.left) (T : PullbackTensor (diagonal Y))
    (G₀ : DiagonalCochainMap Y T K (unitComplex Y)) (U : RightUnitCochainMap Y K)
    (G₁ : DiagonalCochainMap Y T K ((cotangent i S)⟦(1 : ℤ)⟧))
    (P : PushforwardPasting (diagonal Y) (pullback.snd Y.hom Y.hom))
    (I : PushforwardIdentity Y.left)
    (h₀ : IsIso ((derivedPushforwardUnit (diagonal Y)).app (unitComplex Y)))
    (h₁ : IsIso ((derivedPushforwardUnit (diagonal Y)).app ((cotangent i S)⟦(1 : ℤ)⟧)))
    (ht₀ : IsIso (tensorCounit Y.left K (unitComplex Y)))
    (ht₁ : IsIso (tensorCounit Y.left K ((cotangent i S)⟦(1 : ℤ)⟧)))
    (hα : IsIso (targetPushMap i S))
    (hid : IsIso (identityKernelMap Y K T G₀ U P I h₀ ht₀)) :
    DerivedCategory.Q.obj K ⟶
      (derivedTensorUncurried Y.left).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj ((cotangent i S)⟦(1 : ℤ)⟧)) := by
  letI := hid
  exact inv (identityKernelMap Y K T G₀ U P I h₀ ht₀) ≫
    kernelMap Y (universalClass i S A B hα) (DerivedCategory.Q.obj K) ≫
      diagonalTensorMap Y K ((cotangent i S)⟦(1 : ℤ)⟧) T G₁ P I h₁ ht₁

end MathlibExt.AlgebraicGeometry.StablePairFourierMukaiAtiyah
