/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.Comparison.ScalarExtension
public import MathlibExt.KTheory.Ring.StableGeneralLinear.MixedOriginalQLoopSquare

/-!
# Original mixed Q naturality on every canonical K0 component

The actual original scalar loop map is compared to original up, the actual
working scalar map and original down through their whole retained families.
Original component/evaluator laws, same-frame Q naturality and exact K0 maps
then give the fixed original RingK0 formula on every component. The six-role
transport data is retained alongside that intrinsic four-role formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] CategoryTheory.ExactCategory.waldhausenCategory
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_additive
attribute [local instance] AlgebraicKTheory.StableGL.nativeProjectiveZeroScalarFunctor_isExact

namespace AlgebraicKTheory.StableGL

open QuillenMixedUniverseTransport OriginalQuillenUnliftedTransport

private abbrev originalQExactComponentValue.{u, v}
    (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] [ExactCategory C] (c : ZerothHomotopy (NQKSpace C)) : K0 C :=
  WaldhausenKTheory.K0.toExact C (NQKSpacePiZeroEquivK0 C c)

/-- The fixed original RingK0 evaluator uses the SAME exact-Q component dictionary. -/
public def originalQProjectiveComponentsK0.{uR, uM}
    (R : Type uR) [Ring R] (c : ZerothHomotopy (NQKSpace (FGProjectiveCat.{max uR uM} R))) :
    RingK0 R :=
  RingK0.projectiveUniverseEquiv.{uR, uM} R
    (WaldhausenKTheory.K0.toExact (FGProjectiveCat.{max uR uM} R)
      (NQKSpacePiZeroEquivK0 (FGProjectiveCat.{max uR uM} R) c))

/-- Every original loop has the original canonical K0 value after its SAME point chart. -/
public theorem originalQProjectiveComponentsK0_loop.{uR, uM}
    (R : Type uR) [Ring R] (p : NQKSpace (FGProjectiveCat.{max uR uM} R)) :
    originalQProjectiveComponentsK0.{uR, uM} R (ZerothHomotopy.mk p) =
      RingK0.projectiveUniverseEquiv.{uR, uM} R
        (OriginalQK0Comparison.canonicalLoopComponentsK0 (C := FGProjectiveCat.{max uR uM} R)
          (ZerothHomotopy.mk (originalNQLoopPointHomeomorph (FGProjectiveCat.{max uR uM} R) p))) :=
  congrArg (RingK0.projectiveUniverseEquiv.{uR, uM} R)
    (originalNQLoopPointEvaluator (FGProjectiveCat.{max uR uM} R) p).symm

private theorem originalSameFrameExactQEvaluator.{u, v}
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] [ExactCategory C] [ExactCategory D]
    (F : C ⥤ D) [F.Additive] [F.IsExact] (c : ZerothHomotopy (NQKSpace C)) :
    originalQExactComponentValue D (mixedNQKSpacePiZeroMap F c) =
      K0.map F (originalQExactComponentValue C c) := by
  let X := ZerothHomotopy (NQKSpace C)
  let Y := ZerothHomotopy (NQKSpace D)
  let A : X →
      @WaldhausenKTheory.K0 C _ _ (CategoryTheory.ExactCategory.waldhausenCategory C) :=
    NQKSpacePiZeroEquivK0 C
  let B : Y →
      @WaldhausenKTheory.K0 D _ _ (CategoryTheory.ExactCategory.waldhausenCategory D) :=
    NQKSpacePiZeroEquivK0 D
  let TC := WaldhausenKTheory.K0.toExact C
  let TD := WaldhausenKTheory.K0.toExact D
  have hN : B (mixedNQKSpacePiZeroMap F c) = WaldhausenKTheory.K0.map F (A c) :=
    mixedNQKSpacePiZeroEvaluator_sameFrame F c
  have hT : TD (WaldhausenKTheory.K0.map F (A c)) = K0.map F (TC (A c)) :=
    DFunLike.congr_fun (WaldhausenKTheory.K0.toExact_naturality C (D := D) F) (A c)
  exact (congrArg TD hN).trans hT

private abbrev originalWorkingQUpR.{uR, uS, uMR, uMS, uNR, uNS}
    (R : Type uR) [Ring R] :=
  FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} R

private abbrev originalWorkingQUpS.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :=
  FGProjectiveCat.CategoryUniverseLift.upFunctor.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} S

private abbrev originalWorkingQDownS.{uR, uS, uMR, uMS, uNR, uNS}
    (S : Type uS) [Ring S] :=
  FGProjectiveCat.CategoryUniverseLift.downFunctor.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} S

private abbrev originalQUpMapR.{uR, uS, uMR, uMS, uNR, uNS} (R : Type uR) [Ring R] :=
  originalUnliftedNQup.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R

private abbrev originalQUpMapS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :=
  originalUnliftedNQup.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S

private abbrev originalQDownMapS.{uR, uS, uMR, uMS, uNR, uNS} (S : Type uS) [Ring S] :=
  originalUnliftedNQdown.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S

private def originalScalarDownWorkingUpIso.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    (originalWorkingQUpR.{uR, uS, uMR, uMS, uNR, uNS} R ⋙
        mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f) ⋙
      originalWorkingQDownS.{uR, uS, uMR, uMS, uNR, uNS} S ≅
        nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f := by
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  let U := originalWorkingQUpS.{uR, uS, uMR, uMS, uNR, uNS} S
  let E := FGProjectiveCat.CategoryUniverseLift.equivalence.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS} S
  exact Functor.isoWhiskerRight
    (mixedOriginalProjectiveLiftSquare.{uR, uS, uMR, uMS, uNR, uNS} f) E.inverse ≪≫
      Functor.associator F U E.inverse ≪≫
        Functor.isoWhiskerLeft F E.unitIso.symm ≪≫ Functor.rightUnitor F

private theorem originalScalarDownWorkingUpK0Value.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (a : K0 (FGProjectiveCat.{max uR uMR} R)) :
    K0.map (originalWorkingQDownS.{uR, uS, uMR, uMS, uNR, uNS} S)
        (K0.map (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
          (K0.map (originalWorkingQUpR.{uR, uS, uMR, uMS, uNR, uNS} R) a)) =
      K0.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) a := by
  let U := originalWorkingQUpR.{uR, uS, uMR, uMS, uNR, uNS} R
  let D := originalWorkingQDownS.{uR, uS, uMR, uMS, uNR, uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let F := nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f
  have hComp : K0.map ((U ⋙ W) ⋙ D) = (K0.map D).comp ((K0.map W).comp (K0.map U)) :=
    (K0.map_comp (U ⋙ W) D).trans
      (congrArg (fun m => (K0.map D).comp m) (K0.map_comp U W))
  have hIso : K0.map ((U ⋙ W) ⋙ D) = K0.map F :=
    K0.map_eq_of_iso (originalScalarDownWorkingUpIso.{uR, uS, uMR, uMS, uNR, uNS} f)
  exact DFunLike.congr_fun (hComp.symm.trans hIso) a

/-- The actual original scalar loop map has its six-role up/working/down transport family. -/
public def mixedOriginalQScalarLoopTransportHomotopy.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    ContinuousMap.Homotopy
      (mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))
      ((originalUnliftedNQdown.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          ((mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).comp
            (originalUnliftedNQup.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
              max (max uR uMR) (max uS uMS) uNR uNS, uNR} R))) := by
  let F := mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
  let W := mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
  let UR := originalQUpMapR.{uR, uS, uMR, uMS, uNR, uNS} R
  let US := originalQUpMapS.{uR, uS, uMR, uMS, uNR, uNS} S
  let DS := originalQDownMapS.{uR, uS, uMR, uMS, uNR, uNS} S
  let RS := originalUnliftedNQrightFamily.{uS, uMS,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
  let H0 := RS.toHomotopy.symm.compContinuousMap F
  let A : ContinuousMap.Homotopy F (DS.comp (US.comp F)) :=
    H0.cast (by apply ContinuousMap.ext; intro p; rfl)
      (by apply ContinuousMap.ext; intro p; rfl)
  let B := (ContinuousMap.Homotopy.refl DS).comp
    (mixedOriginalRetunedQUpLoopScalarSquare.{uR, uS, uMR, uMS, uNR, uNS} f).symm
  exact A.trans B

/-- EVERY component of the original scalar map has that actual six-role transport value. -/
public theorem mixedOriginalQScalarComponentTransport.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (c : ZerothHomotopy (NQKSpace (FGProjectiveCat.{max uR uMR} R))) :
    mixedNQKSpacePiZeroMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) c =
      originalUnliftedNQdownComponents.{uS, uMS,
        max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
        (mixedNQKSpacePiZeroMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
          (originalUnliftedNQupComponents.{uR, uMR,
            max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
            max (max uR uMR) (max uS uMS) uNR uNS, uNR} R c)) := by
  induction c using ZerothHomotopy.rec with
  | mk p =>
    let U := originalQUpMapR.{uR, uS, uMR, uMS, uNR, uNS} R
    have hU : originalUnliftedNQupComponents.{uR, uMR,
        max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNR} R (ZerothHomotopy.mk p) =
      ZerothHomotopy.mk (U p) := by
      rw [originalUnliftedNQupComponents_value]
      rfl
    rw [mixedNQKSpacePiZeroMap_mk, hU, mixedNQKSpacePiZeroMap_mk]
    rw [originalUnliftedNQdownComponents_value]
    change ZerothHomotopy.mk
        (mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) p) =
      ZerothHomotopy.mk
        (originalQDownMapS.{uR, uS, uMR, uMS, uNR, uNS} S
          (mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f) (U p)))
    exact ZerothHomotopy.sound
      ((mixedOriginalQScalarLoopTransportHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f).evalAt p)

private theorem originalWorkingScalarExactEvaluator.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S)
    (c : ZerothHomotopy (NQKSpace (FGProjectiveCat.{max uR uMR} R))) :
    originalQExactComponentValue (FGProjectiveCat.{max uS uMS} S)
      (originalUnliftedNQdownComponents.{uS, uMS,
        max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
        (mixedNQKSpacePiZeroMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
          (originalUnliftedNQupComponents.{uR, uMR,
            max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
            max (max uR uMR) (max uS uMS) uNR uNS, uNR} R c))) =
      K0.map (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f)
        (originalQExactComponentValue (FGProjectiveCat.{max uR uMR} R) c) := by
  let CR := FGProjectiveCat.{max uR uMR} R
  let CS := FGProjectiveCat.{max uS uMS} S
  let DR := mixedOriginalQWorkingCategoryR.{uR, uS, uMR, uMS, uNR, uNS} R
  let DS := mixedOriginalQWorkingCategoryS.{uR, uS, uMR, uMS, uNR, uNS} S
  let W := mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f
  let U := originalWorkingQUpR.{uR, uS, uMR, uMS, uNR, uNS} R
  let D := originalWorkingQDownS.{uR, uS, uMR, uMS, uNR, uNS} S
  let cU := originalUnliftedNQupComponents.{uR, uMR,
    max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
    max (max uR uMR) (max uS uMS) uNR uNS, uNR} R c
  let cW := mixedNQKSpacePiZeroMap W cU
  have hDown : originalQExactComponentValue CS
      (originalUnliftedNQdownComponents.{uS, uMS,
        max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S cW) =
      K0.map D (originalQExactComponentValue DS cW) :=
    originalUnliftedNQdownEvaluator.{uS, uMS,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNS} S cW
  have hW : originalQExactComponentValue DS cW = K0.map W (originalQExactComponentValue DR cU) :=
    originalSameFrameExactQEvaluator W cU
  have hUp : originalQExactComponentValue DR cU = K0.map U (originalQExactComponentValue CR c) :=
    originalUnliftedNQupEvaluator.{uR, uMR,
      max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
      max (max uR uMR) (max uS uMS) uNR uNS, uNR} R c
  exact hDown.trans ((congrArg (K0.map D) hW).trans
    ((congrArg (fun a => K0.map D (K0.map W a)) hUp).trans
      (originalScalarDownWorkingUpK0Value.{uR, uS, uMR, uMS, uNR, uNS} f
        (originalQExactComponentValue CR c))))

/-- Canonical EVERY-component K0 naturality is bundled with the ACTUAL six-role transport. -/
public theorem mixedOriginalQEveryComponentK0Naturality.{uR, uS, uMR, uMS, uNR, uNS}
    {R : Type uR} {S : Type uS} [Ring R] [Ring S] (f : R →+* S) :
    Nonempty (ContinuousMap.Homotopy
      (mixedNQKSpaceMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f))
      ((originalUnliftedNQdown.{uS, uMS, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
        max (max uR uMR) (max uS uMS) uNR uNS, uNS} S).comp
          ((mixedNQKSpaceMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)).comp
            (originalUnliftedNQup.{uR, uMR, max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
              max (max uR uMR) (max uS uMS) uNR uNS, uNR} R)))) ∧
    (∀ c : ZerothHomotopy (NQKSpace (FGProjectiveCat.{max uR uMR} R)),
      mixedNQKSpacePiZeroMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) c =
        originalUnliftedNQdownComponents.{uS, uMS,
          max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
          max (max uR uMR) (max uS uMS) uNR uNS, uNS} S
          (mixedNQKSpacePiZeroMap (mixedOriginalQWorkingFunctor.{uR, uS, uMR, uMS, uNR, uNS} f)
            (originalUnliftedNQupComponents.{uR, uMR,
              max (max uR uMR + 1) (max uS uMS + 1) uNR uNS,
              max (max uR uMR) (max uS uMS) uNR uNS, uNR} R c))) ∧
    ∀ c : ZerothHomotopy (NQKSpace (FGProjectiveCat.{max uR uMR} R)),
      originalQProjectiveComponentsK0.{uS, uMS} S
          (mixedNQKSpacePiZeroMap (nativeProjectiveZeroScalarFunctor.{uR, uS, uMR, uMS} f) c) =
        FGProjectiveCat.scalarExtensionK0.{uR, uS} f (originalQProjectiveComponentsK0.{uR, uMR} R c)
          := by
  refine ⟨⟨mixedOriginalQScalarLoopTransportHomotopy.{uR, uS, uMR, uMS, uNR, uNS} f⟩,
    (fun c => mixedOriginalQScalarComponentTransport.{uR, uS, uMR, uMS, uNR, uNS} f c), ?_⟩
  intro c
  have hTransport := mixedOriginalQScalarComponentTransport.{uR, uS, uMR, uMS, uNR, uNS} f c
  have hExact :=
    (congrArg (originalQExactComponentValue (FGProjectiveCat.{max uS uMS} S)) hTransport).trans
      (originalWorkingScalarExactEvaluator.{uR, uS, uMR, uMS, uNR, uNS} f c)
  have hChart := DFunLike.congr_fun
    (nativeProjectiveScalarOriginalK0MapChart.{uR, uS, uMR, uMS} f)
    (originalQExactComponentValue (FGProjectiveCat.{max uR uMR} R) c)
  exact (congrArg (RingK0.projectiveUniverseEquiv.{uS, uMS} S) hExact).trans hChart

end AlgebraicKTheory.StableGL

end
