/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.KTheory.Exact.Quillen.UniverseLift

noncomputable section

open CategoryTheory AlgebraicKTheory AlgebraicKTheory.QuillenUniverseLift
open scoped ContinuousMap Topology

universe uR uM uObj uHom uNative

variable (R : Type uR) [Ring R]

namespace QuillenUniverseLiftTests

/-- The Q objects retain the independently selected category object universe. -/
def actualLargeQCarrier : Type (max (max uR uM + 1) uObj) :=
  QuillenQ (liftedCategory.{uR, uM, uObj, uHom} R)

/-- The raw native loops retain the category object/Hom and independent native maxima. -/
def actualNativeLoopCarrier : Type
    (max (max (max (max uR uM + 1) uObj) (max (max uR uM) uHom)) uNative) :=
  nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R

/-- The forward functor is the actual original additive exact object/Hom inclusion. -/
theorem actualQUpFunctor :
    qUpFunctor.{uR, uM, uObj, uHom} R =
      QuillenQ.map
        (FGProjectiveCat.CategoryUniverseLift.upFunctor.{uR, uM, uObj, uHom} R) :=
  qUpFunctor_eq_map.{uR, uM, uObj, uHom} R

/-- The inverse functor is the actual original additive exact object/Hom projection. -/
theorem actualQDownFunctor :
    qDownFunctor.{uR, uM, uObj, uHom} R =
      QuillenQ.map
        (FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R) :=
  qDownFunctor_eq_map.{uR, uM, uObj, uHom} R

/-- Every native loop value descends to its same original carrier value. -/
theorem actualCarrierProjection
    (gamma : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) (t : unitInterval) :
    rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma t = (gamma t).down :=
  rawNativeCarrierDown_apply.{uR, uM, uObj, uHom, uNative} R gamma t

/-- The literal original maps have both inverse families fixed at their actual constant loops. -/
theorem actualMapsAndBothConstantFamilies :
    ∃ f : C(nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R, canonicalLoops.{uR, uM} R),
      ∃ g : C(canonicalLoops.{uR, uM} R, nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R),
        f = Qdown.{uR, uM, uObj, uHom, uNative} R ∧
        g = Qup.{uR, uM, uObj, uHom, uNative} R ∧
        f (nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R) = canonicalConstantLoop.{uR, uM} R ∧
        g (canonicalConstantLoop.{uR, uM} R) = nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R ∧
        ∃ L : ContinuousMap.HomotopyRel (g.comp f)
          (ContinuousMap.id (nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R))
          {nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R},
          ∃ T : ContinuousMap.HomotopyRel (f.comp g)
            (ContinuousMap.id (canonicalLoops.{uR, uM} R)) {canonicalConstantLoop.{uR, uM} R},
            ∀ t : unitInterval,
              L (t, nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R) =
                nativeConstantLoop.{uR, uM, uObj, uHom, uNative} R ∧
              T (t, canonicalConstantLoop.{uR, uM} R) = canonicalConstantLoop.{uR, uM} R := by
  let L := QleftHomotopyRel.{uR, uM, uObj, uHom, uNative} R
  let T := QrightHomotopyRel.{uR, uM, uObj, uHom, uNative} R
  refine ⟨Qdown.{uR, uM, uObj, uHom, uNative} R,
    Qup.{uR, uM, uObj, uHom, uNative} R, rfl, rfl,
    Qdown_constant.{uR, uM, uObj, uHom, uNative} R,
    Qup_constant.{uR, uM, uObj, uHom, uNative} R, L, T, ?_⟩
  intro t
  exact ⟨L.eq_snd t (Set.mem_singleton _), T.eq_snd t (Set.mem_singleton _)⟩

/-- Retuning retains the actual original Q functor and canonical zero-path action on every component. -/
theorem actualAllLoopComponentAction
    (gamma : nativeRawLoopSpace.{uR, uM, uObj, uHom, uNative} R) :
    ZerothHomotopy.mk (Qdown.{uR, uM, uObj, uHom, uNative} R gamma) =
      ZerothHomotopy.mk ((qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap
        (rawNativeCarrierDown.{uR, uM, uObj, uHom, uNative} R gamma)) :=
  Qdown_components.{uR, uM, uObj, uHom, uNative} R gamma

/-- The actual Q functor and its canonical zero path retain the original
mono-forward/epi-reversed generator and the same descended projective. -/
theorem actualGeneratorAction (X : liftedCategory.{uR, uM, uObj, uHom} R) :
    Path.Homotopic
      ((qDownWeaklyPointed.{uR, uM, uObj, uHom} R).loopMap
        (OriginalQK0Comparison.generatorLoop X))
      (OriginalQK0Comparison.generatorLoop
        ((FGProjectiveCat.CategoryUniverseLift.downFunctor.{uR, uM, uObj, uHom} R).obj X)) :=
  qDownWeaklyPointed_generator.{uR, uM, uObj, uHom} R X

end QuillenUniverseLiftTests

end
