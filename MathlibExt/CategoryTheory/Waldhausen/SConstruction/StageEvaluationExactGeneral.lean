/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenGeneral
public import MathlibExt.CategoryTheory.Waldhausen.ExactFunctor

/-!
# Exact evaluations of the named general finite-stage value

Each original interval evaluation preserves zero objects, genuine stage
cofibrations, pointwise weak equivalences and every pushout along a stage
cofibration. The actual whole stage pushout proves the last condition.
The same derived zero and Waldhausen values are installed only locally.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every original interval evaluation is Waldhausen exact for the actual
named stage value, with no caller stage or preservation witness. -/
theorem evalIsGeneralStageWaldhausenExact (n : ℕ) (x : Ar n) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n;
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n;
    (eval C n x).IsWaldhausenExact := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  refine {
    map_isZero := ?_
    map_cofibration := ?_
    map_weakEquivalence := ?_
    map_pushout := ?_ }
  · intro A hA
    let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
    exact ((evaluation (Ar n) C).obj x).map_isZero ((forget C n).map_isZero hA)
  · intro A B φ hφ
    have h := (isCofibration_generalStageWaldhausenCategory_iff C n φ).mp hφ
    exact Stage.app_isCofibration C φ h x
  · intro A B φ hφ
    have h := (isWeakEquivalence_generalStageWaldhausenCategory_iff C n φ).mp hφ
    exact ((mem_stageWeak (C := C) (n := n)).mp h) x
  · intro A B D P φ ψ inl inr hφ hP
    have h := (isCofibration_generalStageWaldhausenCategory_iff C n φ).mp hφ
    exact GeneralStagePushoutPresentation.isPushout_app h hP x

end CategoryTheory.Waldhausen.SConstruction
