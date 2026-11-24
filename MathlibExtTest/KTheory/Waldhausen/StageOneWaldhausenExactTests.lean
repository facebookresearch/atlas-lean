/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWaldhausenExact

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.StageOneWaldhausenExact

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Original S1 evaluation is exact for the actual general Waldhausen value. -/
theorem originalEvaluationExact :
    letI : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
    letI : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
    (stageOneEval C).IsWaldhausenExact := stageOneEval_general_isWaldhausenExact C

/-- The actual unique interval component detects original S1 cofibrations. -/
theorem originalDegreeOneCofibration {A B : Stage C 1} (f : A ⟶ B) :
    stageCofibrations C 1 f ↔ IsCofibration (f.hom.app (interval (0 : Fin 2) 1 (by decide))) :=
  stageCofibrations_one_iff C f

end MathlibExtTest.StageOneWaldhausenExact
