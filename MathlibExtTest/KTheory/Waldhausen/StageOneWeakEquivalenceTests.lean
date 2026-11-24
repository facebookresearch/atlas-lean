/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneWeakEquivalence

public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.StageOneWeakEquivalence

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The genuine original weak S1 equivalence uses insertion and evaluation. -/
def originalWeakDegreeOneEquivalence : CategoryTheory.Waldhausen.WeakCategory C ≌ StageWeakCategory C 1 :=
  stageOneGeneralWeakEquivalence C

end MathlibExtTest.StageOneWeakEquivalence
