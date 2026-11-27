/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenGluing

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace MathlibExtTest.StageWaldhausenGluing
open CategoryTheory.Waldhausen.SConstruction
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every original finite stage inherits gluing from the base gluing axiom. -/
theorem originalStageGluing (hGlue : WaldhausenGluingAxiom (C := C)) (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    WaldhausenGluingAxiom (C := Stage C n) := generalStageWaldhausenGluingAxiom C hGlue n

end MathlibExtTest.StageWaldhausenGluing
