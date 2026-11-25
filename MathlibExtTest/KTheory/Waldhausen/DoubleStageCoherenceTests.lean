/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.DoubleStageCoherence

public section
set_option autoImplicit false
noncomputable section

universe uC vC

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

namespace MathlibExtTest.DoubleStageCoherence

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original double identity remains the whole identity functor. -/
theorem originalDoubleIdentity (m n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    mapDoubleStage (Functor.IsWaldhausenExact.id (C := C)) m n =
      𝟭 (Stage (Stage C n) m) :=
  mapDoubleStage_id m n

end MathlibExtTest.DoubleStageCoherence
