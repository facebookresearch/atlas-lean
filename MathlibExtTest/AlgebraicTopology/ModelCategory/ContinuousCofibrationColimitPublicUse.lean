/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Authors: Tsutomu Okano <toskua@meta.com>
-/

import MathlibExt.AlgebraicTopology.ModelCategory.ContinuousCofibrationColimit

set_option autoImplicit false
noncomputable section
universe uC vC w

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace ContinuousCofibrationColimitNeutralPublicUse

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- An arbitrary model-category caller keeps its original continuous diagram and cocone. -/
theorem endpointCofibrant (F : J ⥤ C) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c) [IsCofibrant (F.obj ⊥)]
    (hF : ∀ j : J, ¬IsMax j → cofibrations C (F.map (homOfLE (Order.le_succ j)))) :
    IsCofibrant c.pt := continuousCofibrationColimit_cofibrant F c hc hF

/-- Its actual initial-to-endpoint map is a cofibration for the same given model. -/
example (F : J ⥤ C) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c) [IsCofibrant (F.obj ⊥)]
    (hF : ∀ j : J, ¬IsMax j → cofibrations C (F.map (homOfLE (Order.le_succ j)))) :
    cofibrations C (initial.to c.pt) := by
  let _ : IsCofibrant c.pt := endpointCofibrant F c hc hF
  exact (cofibration_iff (initial.to c.pt)).mp inferInstance

end ContinuousCofibrationColimitNeutralPublicUse
