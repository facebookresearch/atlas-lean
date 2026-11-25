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

import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Cofibrant colimits of continuous cofibration diagrams

The original model-category theorem is retained from the native continuous
source construction, with its arbitrary category, original ordinal, bottom,
actual cocone and successor cofibration hypotheses.
-/

set_option autoImplicit false
noncomputable section
universe u v w uC vC

namespace HomotopicalAlgebra

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- The actual caller colimit is cofibrant for a genuine continuous cofibration
diagram with cofibrant bottom, retaining all original maps and the colimit cocone. -/
theorem continuousCofibrationColimit_cofibrant (F : J ⥤ C) [F.IsWellOrderContinuous]
    (c : Cocone F) (hc : IsColimit c) [IsCofibrant (F.obj ⊥)]
    (hF : ∀ j : J, ¬IsMax j → cofibrations C (F.map (homOfLE (Order.le_succ j)))) :
    IsCofibrant c.pt := by
  let : (cofibrations C).IsStableUnderTransfiniteComposition.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  have hEndpoint : cofibrations C (c.ι.app ⊥) := by
    apply IsStableUnderTransfiniteCompositionOfShape.le
    exact ⟨{
      F := F
      isoBot := Iso.refl (F.obj ⊥)
      incl := c.ι
      isColimit := hc
      map_mem := hF
      fac := Category.id_comp _ }⟩
  let : Cofibration (c.ι.app ⊥) := (cofibration_iff _).mpr hEndpoint
  exact isCofibrant_of_cofibration (c.ι.app ⊥)

end HomotopicalAlgebra
