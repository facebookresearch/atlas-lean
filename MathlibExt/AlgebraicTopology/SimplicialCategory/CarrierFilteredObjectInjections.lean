/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierColimitCocone
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerCofibrationObjectMonicity
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Original filtered object-colimit labels remain injective under the SAME C0 maps

The complete original Type-colimit equality criterion places an actual
equal-object equation in one later original stage. Genuine original
C0 injectivity then reflects that SAME equation to the original objects.
No object quotient or monicity certificate is substituted.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierColimit

variable {J : Type u} [Category.{u} J] [IsFiltered J] (F : J ⥤ Carrier.{u})

/-- The SAME original stage object labels inject into the genuine filtered object colimit. -/
theorem label_injective
    (h : ∀ {j k : J} (f : j ⟶ k), Function.Injective (F.map f).obj) (j : J) :
    Function.Injective (CarrierLabelDiagram.label F (labelCocone F) j) := by
  intro x y he
  have hh : (colimit.ι (F ⋙ forgetObjects) j) x = (colimit.ι (F ⋙ forgetObjects) j) y := he
  obtain ⟨k, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (colimit.isColimit (F ⋙ forgetObjects)) x y).mp hh
  exact h f hf

/-- Actual original C0 stage maps retain every original object injectively in the SAME filtered colimit. -/
theorem label_injective_of_cofibrations
    (h : ∀ {j k : J} (f : j ⟶ k), Bergner.cofibrations (F.map f)) (j : J) :
    Function.Injective (CarrierLabelDiagram.label F (labelCocone F) j) :=
  label_injective F (fun f => Bergner.cofibration_objects_injective (F.map f) (h f)) j

end CategoryTheory.SimplicialEnrichment.CarrierColimit
