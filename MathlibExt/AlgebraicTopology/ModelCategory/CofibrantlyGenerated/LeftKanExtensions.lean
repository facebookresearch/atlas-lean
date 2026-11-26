/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Original left Kan existence from actual generation data

Every colimit shape is the original costructured-arrow category.
The native essentially-small instance and actual generation-data colimits
give the native pointwise Kan construction on every original functor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe w uD vD uE vE uM vM
open CategoryTheory Limits

namespace HomotopicalAlgebra.CofibrantGenerationData

variable {M : Type uM} [Category.{vM} M] [ModelCategory M]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {E : Type uE} [Category.{vE} E] [LocallySmall.{w} E]

/-- Actual generation data supply every original comma colimit for the native pointwise Kan law. -/
theorem hasPointwiseLeftKanExtension (dM : CofibrantGenerationData M κ)
    (u : D ⥤ E) (F : D ⥤ M) : u.HasPointwiseLeftKanExtension F := by
  intro e
  let _ : HasColimitsOfShape (CostructuredArrow u e) M := dM.hasColimitsOfShape
  infer_instance

/-- The same original data yield the native left Kan existence interface. -/
theorem hasLeftKanExtension (dM : CofibrantGenerationData M κ)
    (u : D ⥤ E) (F : D ⥤ M) : u.HasLeftKanExtension F := by
  let _ : u.HasPointwiseLeftKanExtension F := dM.hasPointwiseLeftKanExtension u F
  infer_instance

end HomotopicalAlgebra.CofibrantGenerationData
