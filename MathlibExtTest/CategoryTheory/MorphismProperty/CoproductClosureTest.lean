/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
-- Original coproduct maps, cells and native colimit-cocone closure.
import MathlibExt.CategoryTheory.MorphismProperty.CoproductClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe w v u
open CategoryTheory CategoryTheory.Limits

namespace OriginalCoproductClosureTest

variable {C : Type u} [Category.{v} C]

/-- Original component membership closes the SAME actual Sigma.map at arbitrary original index. -/
theorem same_original_sigma_map
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    [P.IsStableUnderTransfiniteComposition.{w}]
    {ι : Type w} [HasColimitsOfShape (Discrete ι) C] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, P (f i)) : P (Limits.Sigma.map f) :=
  P.coproductMap_mem_of_cobase_transfinite f hf

/-- Empty original labels produce the actual nullary map without a hidden component premise. -/
theorem empty_original_sigma_map
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    [P.IsStableUnderTransfiniteComposition.{w}]
    [HasColimitsOfShape (Discrete PEmpty.{w+1}) C]
    {A B : PEmpty.{w+1} → C} (f : ∀ i, A i ⟶ B i) :
    P (Limits.Sigma.map f) :=
  P.coproductMap_mem_of_cobase_transfinite f (fun i => PEmpty.elim i)

/-- The original i-cell uses its exact displayed pushout.flip and original component. -/
theorem original_i_cell_membership
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    {ι : Type w} [LinearOrder ι] [SuccOrder (MorphismProperty.CoproductCells.cellOrder ι)]
    [HasColimitsOfShape (Discrete ι) C] {A B : ι → C}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, P (f i)) (i : ι) :
    P ((MorphismProperty.CoproductCells.cellDiagram f).map
      (homOfLE (Order.le_succ (MorphismProperty.CoproductCells.cellIndex i)))) :=
  P.of_isPushout (MorphismProperty.CoproductCells.cell_isPushout f i).flip (hf i)

/-- The same actual raw diagram and whole initial/final equation keep their IsColimit data. -/
theorem same_phi_and_actual_colimit
    {ι : Type w} [LinearOrder ι] [WellFoundedLT ι]
    [SuccOrder (MorphismProperty.CoproductCells.cellOrder ι)]
    [HasColimitsOfShape (Discrete ι) C] {A B : ι → C} (f : ∀ i, A i ⟶ B i) :
    (MorphismProperty.CoproductCells.coproductMapOriginalCells f).isoBot.inv ≫
        (MorphismProperty.CoproductCells.coproductMapOriginalCells f).incl.app ⊥ =
      Limits.Sigma.map f ∧
    Nonempty (IsColimit (Cocone.mk (∐ B)
      (MorphismProperty.CoproductCells.coproductMapOriginalCells f).incl)) :=
  ⟨MorphismProperty.CoproductCells.coproductMapOriginalCells_fac f,
    ⟨MorphismProperty.CoproductCells.coproductMapOriginalCellsIsColimit f⟩⟩

/-- The new class remains the native all-original-colimit-cocone coproduct closure. -/
theorem genuine_native_coproduct_class
    (P : MorphismProperty C) [P.IsStableUnderCobaseChange]
    [P.IsStableUnderTransfiniteComposition.{w}] [HasCoproducts.{w} C] :
    P.IsStableUnderCoproducts.{w} :=
  P.isStableUnderCoproducts_of_cobase_transfinite

end OriginalCoproductClosureTest
