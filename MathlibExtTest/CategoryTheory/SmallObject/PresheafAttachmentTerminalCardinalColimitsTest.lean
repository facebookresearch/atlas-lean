/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentTerminalCardinalColimits

/-! Original terminal cocones and both prescribed cell equations. -/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w s v v'
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.SmallObject.PresheafAttachmentTerminalCardinalColimitsTest
section Preservation
variable {D : Type w} [SmallCategory D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)
    (μ : Cardinal.{max u w}) [Fact μ.IsRegular]
    [∀ i, Mono (j i)] [∀ i, IsCardinalPresentable.{max u w} (A i) μ]

/-- The original supplied cocone is preserved by the actual terminal composite. -/
def original_supplied_cocone
    {J : Type v} [Category.{v'} J] [EssentiallySmall.{max u w} J] [IsCardinalFiltered J μ]
    {F : J ⥤ Dᵒᵖ ⥤ Type (max u w)} {c : Cocone F} (hc : IsColimit c) :
    IsColimit (((terminal.arrowFunctor (Dᵒᵖ ⥤ Type (max u w)) ⋙
      SmallObject.functor j) ⋙ Arrow.leftFunc).mapCocone c) := by
  let K := (terminal.arrowFunctor (Dᵒᵖ ⥤ Type (max u w)) ⋙
    SmallObject.functor j) ⋙ Arrow.leftFunc
  let _ : K.IsCardinalAccessible μ := presheafAttachment_terminal_isCardinalAccessible j μ
  let _ : PreservesColimitsOfShape J K :=
    Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall K μ J
  exact isColimitOfPreserves K hc

end Preservation

section OriginalEquations
variable {D : Type w} [SmallCategory D] {I : Type s}
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)

/-- Original bottom maps in every attaching square remain the chosen terminal maps. -/
theorem original_bottom_map {X : Dᵒᵖ ⥤ Type (max u w)}
    (q : FunctorObjIndex j (terminal.from X)) : q.b = terminal.from (B q.i) :=
  terminalIsTerminal.hom_ext _ _

variable [Small.{max u w} I]

/-- Both prescribed cell equations remain for the original terminal square. -/
theorem original_unit_cell_equations {X : Dᵒᵖ ⥤ Type (max u w)}
    (q : FunctorObjIndex j (terminal.from X)) :
    j q.i ≫ Sigma.ι (functorObjTgtFamily j (terminal.from X)) q ≫
        ρFunctorObj j (terminal.from X) = q.t ≫ ιFunctorObj j (terminal.from X) ∧
    (Sigma.ι (functorObjTgtFamily j (terminal.from X)) q ≫
      ρFunctorObj j (terminal.from X)) ≫ πFunctorObj j (terminal.from X) =
        terminal.from (B q.i) := by
  refine ⟨presheafAttachmentEquiv_cell_boundary j (terminal.from X) q, ?_⟩
  exact (presheafAttachmentEquiv_cell_projection j (terminal.from X) q).trans
    (terminalIsTerminal.hom_ext _ _)

end OriginalEquations
end CategoryTheory.SmallObject.PresheafAttachmentTerminalCardinalColimitsTest
