/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.PresheafAttachmentCardinality

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u w v s
open CategoryTheory CategoryTheory.Limits Cardinal Opposite
namespace CategoryTheory.SmallObject.TerminalAttachmentCardinalityTest
variable {D : Type w} [Category.{v} D] {I : Type s} [Small.{max u w} I]
    {A B : I → Dᵒᵖ ⥤ Type (max u w)} (j : ∀ i, A i ⟶ B i)
    (X : Dᵒᵖ ⥤ Type (max u w))
    [HasColimitsOfShape (Discrete (FunctorObjIndex j (terminal.from X)))
      (Dᵒᵖ ⥤ Type (max u w))]
    [HasPushout (functorObjTop j (terminal.from X)) (functorObjLeft j (terminal.from X))]

/-- The original whole label retains its prescribed top attaching map. -/
theorem original_cell_boundary (q : FunctorObjIndex j (terminal.from X)) :
    j q.i ≫ Sigma.ι (functorObjTgtFamily j (terminal.from X)) q ≫
        ρFunctorObj j (terminal.from X) = q.t ≫ ιFunctorObj j (terminal.from X) := q.comm

/-- The original cell's bottom is recovered exactly by the actual right factor. -/
theorem original_cell_projection (q : FunctorObjIndex j (terminal.from X)) :
    (Sigma.ι (functorObjTgtFamily j (terminal.from X)) q ≫ ρFunctorObj j (terminal.from X)) ≫
      πFunctorObj j (terminal.from X) = q.b := by simp [π'FunctorObj]

omit [Small.{max u w} I] in
/-- The actual unit and right factor retain the original terminal arrow. -/
theorem original_unit_projection :
    ιFunctorObj j (terminal.from X) ≫ πFunctorObj j (terminal.from X) = terminal.from X :=
  ιFunctorObj_πFunctorObj j (terminal.from X)

/-- Fixed endpoints/index, varying original X: the size result consumes no Mono data. -/
theorem original_size (ξ : Cardinal.{max u w}) (hξ : ℵ₀ ≤ ξ)
    (hI : Cardinal.mk (Shrink.{max u w} I) ≤ ξ)
    (hA : ∀ i, Cardinal.mk (A i).Elements ≤ ξ)
    (hB : ∀ i, Cardinal.mk (B i).Elements ≤ ξ)
    (hX : Cardinal.mk X.Elements ≤ 2 ^ ξ) :
    Cardinal.mk (functorObj j (terminal.from X)).Elements ≤ 2 ^ ξ :=
  presheafAttachment_terminal_mk_elements_le j X ξ hξ hI hA hB hX

end CategoryTheory.SmallObject.TerminalAttachmentCardinalityTest
