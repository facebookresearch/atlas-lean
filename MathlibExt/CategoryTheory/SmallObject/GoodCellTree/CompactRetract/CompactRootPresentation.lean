/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.CompactRetract.CompactRootUnderPresentability

/-!
# The actual original root arrow's same-rank compact presentation

The original coefficient LP and genuinely compact fixed root construct
a complete filtered presentation of the actual root arrow. Every right
root-piece end is genuinely compact in the coefficient at the same chi.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w u v

namespace CategoryTheory.SmallObject.CompactRootPresentation

open Limits

variable {C : Type u} [Category.{v} C] (D : C)
  (chi : Cardinal.{w}) [Fact chi.IsRegular] [IsCardinalLocallyPresentable C chi]
  [IsCardinalPresentable D chi]

/-- Coefficient LP constructs the whole original root-arrow presentation at the same rank. -/
theorem existsPresentation {X : C} (u : D ⟶ X) :
    ∃ (J : Type w) (_ : SmallCategory J) (_ : IsCardinalFiltered J chi),
      ∃ p : ColimitPresentation J (Under.mk u),
        ∀ j, IsCardinalPresentable (p.diag.obj j).right chi := by
  let : IsCardinalLocallyPresentable (Under D) chi :=
    CompactRootUnderPresentability.cardinalLocallyPresentable D chi
  obtain ⟨Q, _, hQ⟩ := HasCardinalFilteredGenerator.exists_generator (Under D) chi
  obtain ⟨J, jCategory, jFiltered, ⟨p⟩⟩ := hQ.exists_colimitsOfShape (Under.mk u)
  refine ⟨J, jCategory, jFiltered, p.toColimitPresentation, ?_⟩
  intro j
  let : IsCardinalPresentable (p.diag.obj j) chi :=
    hQ.le_isCardinalPresentable _ (p.prop_diag_obj j)
  exact CompactRootUnderPresentability.rightPresentable D chi (p.diag.obj j)

end CategoryTheory.SmallObject.CompactRootPresentation
