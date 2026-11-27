/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.CoherentRetracts.Absorption
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Order.SuccPred.Limit

/-!
# Coherent retracts at the genuine limit stage of `WithTop ℕ`

The index is `J = WithTop ℕ`, whose top element `⊤` is a successor limit. The original diagram
is the constant functor at `Bool`. Each successor map `𝟙 Bool` is a retract of the cell
`Bool → Bool × Bool`, `b ↦ (b, false)`, which is not an epimorphism. The morphism class
contains only maps isomorphic, as arrows, to this cell.

The clients check:
* the constant diagram is well-order continuous;
* every successor map lies in `cellClass.retracts`;
* the glued diagram `PrefixSplitGlue.wholeDiagram`, built from `coherentPrefixSection`, has a
  colimit target cocone at the limit stage `⊤`;
* the source functor of the glued diagram is the original diagram.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject.CoherentRetracts

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

@[expose] public section

namespace MathlibExtTest.CategoryTheory.SmallObject.CoherentRetractsGenuineLimit

/-- The index `WithTop ℕ`. -/
abbrev J := WithTop ℕ

example : WellFoundedLT J := inferInstance
example : SuccOrder J := inferInstance

/-- The top stage is a successor limit. -/
example : Order.IsSuccLimit (⊤ : J) := WithTop.isSuccLimit_top

/-- The cell `b ↦ (b, false)`. -/
def cell : Bool ⟶ Bool × Bool := ↾fun bit => (bit, false)

/-- The first projection. -/
def projection : Bool × Bool ⟶ Bool := ↾Prod.fst

/-- The identity of `Bool` is a retract of the cell. -/
def actualStageRetract : RetractArrow (𝟙 Bool) cell where
  i := Arrow.homMk (𝟙 Bool) cell (by rfl)
  r := Arrow.homMk (𝟙 Bool) projection (by rfl)
  retract := by ext <;> rfl

/-- The class of maps isomorphic, as arrows, to the cell. -/
def cellClass : MorphismProperty (Type) :=
  fun _ _ map => Nonempty (Arrow.mk map ≅ Arrow.mk cell)

/-- The constant diagram at `Bool`. -/
abbrev original : J ⥤ (Type) := (Functor.const J).obj Bool

/-- The cell is not an epimorphism. -/
theorem cell_not_epi : ¬ Epi cell := by
  intro hEpi
  obtain ⟨bit, hBit⟩ := (epi_iff_surjective cell).1 hEpi (false, true)
  have hFalseTrue : false = true := congrArg Prod.snd hBit
  cases hFalseTrue

instance original_continuous : original.IsWellOrderContinuous where
  nonempty_isColimit point hLimit := by
    let bottomIndex : Set.Iio point := ⟨⊥, Order.IsSuccLimit.bot_lt hLimit⟩
    refine ⟨{ desc := fun cocone => cocone.ι.app bottomIndex
              fac := ?_
              uniq := ?_ }⟩
    · intro cocone index
      change (𝟙 Bool) ≫ cocone.ι.app bottomIndex = cocone.ι.app index
      rw [Category.id_comp]
      have hNatural := cocone.w (homOfLE
        (show bottomIndex ≤ index from (show (⊥ : J) ≤ index.1 from bot_le)))
      change (𝟙 Bool) ≫ cocone.ι.app index = cocone.ι.app bottomIndex at hNatural
      simpa only [Category.id_comp] using hNatural.symm
    · intro cocone map hMap
      have hBottom := hMap bottomIndex
      change (𝟙 Bool) ≫ map = cocone.ι.app bottomIndex at hBottom
      simpa only [Category.id_comp] using hBottom

/-- Every successor map of the original diagram is a retract of a map in the class. -/
theorem original_successors (index : J) (_hNotMax : ¬ IsMax index) :
    cellClass.retracts (original.map (homOfLE (Order.le_succ index))) :=
  ⟨Bool, Bool × Bool, cell, actualStageRetract, ⟨Iso.refl _⟩⟩

/-- The glued split diagram over `J`. -/
def assembled : J ⥤ SplitObject (Type) :=
  PrefixSplitGlue.wholeDiagram cellClass original
    (coherentPrefixSection cellClass original original_successors)

/-- The target cocone of the glued diagram at the limit stage `⊤` is a colimit. -/
theorem assembled_actual_limit :
    Nonempty (IsColimit ((Set.principalSegIio (⊤ : J)).cocone
      (assembled ⋙ SplitObject.targetFunctor))) :=
  PrefixSplitGlue.wholeDiagram_continuous cellClass original
    (coherentPrefixSection cellClass original original_successors) (⊤ : J)
    WithTop.isSuccLimit_top

/-- The source functor of the glued diagram is the original diagram. -/
theorem assembled_original_source : assembled ⋙ SplitObject.sourceFunctor = original :=
  PrefixSplitGlue.wholeDiagram_source cellClass original
    (coherentPrefixSection cellClass original original_successors)

#print axioms assembled_actual_limit
#print axioms assembled_original_source

end MathlibExtTest.CategoryTheory.SmallObject.CoherentRetractsGenuineLimit

end
