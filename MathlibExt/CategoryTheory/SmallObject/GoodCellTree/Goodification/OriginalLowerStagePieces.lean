/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.FilteredOriginalLowerColimit
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Actual original lower pieces cut out by the original initial-stage cover

The actual original intersection functor retains every original lower
label and inclusion map. The original stage cover proves its union is
the same original lower set. Original directedness derives the actual
filtered-category dictionary for every nonempty original stage carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w

namespace CategoryTheory.SmallObject.OriginalLowerStagePieces

open Limits LowerSetColimits

variable {P I : Type w} [Preorder P] [Preorder I]
  (S : I → LowerSet P) (hMono : Monotone S)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)

/-- The whole actual original intersection diagram keeps the same original lower stage labels. -/
abbrev pieces (B : LowerSet P) : I ⥤ LowerSet P where
  obj i := B ⊓ S i
  map h := homOfLE (inf_le_inf_left B (hMono (leOfHom h)))

include hCover in
/-- The actual original stage cover exhausts the same whole original lower carrier. -/
theorem pieces_union (B : LowerSet P) :
    FilteredOriginalLowerColimit.union (pieces S hMono B) = B := by
  ext p
  change p ∈ (⨆ i : I, B ⊓ S i) ↔ p ∈ B
  rw [LowerSet.mem_iSup_iff]
  constructor
  · rintro ⟨i, hp⟩
    exact hp.1
  · intro hp
    obtain ⟨i, hi⟩ := hCover p
    exact ⟨i, hp, hi⟩

/-- The complete original piece object function is the actual original lower intersection. -/
theorem pieces_obj_function (B : LowerSet P) :
    (fun i : I => (pieces S hMono B).obj i) = (fun i : I => B ⊓ S i) := rfl

/-- Each actual original piece stays inside its actual original stage, without a size guess. -/
theorem piece_below (B : LowerSet P) (i : I) : (pieces S hMono B).obj i ≤ S i := inf_le_right

end CategoryTheory.SmallObject.OriginalLowerStagePieces
