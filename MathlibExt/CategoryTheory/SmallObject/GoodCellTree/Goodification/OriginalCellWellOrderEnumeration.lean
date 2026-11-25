/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.Order.Extension.Well
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Original well-order enumeration and actual lower prefixes

The well-order extends the original well-founded cell order. All prefixes
are actual original lower sets, the next difference is exactly the original
next cell, and the prefix union exhausts the same original whole carrier.
No bound on that carrier or on the enumeration length is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w

namespace CategoryTheory.SmallObject.OriginalCellWellOrderEnumeration

variable {P : Type w} [PartialOrder P] [WellFoundedLT P]

/-- The actual original-label well-order carrier. -/
abbrev Index := WellOrderExtension P

/-- The complete original-label bijection to its actual well-order enumeration. -/
abbrev labels : P ≃ Index (P := P) := toWellOrderExtension

/-- The original before-prefix is lower for the original cell order. -/
def before (a : Index (P := P)) : LowerSet P where
  carrier := {p | labels p < a}
  lower' := by
    intro p q h hq
    exact (toWellOrderExtension_strictMono.monotone h).trans_lt hq

/-- The original after-prefix adds precisely the next original cell. -/
def after (a : Index (P := P)) : LowerSet P where
  carrier := {p | labels p ≤ a}
  lower' := by
    intro p q h hq
    exact (toWellOrderExtension_strictMono.monotone h).trans hq

/-- Every original before-prefix cell is retained in its actual after-prefix. -/
theorem before_le_after (a : Index (P := P)) : before a ≤ after a := by
  intro p h
  change labels p < a at h
  change labels p ≤ a
  exact h.le

/-- The actual prefix difference is exactly the next original label, rather than another carrier. -/
theorem mem_after_iff (a : Index (P := P)) (p : P) :
    p ∈ after a ↔ p ∈ before a ∨ p = labels.symm a := by
  change labels p ≤ a ↔ labels p < a ∨ p = labels.symm a
  rw [le_iff_lt_or_eq]
  rw [← Equiv.eq_symm_apply]

/-- Every original strict predecessor is already in the actual before-prefix. -/
theorem original_predecessor_before (p q : P) (h : q < p) :
    q ∈ before (labels p) := toWellOrderExtension_strictMono h

/-- The before-prefix is the actual union of all earlier original after-prefixes. -/
theorem before_union_after (a : Index (P := P)) :
    before a = ⨆ b : Set.Iio a, after b.1 := by
  ext p
  simp only [SetLike.mem_coe, LowerSet.mem_iSup_iff]
  change labels p < a ↔ ∃ b : Set.Iio a, labels p ≤ b.1
  constructor
  · intro hp
    exact ⟨⟨labels p, hp⟩, le_rfl⟩
  · rintro ⟨b, hp⟩
    exact hp.trans_lt b.2

/-- The actual original prefix family covers every original cell label. -/
theorem after_exhausts : (⨆ a : Index (P := P), after a) = ⊤ := by
  apply le_antisymm le_top
  intro p _
  apply LowerSet.mem_iSup_iff.2
  refine ⟨labels p, ?_⟩
  change labels p ≤ labels p
  exact le_rfl

/-- The actual enumeration's strict order is well founded. -/
theorem enumeration_wellFounded :
    WellFounded ((· < ·) : Index (P := P) → Index (P := P) → Prop) := by
  change WellFounded (WellFounded.wellOrderExtension ((· < ·) : P → P → Prop)).lt
  infer_instance

end CategoryTheory.SmallObject.OriginalCellWellOrderEnumeration
