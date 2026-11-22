/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellWellOrderEnumeration
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.GoodCellExtensionOrder

/-!
# Actual original one-cell carrier bijections

The constructed old/new cell carrier is bijective to the original label
subset with exactly the original next label adjoined. Both old and new
label functions are literal. The well-order prefix instance records the
same original before/after carriers used by the transfinite construction.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w

namespace CategoryTheory.SmallObject.CellTreeLabelAdjoin

open GoodCellExtensionOrder

section ActualLabels

variable {P : Type w} (S : Set P) (a : P)

/-- The original old label or original newly adjoined label in the actual enlarged subset. -/
def toInsert (x : Index S) : (insert a S : Set P) :=
  match x.val with
  | some p => ⟨p.1, Or.inr p.2⟩
  | none => ⟨a, Or.inl rfl⟩

/-- Distinct actual old/new occurrences have distinct original labels. -/
theorem toInsert_injective (ha : a ∉ S) : Function.Injective (toInsert S a) := by
  rintro ⟨x⟩ ⟨y⟩ h
  have hv := congrArg Subtype.val h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y =>
      have hy : a = y.1 := hv
      exact False.elim (ha (hy ▸ y.2))
  | some x =>
    cases y with
    | none =>
      have hx : x.1 = a := hv
      exact False.elim (ha (hx ▸ x.2))
    | some y =>
      have hxy : x = y := Subtype.ext hv
      subst y
      rfl

/-- Every original enlarged-subset label is represented by its actual old/new occurrence. -/
theorem toInsert_surjective : Function.Surjective (toInsert S a) := by
  rintro ⟨p, hp⟩
  rcases hp with hpa | hp
  · refine ⟨Index.new, ?_⟩
    exact Subtype.ext hpa.symm
  · refine ⟨Index.old ⟨p, hp⟩, ?_⟩
    rfl

/-- The complete actual original-label equivalence for the constructed one-cell carrier. -/
def adjoinEquiv (ha : a ∉ S) : Index S ≃ (insert a S : Set P) :=
  Equiv.ofBijective (toInsert S a) ⟨toInsert_injective S a ha, toInsert_surjective S a⟩

/-- The entire forward function retains exactly the original old/new label function. -/
theorem adjoinEquiv_function (ha : a ∉ S) : (adjoinEquiv S a ha).toFun = toInsert S a := rfl

end ActualLabels

section OriginalPrefixes

open OriginalCellWellOrderEnumeration

variable {P : Type w} [PartialOrder P] [WellFoundedLT P]

/-- The original next label is not in its original before-prefix. -/
theorem next_not_before (a : OriginalCellWellOrderEnumeration.Index (P := P)) :
    labels.symm a ∉ before a := by
  change ¬ labels (labels.symm a) < a
  simp

/-- The actual after-prefix is precisely the original next label adjoined to the before-prefix. -/
theorem after_insert_before (a : OriginalCellWellOrderEnumeration.Index (P := P)) :
    (after a : Set P) = insert (labels.symm a) (before a : Set P) := by
  ext p
  simp only [SetLike.mem_coe, mem_after_iff, Set.mem_insert_iff]
  exact or_comm

/-- The constructed one-cell index is bijective to the SAME actual original after-prefix labels. -/
def prefixEquiv (a : OriginalCellWellOrderEnumeration.Index (P := P)) :
    GoodCellExtensionOrder.Index (before a) ≃ after a :=
  (adjoinEquiv (before a : Set P) (labels.symm a) (next_not_before a)).trans
    (Set.equivOfEq (after_insert_before a).symm)

end OriginalPrefixes

end CategoryTheory.SmallObject.CellTreeLabelAdjoin
