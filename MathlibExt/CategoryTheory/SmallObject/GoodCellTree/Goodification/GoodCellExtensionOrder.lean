/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.BoundedLowerPresentation

/-!
# The actual weaker order for a captured one-cell good-tree extension

All old cell labels and comparisons are unchanged. The added cell has
only the captured original lower support as its strict predecessors.
The extended carrier records the original old cell or the single added
cell. No size bound on the whole old cell carrier is used.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w

namespace CategoryTheory.SmallObject.GoodCellExtensionOrder

/-- The actual old-cell/new-cell carrier, with no preassigned unrelated ordering. -/
structure Index (P : Type w) where
  /-- The original old label or the unique newly added cell. -/
  val : Option P

namespace Index

/-- The actual original old-cell embedding. -/
def old {P : Type w} (a : P) : Index P := ⟨some a⟩

/-- The unique newly added cell. -/
def new {P : Type w} : Index P := ⟨none⟩

end Index

variable {P : Type w} [PartialOrder P] (B : LowerSet P)

/-- The literal comparisons determined by the old order and the captured lower support. -/
def extensionLe (a b : Index P) : Prop :=
  match a.val, b.val with
  | none, none => True
  | none, some _ => False
  | some a, none => a ∈ B
  | some a, some b => a ≤ b

/-- The actual partial order keeps every old comparison and only the captured new predecessors. -/
@[instance_reducible]
def extensionOrder : PartialOrder (Index P) where
  le := extensionLe B
  lt a b := extensionLe B a b ∧ ¬ extensionLe B b a
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl a := by rcases a with ⟨a⟩; cases a <;> simp [extensionLe]
  le_trans a b c hab hbc := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    rcases c with ⟨c⟩
    cases a with
    | none =>
      cases b with
      | none => exact hbc
      | some b => exact False.elim hab
    | some a =>
      cases b with
      | none =>
        cases c with
        | none => exact hab
        | some c => exact False.elim hbc
      | some b =>
        cases c with
        | none => exact B.lower' hab hbc
        | some c => exact le_trans hab hbc
  le_antisymm a b hab hba := by
    rcases a with ⟨a⟩
    rcases b with ⟨b⟩
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact False.elim hab
    | some a =>
      cases b with
      | none => exact False.elim hba
      | some b => exact congrArg (fun a => Index.mk (some a)) (le_antisymm hab hba)

/-- Every old comparison remains the original comparison of the complete original labels. -/
theorem old_le_old (a b : P) :
    letI := extensionOrder B
    Index.old a ≤ Index.old b ↔ a ≤ b := Iff.rfl

/-- The added cell lies above exactly the captured lower support. -/
theorem old_le_new (a : P) :
    letI := extensionOrder B
    Index.old a ≤ Index.new ↔ a ∈ B := Iff.rfl

/-- The newly added cell never becomes a predecessor of an original old cell. -/
theorem new_not_le_old (a : P) :
    letI := extensionOrder B
    ¬ Index.new ≤ Index.old a := id

/-- All actual old strict comparisons remain their original strict comparisons. -/
theorem old_lt_old (a b : P) :
    letI := extensionOrder B
    Index.old a < Index.old b ↔ a < b := by
  let : PartialOrder (Index P) := extensionOrder B
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge]
  rfl

/-- The captured lower support is the entire strict predecessor carrier of the new cell. -/
theorem old_lt_new (a : P) :
    letI := extensionOrder B
    Index.old a < Index.new ↔ a ∈ B := by
  let : PartialOrder (Index P) := extensionOrder B
  change (a ∈ B ∧ ¬ False) ↔ a ∈ B
  simp

/-- The new cell is never a strict predecessor of an old original cell. -/
theorem new_not_lt_old (a : P) :
    letI := extensionOrder B
    ¬ Index.new < Index.old a := by
  let : PartialOrder (Index P) := extensionOrder B
  intro h
  exact (new_not_le_old B a) h.le

/-- Actual well-foundedness follows from the unchanged old well-founded order. -/
theorem extension_wellFounded (h : WellFounded ((· < ·) : P → P → Prop)) :
    letI := extensionOrder B
    WellFounded ((· < ·) : Index P → Index P → Prop) := by
  let : PartialOrder (Index P) := extensionOrder B
  have old (a : P) : Acc ((· < ·) : Index P → Index P → Prop) (Index.old a) := by
    apply h.induction a
    intro a ih
    refine Acc.intro (Index.old a) ?_
    rintro ⟨b⟩ hb
    cases b with
    | none => exact False.elim ((new_not_lt_old B a) hb)
    | some b => exact ih b ((old_lt_old B b a).1 hb)
  refine ⟨fun a => ?_⟩
  rcases a with ⟨a⟩
  cases a with
  | some a => exact old a
  | none =>
    refine Acc.intro Index.new ?_
    rintro ⟨b⟩ hb
    cases b with
    | some b => exact old b
    | none => exact False.elim ((lt_irrefl (Index.new : Index P)) hb)

/-- The full original predecessor order is the same order on the embedded old cells. -/
def oldPredecessorsIso (a : P) :
    letI := extensionOrder B
    Set.Iio a ≃o Set.Iio (Index.old a) := by
  letI := extensionOrder B
  refine {
    toFun := fun b => ⟨Index.old b.1, (old_lt_old B b.1 a).2 b.2⟩
    invFun := fun b => ?_
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · rcases b with ⟨⟨b⟩, hb⟩
    cases b with
    | none => exact False.elim ((new_not_lt_old B a) hb)
    | some b => exact ⟨b, (old_lt_old B b a).1 hb⟩
  · intro b
    exact Subtype.ext rfl
  · rintro ⟨⟨b⟩, hb⟩
    cases b with
    | none => exact False.elim ((new_not_lt_old B a) hb)
    | some b => exact Subtype.ext rfl
  · intro a b
    rfl

/-- The actual new predecessor carrier is the captured lower support with its original order. -/
def newPredecessorsIso :
    letI := extensionOrder B
    B ≃o Set.Iio (Index.new : Index P) := by
  letI := extensionOrder B
  refine {
    toFun := fun b => ⟨Index.old b.1, (old_lt_new B b.1).2 b.2⟩
    invFun := fun b => ?_
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · rcases b with ⟨⟨b⟩, hb⟩
    cases b with
    | none => exact False.elim ((lt_irrefl (Index.new : Index P)) hb)
    | some b => exact ⟨b, (old_lt_new B b).1 hb⟩
  · intro b
    exact Subtype.ext rfl
  · rintro ⟨⟨b⟩, hb⟩
    cases b with
    | none => exact False.elim ((lt_irrefl (Index.new : Index P)) hb)
    | some b => exact Subtype.ext rfl
  · intro a b
    rfl

end CategoryTheory.SmallObject.GoodCellExtensionOrder
