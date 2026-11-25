/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
# Genuine directed unions of original refining cell orders

The union relation is constructed from compatible actual local stage
relations. Directedness proves its transitivity; original precedence proves
antisymmetry and well-foundedness. Initial-stage compatibility identifies
every whole predecessor with an actual old stage predecessor, retaining
local cardinal bounds without bounding the whole original cell carrier.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w

namespace CategoryTheory.SmallObject.CellOrderDirectedUnion

variable {P I : Type w} [pOrder : PartialOrder P] [Preorder I]
  (S : I → Set P) (r : I → P → P → Prop)
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hRefl : ∀ i p, p ∈ S i → r i p p)
  (hTrans : ∀ i a b c, r i a b → r i b c → r i a c)
  (hMono : ∀ i j, i ≤ j → ∀ a b, r i a b → r j a b)
  (hBelow : ∀ i a b, r i a b → a ≤ b)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)

/-- The actual whole comparison relation is the union of the original local stage relations. -/
def unionLe (a b : P) : Prop := ∃ i : I, r i a b

include hRefl hCover in
omit [PartialOrder P] [Preorder I] in
/-- Every original label has its actual local reflexive comparison in the whole relation. -/
theorem unionLe_refl (p : P) : unionLe r p p := by
  obtain ⟨i, hi⟩ := hCover p
  exact ⟨i, hRefl i p hi⟩

include hDirected hTrans hMono in
omit [PartialOrder P] in
/-- A real common original stage proves transitivity of the actual whole relation. -/
theorem unionLe_trans {a b c : P} (hab : unionLe r a b) (hbc : unionLe r b c) :
    unionLe r a c := by
  obtain ⟨i, hi⟩ := hab
  obtain ⟨j, hj⟩ := hbc
  obtain ⟨k, hik, hjk⟩ := hDirected i j
  exact ⟨k, hTrans k a b c (hMono i k hik a b hi) (hMono j k hjk b c hj)⟩

include hBelow in
omit [Preorder I] in
/-- Every actual whole comparison refines the same original cell precedence. -/
theorem unionLe_below {a b : P} (h : unionLe r a b) : a ≤ b := by
  obtain ⟨i, hi⟩ := h
  exact hBelow i a b hi

/-- The actual whole partial order is constructed on the same original carrier. -/
@[instance_reducible]
def unionOrder : PartialOrder P where
  le := unionLe r
  lt a b := unionLe r a b ∧ a ≠ b
  le_refl := unionLe_refl S r hRefl hCover
  le_trans _ _ _ := unionLe_trans r hDirected hTrans hMono
  le_antisymm a b hab hba :=
    le_antisymm (unionLe_below r hBelow hab) (unionLe_below r hBelow hba)
  lt_iff_le_not_ge a b := by
    constructor
    · rintro ⟨hab, hne⟩
      refine ⟨hab, ?_⟩
      intro hba
      exact hne (le_antisymm (unionLe_below r hBelow hab) (unionLe_below r hBelow hba))
    · rintro ⟨hab, hba⟩
      refine ⟨hab, ?_⟩
      intro he
      subst b
      exact hba (unionLe_refl S r hRefl hCover a)

include hDirected hRefl hTrans hMono hBelow hCover in
/-- Original well-foundedness proves well-foundedness of the constructed whole refining order. -/
theorem unionOrder_wellFounded (h : WellFounded ((· < ·) : P → P → Prop)) :
    letI := unionOrder S r hDirected hRefl hTrans hMono hBelow hCover
    WellFounded ((· < ·) : P → P → Prop) := by
  let : PartialOrder P := unionOrder S r hDirected hRefl hTrans hMono hBelow hCover
  apply h.mono
  intro a b hab
  obtain ⟨i, hi⟩ := hab.1
  exact @lt_of_le_of_ne P pOrder a b (hBelow i a b hi) hab.2

variable
  (hInitial : ∀ i j, i ≤ j → ∀ a b, b ∈ S i → r j a b → r i a b)

include hDirected hMono hInitial in
omit [PartialOrder P] in
/-- Every whole predecessor of an original old-stage label is in that same actual old stage. -/
theorem unionLe_at_stage (i : I) {a b : P} (hb : b ∈ S i) (h : unionLe r a b) :
    r i a b := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨k, hik, hjk⟩ := hDirected i j
  exact hInitial i k hik a b hb (hMono j k hjk a b hj)

include hDirected hRefl hTrans hMono hBelow hCover hInitial in
/-- Genuine local stage predecessor bounds control every whole original strict predecessor. -/
theorem unionOrder_predecessor_bound (chi : Cardinal.{w})
    (hLocal : ∀ i p, p ∈ S i → HasCardinalLT {q : P // r i q p ∧ q ≠ p} chi)
    (p : P) :
    letI := unionOrder S r hDirected hRefl hTrans hMono hBelow hCover
    HasCardinalLT (Set.Iio p) chi := by
  let : PartialOrder P := unionOrder S r hDirected hRefl hTrans hMono hBelow hCover
  obtain ⟨i, hi⟩ := hCover p
  let f : Set.Iio p → {q : P // r i q p ∧ q ≠ p} := fun q =>
    ⟨q.1, unionLe_at_stage S r hDirected hMono hInitial i hi q.2.1, q.2.2⟩
  exact (hLocal i p hi).of_injective f (by
    intro a b h
    have hv : (f a).1 = (f b).1 :=
      congrArg (fun q : {q : P // r i q p ∧ q ≠ p} => q.1) h
    exact Subtype.ext hv)

end CategoryTheory.SmallObject.CellOrderDirectedUnion
