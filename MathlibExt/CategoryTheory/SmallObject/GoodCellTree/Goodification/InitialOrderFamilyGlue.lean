/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.CellOrderDirectedUnion
public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.LowerSetColimits

/-!
# Actual directed unions of original compatible initial-stage orders

The local comparison relations are extracted from the actual local partial
orders on literal original lower carriers. The whole refining order is
constructed on the same original carrier. Each original stage remains
initial and its complete local order is the whole restricted order.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w

namespace CategoryTheory.SmallObject.InitialOrderFamilyGlue

open LowerSetColimits

variable {P I : Type w} [pOrder : PartialOrder P] [Preorder I]
  (S : I → LowerSet P) (orders : ∀ i : I, PartialOrder (S i))
  (hDirected : ∀ i j : I, ∃ k : I, i ≤ k ∧ j ≤ k)
  (hMono : Monotone S)
  (hRestrict : ∀ (i j : I) (hij : i ≤ j) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i),
    @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩ ↔
      @LE.le (S j) (orders j).toLE ⟨a, hMono hij ha⟩ ⟨b, hMono hij hb⟩)
  (hInitial : ∀ (i j : I) (_ : i ≤ j) (a b : S j), b.1 ∈ S i →
    @LE.le (S j) (orders j).toLE a b → a.1 ∈ S i)
  (hBelow : ∀ (i : I) (a b : S i),
    @LE.le (S i) (orders i).toLE a b → a.1 ≤ b.1)
  (hCover : ∀ p : P, ∃ i : I, p ∈ S i)

/-- Every local comparison is the actual comparison of two literal original stage labels. -/
def rel (i : I) (a b : P) : Prop :=
  ∃ (ha : a ∈ S i) (hb : b ∈ S i),
    @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩

omit [Preorder I] in
/-- The actual local order supplies each original stage label's reflexive comparison. -/
theorem rel_refl (i : I) (p : P) (hp : p ∈ S i) : rel S orders i p p :=
  ⟨hp, hp, (orders i).le_refl _⟩

omit [Preorder I] in
/-- Actual local transitivity proves transitivity of each original stage relation. -/
theorem rel_trans (i : I) (a b c : P)
    (hab : rel S orders i a b) (hbc : rel S orders i b c) : rel S orders i a c := by
  obtain ⟨ha, hb, hab⟩ := hab
  obtain ⟨_, hc, hbc⟩ := hbc
  exact ⟨ha, hc, (orders i).le_trans _ _ _ hab hbc⟩

include hBelow in
omit [Preorder I] in
/-- Each actual original local comparison refines the same original whole precedence. -/
theorem rel_below (i : I) (a b : P) (hab : rel S orders i a b) : a ≤ b := by
  obtain ⟨ha, hb, h⟩ := hab
  exact hBelow i ⟨a, ha⟩ ⟨b, hb⟩ h

include hRestrict in
/-- The actual old-stage order embedding supplies every later original stage comparison. -/
theorem rel_mono (i j : I) (hij : i ≤ j) (a b : P)
    (hab : rel S orders i a b) : rel S orders j a b := by
  obtain ⟨ha, hb, h⟩ := hab
  exact ⟨hMono hij ha, hMono hij hb, (hRestrict i j hij a b ha hb).1 h⟩

include hRestrict hInitial in
/-- An actual later comparison below an old original label stays in that same original old stage. -/
theorem rel_initial (i j : I) (hij : i ≤ j) (a b : P) (hb : b ∈ S i)
    (hab : rel S orders j a b) : rel S orders i a b := by
  obtain ⟨haj, hbj, h⟩ := hab
  have ha : a ∈ S i := hInitial i j hij ⟨a, haj⟩ ⟨b, hbj⟩ hb h
  exact ⟨ha, hb, (hRestrict i j hij a b ha hb).2 h⟩

/-- The actual whole refining partial order is constructed on the same original carrier. -/
@[instance_reducible]
def order : PartialOrder P :=
  CellOrderDirectedUnion.unionOrder (fun i => (S i : Set P)) (rel S orders)
    hDirected (rel_refl S orders) (rel_trans S orders)
    (rel_mono S orders hMono hRestrict) (rel_below S orders hBelow) hCover

include hDirected hMono hRestrict hInitial in
/-- Each complete whole comparison at an original stage is precisely its actual local comparison. -/
theorem le_at_stage (i : I) (a b : P) (ha : a ∈ S i) (hb : b ∈ S i) :
    CellOrderDirectedUnion.unionLe (rel S orders) a b ↔
      @LE.le (S i) (orders i).toLE ⟨a, ha⟩ ⟨b, hb⟩ := by
  constructor
  · intro h
    obtain ⟨_, _, hi⟩ :=
      CellOrderDirectedUnion.unionLe_at_stage (fun i => (S i : Set P))
        (rel S orders) hDirected (rel_mono S orders hMono hRestrict)
        (rel_initial S orders hMono hRestrict hInitial) i hb h
    exact hi
  · intro h
    exact ⟨i, ha, hb, h⟩

/-- Every actual original stage remains lower in the constructed whole refining order. -/
def lower (i : I) :
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    LowerSet P := by
  let carrier : Set P := (S i : Set P)
  have hLower : ∀ (b a : P), a ≤ b → b ∈ carrier → a ∈ carrier := by
    intro b a hab hb
    exact (S i).lower' hab hb
  let r := rel S orders
  have hUnionBelow : ∀ {a b : P}, CellOrderDirectedUnion.unionLe r a b → a ≤ b :=
    fun h => CellOrderDirectedUnion.unionLe_below r (rel_below S orders hBelow) h
  letI := order S orders hDirected hMono hRestrict hBelow hCover
  exact {
    carrier := carrier
    lower' := by
      intro b a hab hb
      exact hLower b a (hUnionBelow hab) hb }

/-- The full original global stage carrier is the literal original stage label set. -/
theorem lower_carrier (i : I) :
    @LowerSet.carrier P (order S orders hDirected hMono hRestrict hBelow hCover).toLE
      (lower S orders hDirected hMono hRestrict hBelow hCover i) =
    @LowerSet.carrier P pOrder.toLE (S i) := rfl

/-- The actual global restricted stage order is inherited from the constructed whole order. -/
@[instance_reducible]
def restrictedOrder (i : I) :
    PartialOrder (lower S orders hDirected hMono hRestrict hBelow hCover i) := by
  letI := order S orders hDirected hMono hRestrict hBelow hCover
  infer_instance

/-- The literal identity on original labels gives the actual whole/local stage order isomorphism. -/
def stageIso (i : I) :
    @OrderIso (lower S orders hDirected hMono hRestrict hBelow hCover i) (S i)
      (restrictedOrder S orders hDirected hMono hRestrict hBelow hCover i).toLE
      (orders i).toLE where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro a b
    change @LE.le (S i) (orders i).toLE ⟨a.1, a.2⟩ ⟨b.1, b.2⟩ ↔
      CellOrderDirectedUnion.unionLe (rel S orders) a.1 b.1
    exact (le_at_stage S orders hDirected hMono hRestrict hInitial i a.1 b.1 a.2 b.2).symm

/-- Original well-foundedness proves the constructed whole refining order is well founded. -/
theorem order_wellFounded (h : WellFounded ((· < ·) : P → P → Prop)) :
    letI := order S orders hDirected hMono hRestrict hBelow hCover
    WellFounded ((· < ·) : P → P → Prop) :=
  CellOrderDirectedUnion.unionOrder_wellFounded (fun i => (S i : Set P)) (rel S orders)
    hDirected (rel_refl S orders) (rel_trans S orders)
    (rel_mono S orders hMono hRestrict) (rel_below S orders hBelow) hCover h

end CategoryTheory.SmallObject.InitialOrderFamilyGlue
