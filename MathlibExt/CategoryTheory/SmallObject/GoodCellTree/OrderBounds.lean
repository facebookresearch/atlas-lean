/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Basic

/-!
# Cardinal bounds on the original good-order labels

A locally bounded strict predecessor function controls lower closures of
bounded original seeds. Joins, original index unions and literal increments
keep the same labels. Countable unions require a genuine uncountable bound.
No coefficient object or subobject intersection is involved.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w t v u uI

namespace CategoryTheory.SmallObject.GoodOrderBounds

open CategoryTheory.Limits LowerSetColimits

variable {P : Type w} [PartialOrder P] (κ : Cardinal.{w}) [Fact κ.IsRegular]

/-- Each original principal lower support adds only its original greatest label. -/
theorem principalLt (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) (a : P) :
    HasCardinalLT (Set.Iic a) κ := by
  have hSet : Set.Iic a = Set.Iio a ∪ {a} := by
    ext x
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
    exact le_iff_lt_or_eq
  rw [hSet]
  exact hasCardinalLT_union (Fact.out : κ.IsRegular).aleph0_le (hPred a)
    (hasCardinalLT_of_finite ({a} : Set P) κ (Fact.out : κ.IsRegular).aleph0_le)

/-- The whole lower closure of bounded original seed labels is bounded. -/
theorem lowerClosureLt (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    (S : Set P) (hS : HasCardinalLT S κ) :
    HasCardinalLT (lowerClosure S : Set P) κ := by
  have hSet : (lowerClosure S : Set P) = ⋃ a : S, Set.Iic a.1 := by
    ext x
    simp only [SetLike.mem_coe, mem_lowerClosure, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · rintro ⟨a, ha, hxa⟩
      exact ⟨⟨a, ha⟩, hxa⟩
    · rintro ⟨⟨a, ha⟩, hxa⟩
      exact ⟨a, ha, hxa⟩
  rw [hSet]
  exact hasCardinalLT_iUnion (fun a : S => Set.Iic a.1) hS
    (fun a => principalLt κ hPred a.1)

/-- The actual arrow carrier on a bounded original principal support is bounded. -/
theorem principalArrowLt (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ) (a : P) :
    HasCardinalLT (Arrow (Set.Iic a)) κ :=
  (hasCardinalLT_arrow_iff_of_isThin (Set.Iic a) κ
    (Fact.out : κ.IsRegular).aleph0_le).2 (principalLt κ hPred a)

/-- The same bound holds for every original arrow on the lower closure. -/
theorem lowerClosureArrowLt (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    (S : Set P) (hS : HasCardinalLT S κ) :
    HasCardinalLT (Arrow (lowerClosure S : Set P)) κ :=
  (hasCardinalLT_arrow_iff_of_isThin (lowerClosure S : Set P) κ
    (Fact.out : κ.IsRegular).aleph0_le).2 (lowerClosureLt κ hPred S hS)

/-- The original lower extension by the given seed labels. -/
abbrev extension (B : LowerSet P) (S : Set P) : LowerSet P :=
  B ⊔ lowerClosure S

/-- Membership in the extension retains the original base and seed labels. -/
theorem mem_extension (B : LowerSet P) (S : Set P) (a : P) :
    a ∈ extension B S ↔ a ∈ B ∨ ∃ b ∈ S, a ≤ b := by
  simp only [extension, LowerSet.mem_sup_iff, mem_lowerClosure]

/-- Every original base label has its literal unchanged extension label. -/
abbrev baseInclusion (B : LowerSet P) (S : Set P) : B → extension B S :=
  fun a => ⟨a.1, Or.inl a.2⟩

/-- Every original seed label has its literal unchanged extension label. -/
abbrev seedInclusion (B : LowerSet P) (S : Set P) : S → extension B S :=
  fun a => ⟨a.1, Or.inr (subset_lowerClosure a.2)⟩

@[simp]
theorem baseInclusion_val (B : LowerSet P) (S : Set P) (a : B) :
    (baseInclusion B S a).1 = a.1 := rfl

@[simp]
theorem seedInclusion_val (B : LowerSet P) (S : Set P) (a : S) :
    (seedInclusion B S a).1 = a.1 := rfl

/-- Both original inclusions remain injective as functions of labels. -/
theorem baseInclusion_injective (B : LowerSet P) (S : Set P) :
    Function.Injective (baseInclusion B S) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : extension B S => x.1) h)

theorem seedInclusion_injective (B : LowerSet P) (S : Set P) :
    Function.Injective (seedInclusion B S) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : extension B S => x.1) h)

/-- The original base/seed inclusions induce an actual lower extension inclusion. -/
theorem extension_mono {B D : LowerSet P} (hBD : B ≤ D)
    {S T : Set P} (hST : S ⊆ T) : extension B S ≤ extension D T :=
  sup_le_sup hBD (lowerClosure_mono hST)

/-- The original extension map keeps each individual label unchanged. -/
abbrev extensionInclusion {B D : LowerSet P} (hBD : B ≤ D)
    {S T : Set P} (hST : S ⊆ T) : extension B S → extension D T :=
  fun a => ⟨a.1, memOfLE (extension_mono hBD hST) a.2⟩

@[simp]
theorem extensionInclusion_val {B D : LowerSet P} (hBD : B ≤ D)
    {S T : Set P} (hST : S ⊆ T) (a : extension B S) :
    (extensionInclusion hBD hST a).1 = a.1 := rfl

/-- A bounded original base and bounded original seeds have a bounded lower extension. -/
theorem extensionLt (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    (B : LowerSet P) (S : Set P)
    (hB : HasCardinalLT (B : Set P) κ) (hS : HasCardinalLT S κ) :
    HasCardinalLT (extension B S : Set P) κ := by
  exact hasCardinalLT_union (Fact.out : κ.IsRegular).aleph0_le hB
    (lowerClosureLt κ hPred S hS)

/-- The exact union of the original indexed lower supports. -/
abbrev indexedUnion {I : Type uI} (B : I → LowerSet P) : LowerSet P :=
  ⨆ i, B i

/-- Each actual source support maps to the same original union label. -/
abbrev indexedInclusion {I : Type uI} (B : I → LowerSet P) (i : I) :
    B i → indexedUnion B :=
  fun a => ⟨a.1, memOfLE (le_iSup B i) a.2⟩

@[simp]
theorem indexedInclusion_val {I : Type uI} (B : I → LowerSet P) (i : I) (a : B i) :
    (indexedInclusion B i a).1 = a.1 := rfl

/-- An actual bounded index and bounded source supports give a bounded original union. -/
theorem indexedUnionLt {I : Type uI} (B : I → LowerSet P)
    (hI : HasCardinalLT I κ) (hB : ∀ i, HasCardinalLT (B i : Set P) κ) :
    HasCardinalLT (indexedUnion B : Set P) κ := by
  have hSet : (indexedUnion B : Set P) = ⋃ i, (B i : Set P) := by
    ext a
    simp only [indexedUnion, SetLike.mem_coe, LowerSet.mem_iSup_iff, Set.mem_iUnion]
  rw [hSet]
  exact hasCardinalLT_iUnion (fun i => (B i : Set P)) hI hB

omit [Fact κ.IsRegular] in
/-- The actual natural-number index is below this genuinely uncountable bound. -/
theorem natLt (hκ : Cardinal.aleph0 < κ) : HasCardinalLT ℕ κ := by
  have hLift : Cardinal.lift.{0, w} (Cardinal.aleph0.{w}) < Cardinal.lift.{0, w} κ :=
    Cardinal.lift_lt.2 hκ
  simpa only [HasCardinalLT, Cardinal.mk_nat, Cardinal.lift_aleph0] using hLift

/-- Countably many original bounded lower supports stay bounded at an uncountable rank. -/
theorem countableUnionLt (hκ : Cardinal.aleph0 < κ) (B : ℕ → LowerSet P)
    (hB : ∀ n, HasCardinalLT (B n : Set P) κ) :
    HasCardinalLT (indexedUnion B : Set P) κ :=
  indexedUnionLt κ B (natLt κ hκ) hB

/-- Countably many original bounded seeds have a bounded original lower closure. -/
theorem countableLowerClosureLt (hPred : ∀ a : P, HasCardinalLT (Set.Iio a) κ)
    (hκ : Cardinal.aleph0 < κ) (S : ℕ → Set P)
    (hS : ∀ n, HasCardinalLT (S n) κ) :
    HasCardinalLT (lowerClosure (⋃ n, S n) : Set P) κ :=
  lowerClosureLt κ hPred (⋃ n, S n)
    (hasCardinalLT_iUnion S (natLt κ hκ) hS)

/-- The actual new-label increment maps injectively into the original upper support. -/
abbrev incrementInclusion (B D : LowerSet P) : CellTree.Increment B D → D :=
  fun a => ⟨a.1, a.2.1⟩

@[simp]
theorem incrementInclusion_val (B D : LowerSet P) (a : CellTree.Increment B D) :
    (incrementInclusion B D a).1 = a.1 := rfl

theorem incrementInclusion_injective (B D : LowerSet P) :
    Function.Injective (incrementInclusion B D) := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : D => x.1) h)

omit [Fact κ.IsRegular] in
/-- Only the bounded original upper support controls the literal increment cardinal. -/
theorem incrementLt (B D : LowerSet P) (hD : HasCardinalLT (D : Set P) κ) :
    HasCardinalLT (CellTree.Increment B D) κ :=
  hD.of_injective (incrementInclusion B D) (incrementInclusion_injective B D)

end CategoryTheory.SmallObject.GoodOrderBounds

namespace CategoryTheory.SmallObject.CellTree.IsGood

open GoodOrderBounds

variable {P : Type w} [PartialOrder P] {C : Type u} [Category.{v} C]
  {α : Type t} {s : α → Arrow C} {X : C} {T : CellTree s X (P := P)}
  {κ : Cardinal.{w}} [Fact κ.IsRegular] (h : T.IsGood κ)

include h

/-- The recorded good-tree bound applies to its original full principal supports. -/
theorem principalLt (a : P) : HasCardinalLT (Set.Iic a) κ :=
  GoodOrderBounds.principalLt κ h.predecessor_lt a

/-- The same actual recorded tree controls lower closure of original bounded seeds. -/
theorem lowerClosureLt (S : Set P) (hS : HasCardinalLT S κ) :
    HasCardinalLT (lowerClosure S : Set P) κ :=
  GoodOrderBounds.lowerClosureLt κ h.predecessor_lt S hS

/-- The original good tree controls extensions without any new root or endpoint assumption. -/
theorem extensionLt (B : LowerSet P) (S : Set P)
    (hB : HasCardinalLT (B : Set P) κ) (hS : HasCardinalLT S κ) :
    HasCardinalLT (GoodOrderBounds.extension B S : Set P) κ :=
  GoodOrderBounds.extensionLt κ h.predecessor_lt B S hB hS

end CategoryTheory.SmallObject.CellTree.IsGood
