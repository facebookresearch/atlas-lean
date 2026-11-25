/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.Goodification.OriginalCellTreeGoodification
public import Mathlib.CategoryTheory.Presentable.Type
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Goodification of a one-cell tree over a non-presentable root

The tree attaches the cell `PEmpty → PUnit` to the root `ℕ` along the empty map, with the explicit
pushout square `ℕ → ℕ ⊕ PUnit ← PUnit`. The rank is `ℵ₀`.

The clients check:
* the root `ℕ` is not `ℵ₀`-presentable, and the endpoint map `ℕ → ℕ ⊕ PUnit` is not an
  isomorphism;
* `cellTreeGoodification` applies to this tree with its chosen lower colimits;
* the produced tree is `IsGood ℵ₀` and keeps the original labels;
* its endpoint comparison composes with the produced root arrow to the original endpoint map
  `Sum.inl`, in both directions.

The original and produced partial orders on `Unit` are pinned explicitly, because both live on
the same carrier.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
open OriginalGoodification

set_option autoImplicit false

noncomputable section

@[expose] public section

namespace MathlibExtTest.CategoryTheory.SmallObject.ConcreteGoodification

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The rank `ℵ₀`. -/
abbrev chi : Cardinal.{0} := Cardinal.aleph0

/-- The category instance on `Type`, pinned for explicit applications. -/
abbrev category : Category.{0} (Type 0) := inferInstance

/-- The original vertex order on `Unit`. -/
abbrev originalOrder : PartialOrder Unit := inferInstance

/-- The working-size colimits of `Type`. -/
abbrev colimits : HasColimitsOfSize.{0, 0} (Type 0) := inferInstance

/-- Regularity of `ℵ₀`. -/
abbrev regular : Fact chi.IsRegular := inferInstance

/-- The empty attaching map into the root `ℕ`. -/
abbrev attaching : (PEmpty : Type) ⟶ ℕ := TypeCat.ofHom PEmpty.elim

/-- The generating cell `PEmpty → PUnit`. -/
abbrev generatingCell : (PEmpty : Type) ⟶ PUnit := TypeCat.ofHom PEmpty.elim

/-- The endpoint map `ℕ → ℕ ⊕ PUnit`. -/
abbrev endpointMap : ℕ ⟶ ℕ ⊕ PUnit := TypeCat.ofHom Sum.inl

/-- The cell-target map `PUnit → ℕ ⊕ PUnit`. -/
abbrev cellMap : PUnit ⟶ ℕ ⊕ PUnit := TypeCat.ofHom Sum.inr

/-- The constant one-cell family. -/
abbrev cells : Unit → Arrow (Type 0) := fun _ => Arrow.mk generatingCell

/-- The explicit attaching square is a pushout. -/
theorem square : IsPushout attaching generatingCell endpointMap cellMap := by
  apply IsPushout.mk'
  · ext x
    cases x
  · intro target first second hleft hright
    ext x
    cases x with
    | inl n => exact ConcreteCategory.congr_hom hleft n
    | inr point => exact ConcreteCategory.congr_hom hright point
  · intro target left right _
    exact ⟨TypeCat.ofHom (Sum.elim left right), rfl, rfl⟩

/-- The one-cell tree over the root `ℕ`. -/
abbrev tree : @CellTree (Type 0) category Unit originalOrder Unit cells ℕ :=
  CellTree.ofPushout cells ℕ () attaching endpointMap cellMap square

/-- The chosen lower colimits of the tree. -/
abbrev lowerData : LowerSetColimitData tree.diagram := tree.lowerData

/-- The root `ℕ` is not `ℵ₀`-presentable. -/
theorem root_not_presentable : ¬ IsCardinalPresentable ℕ chi := by
  rw [Types.isCardinalPresentable_iff, hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_nat]
  exact lt_irrefl _

/-- The endpoint map is not an isomorphism. -/
theorem endpoint_not_iso : ¬ IsIso endpointMap := by
  rw [isIso_iff_bijective]
  intro h
  obtain ⟨n, hn⟩ := h.2 (Sum.inr PUnit.unit)
  change (Sum.inl n : ℕ ⊕ PUnit) = Sum.inr PUnit.unit at hn
  cases hn

instance empty_presentable : IsCardinalPresentable (PEmpty : Type) chi :=
  (hasCardinalLT_of_finite PEmpty chi (le_refl _)).isCardinalPresentable

instance unit_presentable : IsCardinalPresentable (PUnit : Type) chi :=
  (hasCardinalLT_of_finite PUnit chi (le_refl _)).isCardinalPresentable

/-- The goodification of the one-cell tree at `ℵ₀`. -/
def output : CellTreeGoodification tree lowerData chi :=
  cellTreeGoodification tree lowerData chi
    (fun _ => by change IsCardinalPresentable (PEmpty : Type) chi; infer_instance)
    (fun _ => by change IsCardinalPresentable (PUnit : Type) chi; infer_instance)

/-- The produced vertex order on `Unit`. -/
abbrev outputOrder : PartialOrder Unit :=
  @CellTreeGoodification.order Unit originalOrder (Type 0) category colimits Unit cells ℕ
    tree lowerData chi regular output

/-- The produced cell tree, with the produced order. -/
abbrev outputTree : @CellTree (Type 0) category Unit outputOrder Unit cells ℕ :=
  @CellTreeGoodification.tree Unit originalOrder (Type 0) category colimits Unit cells ℕ
    tree lowerData chi regular output

/-- The comparison of the produced endpoint with the original endpoint. -/
abbrev endpointIso : (@CellTree.endpointObj (Type 0) category Unit outputOrder Unit cells ℕ
    outputTree) ≅ tree.endpointObj :=
  @CellTreeGoodification.endpointIso Unit originalOrder (Type 0) category colimits Unit cells ℕ
    tree lowerData chi regular output

/-- The produced tree is good at `ℵ₀`. -/
example : @CellTree.IsGood (Type 0) category Unit outputOrder Unit cells ℕ outputTree chi
    regular :=
  @CellTreeGoodification.good Unit originalOrder (Type 0) category colimits Unit cells ℕ
    tree lowerData chi regular output

/-- The produced tree keeps the original labels. -/
example (p : Unit) : @CellTree.label (Type 0) category Unit outputOrder Unit cells ℕ
    outputTree p = tree.label p :=
  @CellTreeGoodification.labels Unit originalOrder (Type 0) category colimits Unit cells ℕ
    tree lowerData chi regular output p

/-- The produced root arrow followed by the endpoint comparison is the original endpoint map. -/
example : @CellTree.hom (Type 0) category Unit outputOrder Unit cells ℕ outputTree ≫
    endpointIso.hom.right = endpointMap :=
  @CellTreeGoodification.root Unit originalOrder (Type 0) category colimits Unit cells ℕ
    tree lowerData chi regular output

/-- The original endpoint map followed by the inverse comparison is the produced root arrow. -/
example : endpointMap ≫ endpointIso.inv.right =
    @CellTree.hom (Type 0) category Unit outputOrder Unit cells ℕ outputTree :=
  @CellTreeGoodification.inv_root Unit originalOrder (Type 0) category colimits Unit cells ℕ
    tree lowerData chi regular output

#print axioms output
#print axioms root_not_presentable
#print axioms endpoint_not_iso

end MathlibExtTest.CategoryTheory.SmallObject.ConcreteGoodification

end
