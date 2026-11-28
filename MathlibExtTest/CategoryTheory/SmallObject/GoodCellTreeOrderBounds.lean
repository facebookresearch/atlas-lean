/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.GoodCellTree.OrderBounds
public import MathlibExtTest.CategoryTheory.SmallObject.GoodCellTreeData

import Mathlib.Tactic.NormNum

/-!
# Original good-order cardinal examples

The natural order has finite strict predecessors and finite lower closures
of finite seeds. Its countable exhaustion shows why the uncountable bound
cannot be omitted. Literal increments and independently sized tree labels
retain their actual original values.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe t

open CategoryTheory CategoryTheory.SmallObject GoodOrderBounds

namespace GoodOrderBoundExamples

attribute [local instance] Cardinal.fact_isRegular_aleph0

/-- The actual strict predecessors in the natural order are finite. -/
theorem natPredecessors (n : ℕ) : HasCardinalLT (Set.Iio n) Cardinal.aleph0.{0} := by
  let : Finite (Set.Iio n) := Finite.of_injective
    (fun a : Set.Iio n => (⟨a.1, a.2⟩ : Fin n))
    (by intro a b h; exact Subtype.ext (congrArg Fin.val h))
  exact hasCardinalLT_of_finite (Set.Iio n) Cardinal.aleph0.{0} le_rfl

/-- Each actual principal natural-number support is finite. -/
theorem natPrincipal (n : ℕ) : HasCardinalLT (Set.Iic n) Cardinal.aleph0.{0} :=
  principalLt Cardinal.aleph0.{0} natPredecessors n

/-- These are the original two selected seed labels. -/
abbrev seeds : Set ℕ := {5, 9}

/-- The lower closure of those actual finite seeds is finite. -/
theorem finiteSeedClosure :
    HasCardinalLT (lowerClosure seeds : Set ℕ) Cardinal.aleph0.{0} :=
  lowerClosureLt Cardinal.aleph0.{0} natPredecessors seeds
    (hasCardinalLT_of_finite seeds Cardinal.aleph0.{0} le_rfl)

/-- Label eight is included by the original seed nine. -/
theorem eight_mem_lowerClosure : (8 : ℕ) ∈ lowerClosure seeds := by
  apply mem_lowerClosure.2
  exact ⟨9, by simp [seeds], by norm_num⟩

/-- The actual old bounded base and the actual finite seed extension. -/
abbrev originalExtension : LowerSet ℕ := extension (LowerSet.Iic 2) seeds

theorem extension_is_bounded :
    HasCardinalLT (originalExtension : Set ℕ) Cardinal.aleph0.{0} :=
  extensionLt Cardinal.aleph0.{0} natPredecessors (LowerSet.Iic 2) seeds
    (natPrincipal 2) (hasCardinalLT_of_finite seeds Cardinal.aleph0.{0} le_rfl)

/-- The unchanged original base label remains in the extension. -/
def baseTwo : originalExtension :=
  baseInclusion (LowerSet.Iic 2) seeds ⟨2, by change (2 : ℕ) ≤ 2; exact le_rfl⟩

theorem baseTwo_value : baseTwo.1 = 2 := rfl

/-- The actual original seed nine retains its own label. -/
def seedNine : originalExtension :=
  seedInclusion (LowerSet.Iic 2) seeds ⟨9, by simp [seeds]⟩

theorem seedNine_value : seedNine.1 = 9 := rfl

/-- The original empty seed produces the actual empty lower support. -/
theorem emptyClosure : lowerClosure (∅ : Set ℕ) = ⊥ := by
  ext a
  constructor
  · intro h
    obtain ⟨b, hb, _⟩ := mem_lowerClosure.1 h
    exact False.elim hb
  · intro h
    exact False.elim (LowerSet.notMem_bot h)

/-- The actual finite-stage exhaustion of the natural order. -/
abbrev stages (n : ℕ) : LowerSet ℕ := LowerSet.Iic n

theorem eachStageSmall (n : ℕ) :
    HasCardinalLT (stages n : Set ℕ) Cardinal.aleph0.{0} :=
  natPrincipal n

/-- Every original natural-number label appears at its own stage. -/
theorem union_is_full : indexedUnion stages = (⊤ : LowerSet ℕ) := by
  ext a
  constructor
  · intro _
    trivial
  · intro _
    apply LowerSet.mem_iSup_iff.2
    exact ⟨a, by change a ≤ a; exact le_rfl⟩

/-- The same countable union is genuinely not below aleph0. -/
theorem countableUnion_notSmall :
    ¬ HasCardinalLT (indexedUnion stages : Set ℕ) Cardinal.aleph0.{0} := by
  intro h
  have hNat : HasCardinalLT ℕ Cardinal.aleph0.{0} :=
    h.of_injective (fun n => ⟨n, LowerSet.mem_iSup_iff.2
      ⟨n, by change n ≤ n; exact le_rfl⟩⟩)
      (by intro a b h; exact congrArg Subtype.val h)
  have hh := (hasCardinalLT_iff_cardinal_mk_lt ℕ Cardinal.aleph0.{0}).1 hNat
  simp only [Cardinal.mk_nat, lt_self_iff_false] at hh

/-- The new actual increment between the original finite supports keeps label one. -/
def incrementOne : CellTree.Increment (LowerSet.Iic (0 : ℕ)) (LowerSet.Iic 1) :=
  ⟨1, ⟨by change (1 : ℕ) ≤ 1; exact le_rfl, by change ¬ (1 : ℕ) ≤ 0; norm_num⟩⟩

theorem incrementOne_value :
    (incrementInclusion (LowerSet.Iic (0 : ℕ)) (LowerSet.Iic 1) incrementOne).1 = 1 := rfl

theorem increment_bounded :
    HasCardinalLT (CellTree.Increment (LowerSet.Iic (0 : ℕ)) (LowerSet.Iic 1))
      Cardinal.aleph0.{0} :=
  incrementLt Cardinal.aleph0.{0} (LowerSet.Iic 0) (LowerSet.Iic 1) (natPrincipal 1)

/-- An actual seed in the original one-occurrence carrier. -/
abbrev treeSeed : Set GoodCellTreeDataExamples.OneVertex := {default}

/-- The accepted original independently sized labels survive the bounded extension. -/
theorem originalTreeLabels :
    HasCardinalLT (lowerClosure treeSeed : Set GoodCellTreeDataExamples.OneVertex)
      Cardinal.aleph0.{0} ∧
    ∀ a : treeSeed, GoodCellTreeDataExamples.quotientTree.{t}.label
      (seedInclusion (⊥ : LowerSet GoodCellTreeDataExamples.OneVertex) treeSeed a).1 =
        GoodCellTreeDataExamples.quotientTree.{t}.label a.1 := by
  constructor
  · exact GoodCellTreeDataExamples.quotientTreeGood.{t}.lowerClosureLt treeSeed
      (hasCardinalLT_of_finite treeSeed Cardinal.aleph0.{0} le_rfl)
  · intro a
    rfl

end GoodOrderBoundExamples
