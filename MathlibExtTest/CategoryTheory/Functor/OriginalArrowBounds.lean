/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Functor.OriginalArrowBounds
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Original arrow ranks, nonthin indices and duplicate objects

The positive clients retain independent original universes, an empty index,
and the two distinct parallel arrows at an actual natural-number label.
The negative client constructs a genuine equivalence of a codiscrete
category to a one-object category. Its original object cardinal equals
the tested uncountable rank, so its full original Arrow carrier is not
bounded at that rank even though the representative Arrow carrier is.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe w uD vD uI

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor.OriginalArrowBounds

namespace OriginalArrowBoundExamples

section IndependentUniverses

variable (D : Type uD) [Category.{vD} D] [Small.{w} D] [LocallySmall.{w} D]

/-- The actual original object and Hom carriers occur in the generic joint conclusion. -/
theorem independentOriginalCarriers (rank : Cardinal.{w}) :
    ∃ chi : Cardinal.{w}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      rank ≤ chi ∧ HasCardinalLT (Arrow D) chi ∧ HasCardinalLT D chi ∧
      ∀ d e : D, HasCardinalLT (d ⟶ e) chi :=
  existsRegularBoundAbove (D := D) rank

/-- A supplied finite family is retained without identifying any of its cardinal values. -/
theorem independentFiniteRanks (ranks : Finset (Cardinal.{w})) :
    ∃ chi : Cardinal.{w}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      (∀ rank ∈ ranks, rank ≤ chi) ∧
      HasCardinalLT (Arrow D) chi ∧ HasCardinalLT D chi ∧
      ∀ d e : D, HasCardinalLT (d ⟶ e) chi :=
  existsRegularBoundForFiniteRanks (D := D) ranks

end IndependentUniverses

/-- The actual empty ordinary index still has a genuine uncountable regular rank. -/
theorem originalEmptyIndex :
    ∃ chi : Cardinal.{0}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      (0 : Cardinal.{0}) ≤ chi ∧ HasCardinalLT (Arrow (Discrete Empty)) chi ∧
      HasCardinalLT (Discrete Empty) chi ∧
      ∀ d e : Discrete Empty, HasCardinalLT (d ⟶ e) chi :=
  existsRegularBoundAbove (D := Discrete Empty) 0

/-- The actual infinite index contains a nonthin parallel pair at every original Nat label. -/
abbrev NonthinIndex := Discrete ℕ × WalkingParallelPair

instance originalIndexInfinite : Infinite NonthinIndex :=
  Infinite.of_injective (fun n : ℕ => (Discrete.mk n, WalkingParallelPair.zero))
    (fun _ _ h => congrArg (fun d : NonthinIndex => d.1.as) h)

/-- Keep the actual original source object at label seven. -/
def zeroSeven : NonthinIndex := (Discrete.mk 7, WalkingParallelPair.zero)

/-- Keep its actual original parallel target object at the same Nat label. -/
def oneSeven : NonthinIndex := (Discrete.mk 7, WalkingParallelPair.one)

/-- The first actual original arrow retains the left parallel value. -/
def firstOriginal : zeroSeven ⟶ oneSeven :=
  (𝟙 (Discrete.mk 7), WalkingParallelPairHom.left)

/-- The second actual original arrow retains the other parallel value. -/
def secondOriginal : zeroSeven ⟶ oneSeven :=
  (𝟙 (Discrete.mk 7), WalkingParallelPairHom.right)

theorem originalParallelValuesDifferent : firstOriginal ≠ secondOriginal := by
  intro h
  have he : WalkingParallelPairHom.left = WalkingParallelPairHom.right :=
    congrArg Prod.snd h
  cases he

/-- Equality of Arrow values cannot erase these two original Hom values. -/
theorem originalArrowValuesDifferent : Arrow.mk firstOriginal ≠ Arrow.mk secondOriginal := by
  intro h
  exact originalParallelValuesDifferent ((Arrow.mk_inj zeroSeven oneSeven).1 h)

theorem firstOriginalSource : (Arrow.mk firstOriginal).left = zeroSeven := rfl

theorem firstOriginalTarget : (Arrow.mk firstOriginal).right = oneSeven := rfl

theorem secondOriginalSource : (Arrow.mk secondOriginal).left = zeroSeven := rfl

theorem secondOriginalTarget : (Arrow.mk secondOriginal).right = oneSeven := rfl

/-- This actual successor is the fixed original uncountable rank of the negative client. -/
def originalRank : Cardinal.{0} := Order.succ Cardinal.aleph0

instance originalRankRegular : Fact originalRank.IsRegular :=
  ⟨Cardinal.isRegular_succ le_rfl⟩

theorem originalRankUncountable : Cardinal.aleph0.{0} < originalRank :=
  Order.lt_succ_of_le le_rfl

/-- Both distinct supplied cardinal values are bounded on the actual infinite nonthin index. -/
theorem nonthinOriginalRankBounds :
    ∃ chi : Cardinal.{0}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      originalRank ≤ chi ∧ Cardinal.aleph0 ≤ chi ∧
      HasCardinalLT (Arrow NonthinIndex) chi ∧ HasCardinalLT NonthinIndex chi ∧
      ∀ d e : NonthinIndex, HasCardinalLT (d ⟶ e) chi := by
  classical
  let ranks : Finset (Cardinal.{0}) := {Cardinal.aleph0, originalRank}
  obtain ⟨chi, hRegular, hUncountable, hRanks, hArrow, hObjects, hHoms⟩ :=
    existsRegularBoundForFiniteRanks (D := NonthinIndex) ranks
  exact ⟨chi, hRegular, hUncountable, hRanks originalRank (by simp [ranks]),
    hRanks Cardinal.aleph0 (by simp [ranks]), hArrow, hObjects, hHoms⟩

/-- The original nonthin Hom contains both displayed arrows and has the same returned bound. -/
theorem actualParallelHomBound {chi : Cardinal.{0}}
    (hArrow : HasCardinalLT (Arrow NonthinIndex) chi) :
    HasCardinalLT (zeroSeven ⟶ oneSeven) chi :=
  homLt hArrow zeroSeven oneSeven

section OriginalDuplicateObjects

variable (I : Type uI)

/-- The actual forwards functor sends every original object to the one original model point. -/
def toOneModel : Codiscrete I ⥤ Codiscrete PUnit.{1} :=
  Codiscrete.functor (fun _ => PUnit.unit)

/-- The actual inverse uses the specified original object, without changing the original carrier. -/
def fromOneModel (i0 : I) : Codiscrete PUnit.{1} ⥤ Codiscrete I :=
  Codiscrete.functor (fun _ => i0)

/-- A genuine equivalence, whose unit is an isomorphism rather than an object equality. -/
def originalOneEquivalence (i0 : I) : Codiscrete I ≌ Codiscrete PUnit.{1} where
  functor := toOneModel I
  inverse := fromOneModel I i0
  unitIso := Codiscrete.natIso
  counitIso := Codiscrete.natIso
  functor_unitIso_comp _ := rfl

theorem originalForwardObjectFunction :
    (fun d : Codiscrete I => (toOneModel I).obj d) =
      (fun _ : Codiscrete I => Codiscrete.mk PUnit.unit) := rfl

theorem originalInverseObjectFunction (i0 : I) :
    (fun d : Codiscrete PUnit.{1} => (fromOneModel I i0).obj d) =
      (fun _ : Codiscrete PUnit.{1} => Codiscrete.mk i0) := rfl

theorem originalForwardMapFunction :
    (fun (d e : Codiscrete I) (g : d ⟶ e) => (toOneModel I).map g) =
      (fun (d e : Codiscrete I) (_g : d ⟶ e) => (() : Unit)) := rfl

theorem originalInverseMapFunction (i0 : I) :
    (fun (d e : Codiscrete PUnit.{1}) (g : d ⟶ e) => (fromOneModel I i0).map g) =
      (fun (d e : Codiscrete PUnit.{1}) (_g : d ⟶ e) => (() : Unit)) := rfl

/-- The complete original unit hom function has the actual original objects as its sources. -/
theorem originalUnitHomFunction (i0 : I) :
    (fun d : Codiscrete I => (originalOneEquivalence I i0).unitIso.hom.app d) =
      (fun d : Codiscrete I => (() : d ⟶ Codiscrete.mk i0)) := rfl

/-- The complete inverse unit function returns to each actual original object. -/
theorem originalUnitInvFunction (i0 : I) :
    (fun d : Codiscrete I => (originalOneEquivalence I i0).unitIso.inv.app d) =
      (fun d : Codiscrete I => (() : Codiscrete.mk i0 ⟶ d)) := rfl

theorem originalCounitHomFunction (i0 : I) :
    (fun d : Codiscrete PUnit.{1} => (originalOneEquivalence I i0).counitIso.hom.app d) =
      (fun d : Codiscrete PUnit.{1} => (() : d ⟶ d)) := rfl

theorem originalCounitInvFunction (i0 : I) :
    (fun d : Codiscrete PUnit.{1} => (originalOneEquivalence I i0).counitIso.inv.app d) =
      (fun d : Codiscrete PUnit.{1} => (() : d ⟶ d)) := rfl

end OriginalDuplicateObjects

/-- The actual one-object model Arrow carrier is bounded at every infinite rank. -/
theorem oneModelArrowsLt (chi : Cardinal.{w}) (hAleph : Cardinal.aleph0 ≤ chi) :
    HasCardinalLT (Arrow (Codiscrete PUnit.{1})) chi := by
  let : Finite (Codiscrete PUnit.{1}) :=
    Finite.of_equiv PUnit.{1} (codiscreteEquiv (α := PUnit.{1})).symm
  exact (hasCardinalLT_arrow_iff_of_isThin (Codiscrete PUnit.{1}) chi hAleph).2
    (hasCardinalLT_of_finite (Codiscrete PUnit.{1}) chi hAleph)

/-- Original duplicate objects obstruct the full original Arrow bound at the same rank. -/
theorem originalArrowsNotLt {I : Type uI} (chi : Cardinal.{w})
    (hI : ¬ HasCardinalLT I chi) : ¬ HasCardinalLT (Arrow (Codiscrete I)) chi := by
  intro hArrow
  have hObjects : HasCardinalLT (Codiscrete I) chi :=
    hasCardinalLT_of_hasCardinalLT_arrow hArrow
  exact hI (hObjects.of_injective Codiscrete.mk (fun _ _ h => congrArg Codiscrete.as h))

/-- A genuine one-object equivalence does not supply the missing original all-arrow bound. -/
theorem originalRepresentativeBoundary {I : Type uI} (i0 : I) (chi : Cardinal.{w})
    (hAleph : Cardinal.aleph0 ≤ chi) (hI : ¬ HasCardinalLT I chi) :
    Nonempty (Codiscrete I ≌ Codiscrete PUnit.{1}) ∧
      HasCardinalLT (Arrow (Codiscrete PUnit.{1})) chi ∧
      ¬ HasCardinalLT (Arrow (Codiscrete I)) chi :=
  ⟨⟨originalOneEquivalence I i0⟩, oneModelArrowsLt chi hAleph, originalArrowsNotLt chi hI⟩

/-- The concrete original object type has exactly the tested original uncountable cardinal. -/
def DuplicateObjects : Type := originalRank.ord.ToType

theorem duplicateObjectsCardinal : Cardinal.mk DuplicateObjects = originalRank := by
  change Cardinal.mk originalRank.ord.ToType = originalRank
  rw [Cardinal.mk_toType, Cardinal.card_ord]

instance duplicateObjectsNonempty : Nonempty DuplicateObjects :=
  Cardinal.mk_ne_zero_iff.1 (by
    rw [duplicateObjectsCardinal]
    exact ne_of_gt (Cardinal.aleph0_pos.trans originalRankUncountable))

/-- Fix one actual original object for the complete unit/counit construction. -/
def originalDuplicatePoint : DuplicateObjects := Classical.choice duplicateObjectsNonempty

theorem duplicateObjectsNotLt : ¬ HasCardinalLT DuplicateObjects originalRank := by
  rw [hasCardinalLT_iff_cardinal_mk_lt, duplicateObjectsCardinal]
  exact lt_irrefl _

/-- The same concrete original category has an actual one-object model with both comparisons. -/
def concreteOneEquivalence : Codiscrete DuplicateObjects ≌ Codiscrete PUnit.{1} :=
  originalOneEquivalence DuplicateObjects originalDuplicatePoint

/-- At the actual original rank, the representative bound passes and the original bound fails. -/
theorem concreteOriginalArrowBoundary :
    originalRank.IsRegular ∧ Cardinal.aleph0 < originalRank ∧
      Nonempty (Codiscrete DuplicateObjects ≌ Codiscrete PUnit.{1}) ∧
      HasCardinalLT (Arrow (Codiscrete PUnit.{1})) originalRank ∧
      ¬ HasCardinalLT (Arrow (Codiscrete DuplicateObjects)) originalRank :=
  ⟨Fact.out, originalRankUncountable, ⟨concreteOneEquivalence⟩,
    oneModelArrowsLt originalRank originalRankUncountable.le,
    originalArrowsNotLt originalRank duplicateObjectsNotLt⟩

/-- Its actual small original carrier still admits a genuinely larger direct bound. -/
theorem concreteLargerOriginalRank :
    ∃ chi : Cardinal.{0}, chi.IsRegular ∧ Cardinal.aleph0 < chi ∧
      originalRank ≤ chi ∧ HasCardinalLT (Arrow (Codiscrete DuplicateObjects)) chi ∧
      HasCardinalLT (Codiscrete DuplicateObjects) chi ∧
      ∀ d e : Codiscrete DuplicateObjects, HasCardinalLT (d ⟶ e) chi :=
  existsRegularBoundAbove (D := Codiscrete DuplicateObjects) originalRank

end OriginalArrowBoundExamples
