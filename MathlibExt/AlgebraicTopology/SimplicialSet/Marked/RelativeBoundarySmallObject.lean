/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeBoundaryCompletedCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseCellSmallObject
import MathlibExt.CategoryTheory.SmallObject.CardinalPresentableSources

/-!
# Genuine original-universe source bounds for the relative boundary completion

The actual marked slice is locally presentable, and the full family of
original source and target objects is small. The native small-family
presentability theorem gives a common regular cardinal in the original
value universe. Source presentability then verifies the actual native
transfinite-colimit preservation and constructs the original functorial
small-object factors. This new completed-family bound is not identified
with either frozen earlier bound and is not a uniform bound for all weak
marked monomorphisms.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked.RelativeBoundarySmallObject

/-- Every actual completed source and target has a genuine common presentability rank in the original universe. -/
theorem exists_source_target_cardinal (B : SSet.{u}) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      (∀ s, IsCardinalPresentable (cartesianRelativeBoundaryCell B s).left κ ∧
        IsCardinalPresentable (cartesianRelativeBoundaryCell B s).right κ) ∧
      ∀ s, IsCardinalPresentable (cocartesianRelativeBoundaryCell B s).left κ ∧
        IsCardinalPresentable (cocartesianRelativeBoundaryCell B s).right κ := by
  let _ : IsLocallyPresentable.{u} (Over (max B)) := over_isLocallyPresentable (max B)
  let I := RelativeBoundaryCellIndex cartesianCell.{u} B ⊕ RelativeBoundaryCellIndex cocartesianCell.{u} B
  let _ : Small.{u} (RelativeBoundaryCellIndex cartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ : Small.{u} (RelativeBoundaryCellIndex cocartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ : Small.{u} (I ⊕ I) := inferInstance
  let X : I ⊕ I → Over (max B)
    | .inl (.inl s) => (cartesianRelativeBoundaryCell B s).left
    | .inl (.inr s) => (cocartesianRelativeBoundaryCell B s).left
    | .inr (.inl s) => (cartesianRelativeBoundaryCell B s).right
    | .inr (.inr s) => (cocartesianRelativeBoundaryCell B s).right
  let _ (s : I ⊕ I) : IsPresentable.{u} (X s) := inferInstance
  obtain ⟨κ, hκ, hX⟩ := exists_cardinalPresentable_small_family X
  exact ⟨κ, hκ, fun s => ⟨hX (.inl (.inl s)), hX (.inr (.inl s))⟩,
    fun s => ⟨hX (.inl (.inr s)), hX (.inr (.inr s))⟩⟩

/-- The actual regular source/target rank chosen for this original boundary-completed family. -/
def cardinal (B : SSet.{u}) : Cardinal.{u} := (exists_source_target_cardinal B).choose

/-- Its regularity is supplied by the proved original native presentability bound. -/
theorem cardinal_regular (B : SSet.{u}) : Fact (cardinal B).IsRegular :=
  (exists_source_target_cardinal B).choose_spec.choose

local instance relativeBoundaryCardinalRegular (B : SSet.{u}) : Fact (cardinal B).IsRegular := cardinal_regular B

/-- Each actual original Cartesian completed source is presentable at the proven completed-family rank. -/
theorem cartesian_source_presentable (B : SSet.{u}) (s : RelativeBoundaryCellIndex cartesianCell.{u} B) :
    IsCardinalPresentable (cartesianRelativeBoundaryCell B s).left (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.1 s).1

/-- The corresponding original Cartesian target retains the same actual rank. -/
theorem cartesian_target_presentable (B : SSet.{u}) (s : RelativeBoundaryCellIndex cartesianCell.{u} B) :
    IsCardinalPresentable (cartesianRelativeBoundaryCell B s).right (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.1 s).2

/-- Every original dual completed source has the same genuinely proved source bound. -/
theorem cocartesian_source_presentable (B : SSet.{u}) (s : RelativeBoundaryCellIndex cocartesianCell.{u} B) :
    IsCardinalPresentable (cocartesianRelativeBoundaryCell B s).left (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.2 s).1

/-- Every dual original target is presentable at that unchanged completed-family rank. -/
theorem cocartesian_target_presentable (B : SSet.{u}) (s : RelativeBoundaryCellIndex cocartesianCell.{u} B) :
    IsCardinalPresentable (cocartesianRelativeBoundaryCell B s).right (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.2 s).2

/-- Actual completed source presentability proves the required original transfinite small-object preservation. -/
theorem cartesian_hasSmallObjectArgument (B : SSet.{u}) : HasSmallObjectArgument.{u}
    (cartesianRelativeBoundaryCells B) := by
  let _ : Small.{u} (RelativeBoundaryCellIndex cartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ (s : RelativeBoundaryCellIndex cartesianCell.{u} B) :
      IsCardinalPresentable (cartesianRelativeBoundaryCell B s).left (cardinal B) := cartesian_source_presentable B s
  exact ofHoms_hasSmallObjectArgument_atCardinal _ (cardinal B)

/-- The original dual boundary-completed cells have their same proved native small-object argument. -/
theorem cocartesian_hasSmallObjectArgument (B : SSet.{u}) : HasSmallObjectArgument.{u}
    (cocartesianRelativeBoundaryCells B) := by
  let _ : Small.{u} (RelativeBoundaryCellIndex cocartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ (s : RelativeBoundaryCellIndex cocartesianCell.{u} B) :
      IsCardinalPresentable (cocartesianRelativeBoundaryCell B s).left (cardinal B) :=
        cocartesian_source_presentable B s
  exact ofHoms_hasSmallObjectArgument_atCardinal _ (cardinal B)

/-- The actual original completed Cartesian maps have a native functorial small-object factorization at the
  genuine source rank. -/
def cartesianFunctorialFactorization (B : SSet.{u}) :
    FunctorialFactorizationData (cartesianRelativeBoundaryCells B).rlp.llp (cartesianRelativeBoundaryCells B).rlp := by
  let _ : Small.{u} (RelativeBoundaryCellIndex cartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ (s : RelativeBoundaryCellIndex cartesianCell.{u} B) :
      IsCardinalPresentable (cartesianRelativeBoundaryCell B s).left (cardinal B) := cartesian_source_presentable B s
  exact ofHomsFunctorialFactorizationAtCardinal _ (cardinal B)

/-- The same native source construction retains both original dual factor maps and the completed-family ordinal. -/
def cocartesianFunctorialFactorization (B : SSet.{u}) :
    FunctorialFactorizationData (cocartesianRelativeBoundaryCells B).rlp.llp
      (cocartesianRelativeBoundaryCells B).rlp := by
  let _ : Small.{u} (RelativeBoundaryCellIndex cocartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ (s : RelativeBoundaryCellIndex cocartesianCell.{u} B) :
      IsCardinalPresentable (cocartesianRelativeBoundaryCell B s).left (cardinal B) :=
        cocartesian_source_presentable B s
  exact ofHomsFunctorialFactorizationAtCardinal _ (cardinal B)

end SSet.Marked.RelativeBoundarySmallObject
