/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseHornCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverLocallyPresentable
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverCellSmallObject
import MathlibExt.CategoryTheory.SmallObject.CardinalPresentableSources

/-!
# Native small-object WFSs for the actual constant-base cells

All source and target objects in both actual fixed-base families are
genuinely presentable in their original marked slice. Their full small
base-map indices have one common regular rank in the original value
universe. The native source-colimit and small-object theorems construct
the functorial WFSs at this same supplied rank. No base-size or Kan bound,
weak-class recognition, or marked-model outcome is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked.FixedBaseSmallObject

/-- Both original fixed-base arrow families have genuine source and target presentability at one actual
  original-universe rank. -/
theorem exists_source_target_cardinal (B : SSet.{u}) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      (∀ s, IsCardinalPresentable (cartesianFixedBaseCell B s).left κ ∧
        IsCardinalPresentable (cartesianFixedBaseCell B s).right κ) ∧
      ∀ s, IsCardinalPresentable (cocartesianFixedBaseCell B s).left κ ∧
        IsCardinalPresentable (cocartesianFixedBaseCell B s).right κ := by
  let _ : IsLocallyPresentable.{u} (Over (max B)) := over_isLocallyPresentable (max B)
  let I := FixedBaseCellIndex cartesianCell.{u} B ⊕ FixedBaseCellIndex cocartesianCell.{u} B
  let _ : Small.{u} (FixedBaseCellIndex cartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ : Small.{u} (FixedBaseCellIndex cocartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ : Small.{u} (I ⊕ I) := inferInstance
  let A : I ⊕ I → Over (max B)
    | .inl (.inl s) => (cartesianFixedBaseCell B s).left
    | .inl (.inr s) => (cocartesianFixedBaseCell B s).left
    | .inr (.inl s) => (cartesianFixedBaseCell B s).right
    | .inr (.inr s) => (cocartesianFixedBaseCell B s).right
  let _ (s : I ⊕ I) : IsPresentable.{u} (A s) := inferInstance
  obtain ⟨κ, hκ, hA⟩ := exists_cardinalPresentable_small_family A
  exact ⟨κ, hκ, fun s => ⟨hA (.inl (.inl s)), hA (.inr (.inl s))⟩,
    fun s => ⟨hA (.inl (.inr s)), hA (.inr (.inr s))⟩⟩

/-- The genuine original common source and target rank for the supplied fixed base. -/
def cardinal (B : SSet.{u}) : Cardinal.{u} := (exists_source_target_cardinal B).choose

/-- The actual selected rank is regular in the original universe. -/
theorem cardinal_regular (B : SSet.{u}) : Fact (cardinal B).IsRegular :=
  (exists_source_target_cardinal B).choose_spec.choose

local instance (B : SSet.{u}) : Fact (cardinal B).IsRegular := cardinal_regular B

/-- Every actual original cartesian fixed-base cell has its source presentable at the selected common rank. -/
theorem cartesian_source_presentable (B : SSet.{u}) (s : FixedBaseCellIndex cartesianCell.{u} B) :
    IsCardinalPresentable (cartesianFixedBaseCell B s).left (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.1 s).1

/-- The entire original cartesian target family has the same actual presentability bound. -/
theorem cartesian_target_presentable (B : SSet.{u}) (s : FixedBaseCellIndex cartesianCell.{u} B) :
    IsCardinalPresentable (cartesianFixedBaseCell B s).right (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.1 s).2

/-- Source presentability proves the native same-rank small-object hypotheses for the actual cartesian
  fixed-base cells. -/
theorem cartesian_hasSmallObjectArgument (B : SSet.{u}) : HasSmallObjectArgument.{u} (cartesianFixedBaseCells B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (FixedBaseCellIndex cartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ (s : FixedBaseCellIndex cartesianCell.{u} B) :
      IsCardinalPresentable (cartesianFixedBaseCell B s).left (cardinal B) := cartesian_source_presentable B s
  exact ofHoms_hasSmallObjectArgument_atCardinal _ (cardinal B)

/-- The actual original cartesian factors use the specified common source rank and its original ordinal. -/
def cartesianFunctorialFactorization (B : SSet.{u}) :
    FunctorialFactorizationData (cartesianFixedBaseCells B).rlp.llp (cartesianFixedBaseCells B).rlp := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (FixedBaseCellIndex cartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ (s : FixedBaseCellIndex cartesianCell.{u} B) :
      IsCardinalPresentable (cartesianFixedBaseCell B s).left (cardinal B) := cartesian_source_presentable B s
  exact ofHomsFunctorialFactorizationAtCardinal _ (cardinal B)

/-- The actual cartesian fixed-base lifting classes genuinely form a functorial weak factorization system. -/
theorem cartesian_isWeakFactorizationSystem (B : SSet.{u}) :
    IsWeakFactorizationSystem (cartesianFixedBaseCells B).rlp.llp (cartesianFixedBaseCells B).rlp := by
  let _ : HasFunctorialFactorization (cartesianFixedBaseCells B).rlp.llp (cartesianFixedBaseCells B).rlp :=
    ⟨⟨cartesianFunctorialFactorization B⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- The entire actual cartesian fixed-base cell left class consists of original marked slice monomorphisms. -/
theorem cartesian_left_le_monomorphisms (B : SSet.{u}) :
    (cartesianFixedBaseCells B).rlp.llp ≤ monomorphisms (Over (max B)) := by
  calc
    _ ≤ (monomorphisms (Over (max B))).rlp.llp :=
      antitone_llp (antitone_rlp (cartesianFixedBaseCells_le_monomorphisms B))
    _ = _ := (CellSmallness.over_mono_isWeakFactorizationSystem B).llp

/-- Every actual original cocartesian fixed-base cell has its source presentable at the selected common rank. -/
theorem cocartesian_source_presentable (B : SSet.{u}) (s : FixedBaseCellIndex cocartesianCell.{u} B) :
    IsCardinalPresentable (cocartesianFixedBaseCell B s).left (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.2 s).1

/-- The entire original cocartesian target family has the same actual presentability bound. -/
theorem cocartesian_target_presentable (B : SSet.{u}) (s : FixedBaseCellIndex cocartesianCell.{u} B) :
    IsCardinalPresentable (cocartesianFixedBaseCell B s).right (cardinal B) :=
  ((exists_source_target_cardinal B).choose_spec.choose_spec.2 s).2

/-- Source presentability proves the native same-rank small-object hypotheses for the actual cocartesian
  fixed-base cells. -/
theorem cocartesian_hasSmallObjectArgument (B : SSet.{u}) : HasSmallObjectArgument.{u}
    (cocartesianFixedBaseCells B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (FixedBaseCellIndex cocartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ (s : FixedBaseCellIndex cocartesianCell.{u} B) :
      IsCardinalPresentable (cocartesianFixedBaseCell B s).left (cardinal B) := cocartesian_source_presentable B s
  exact ofHoms_hasSmallObjectArgument_atCardinal _ (cardinal B)

/-- The actual original cocartesian factors use the specified common source rank and its original ordinal. -/
def cocartesianFunctorialFactorization (B : SSet.{u}) :
    FunctorialFactorizationData (cocartesianFixedBaseCells B).rlp.llp (cocartesianFixedBaseCells B).rlp := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (FixedBaseCellIndex cocartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ (s : FixedBaseCellIndex cocartesianCell.{u} B) :
      IsCardinalPresentable (cocartesianFixedBaseCell B s).left (cardinal B) := cocartesian_source_presentable B s
  exact ofHomsFunctorialFactorizationAtCardinal _ (cardinal B)

/-- The actual cocartesian fixed-base lifting classes genuinely form a functorial weak factorization system. -/
theorem cocartesian_isWeakFactorizationSystem (B : SSet.{u}) :
    IsWeakFactorizationSystem (cocartesianFixedBaseCells B).rlp.llp (cocartesianFixedBaseCells B).rlp := by
  let _ : HasFunctorialFactorization (cocartesianFixedBaseCells B).rlp.llp (cocartesianFixedBaseCells B).rlp :=
    ⟨⟨cocartesianFunctorialFactorization B⟩⟩
  exact IsWeakFactorizationSystem.mk' _ _ (fun i p hi hp => hi p hp)

/-- The entire actual cocartesian fixed-base cell left class consists of original marked slice monomorphisms. -/
theorem cocartesian_left_le_monomorphisms (B : SSet.{u}) :
    (cocartesianFixedBaseCells B).rlp.llp ≤ monomorphisms (Over (max B)) := by
  calc
    _ ≤ (monomorphisms (Over (max B))).rlp.llp :=
      antitone_llp (antitone_rlp (cocartesianFixedBaseCells_le_monomorphisms B))
    _ = _ := (CellSmallness.over_mono_isWeakFactorizationSystem B).llp

end SSet.Marked.FixedBaseSmallObject
