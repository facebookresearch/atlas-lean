/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.FixedBaseCellSmallObject
import MathlibExt.CategoryTheory.SmallObject.FactorizationAccessibility

/-!
# Accessibility of the same original fixed-base factors

Both endpoints of every actual original generator have the proved common
rank. The existing native attaching-cofan and iteration accessibility
theorems apply to the very same functorial factors and ordinal, without
changing their source maps, target maps, base triangles, or marks.
No marked model or general functor-model factory is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked.FixedBaseSmallObject

local instance (B : SSet.{u}) : Fact (cardinal B).IsRegular := cardinal_regular B

/-- Every actual cartesian generator Arrow retains its genuine source bound at the original chosen rank. -/
theorem cartesian_toSet_source_presentable (B : SSet.{u}) (s : (cartesianFixedBaseCells B).toSet) :
    IsCardinalPresentable s.1.left (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cartesian_source_presentable B s

/-- Every actual cartesian generator Arrow retains its whole original target bound. -/
theorem cartesian_toSet_target_presentable (B : SSet.{u}) (s : (cartesianFixedBaseCells B).toSet) :
    IsCardinalPresentable s.1.right (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cartesian_target_presentable B s

/-- The SAME native original cartesian middle factor functor preserves filtered colimits at its proved original rank. -/
theorem cartesianFunctorialFactorization_Z_isCardinalAccessible (B : SSet.{u}) :
    (cartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (FixedBaseCellIndex cartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ (s : FixedBaseCellIndex cartesianCell.{u} B) :
      IsCardinalPresentable (cartesianFixedBaseCell B s).left (cardinal B) := cartesian_source_presentable B s
  let _ : OrderBot (cardinal B).ord.ToType := sourceRankOrderBot (cardinal B)
  let _ : IsCardinalForSmallObjectArgument (cartesianFixedBaseCells B) (cardinal B) :=
    ofHoms_isCardinalForSmallObjectArgument _ (cardinal B)
  let _ (s : (cartesianFixedBaseCells B).toSet) : IsCardinalPresentable s.1.left (cardinal B) :=
    cartesian_toSet_source_presentable B s
  let _ (s : (cartesianFixedBaseCells B).toSet) : IsCardinalPresentable s.1.right (cardinal B) :=
    cartesian_toSet_target_presentable B s
  change (SmallObject.functorialFactorizationData (cartesianFixedBaseCells B) (cardinal
    B)).Z.IsCardinalAccessible (cardinal B)
  exact SmallObject.functorialFactorizationData_Z_isCardinalAccessible _ _ _

/-- The SAME actual cartesian first factor Arrow functor preserves those original filtered colimits. -/
theorem cartesianFunctorialFactorization_left_isCardinalAccessible (B : SSet.{u}) :
    (cartesianFunctorialFactorization B).originalLeftFactorFunctor.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : (cartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) :=
    cartesianFunctorialFactorization_Z_isCardinalAccessible B
  exact (cartesianFunctorialFactorization B).originalLeftFactorFunctor_isCardinalAccessible _

/-- The SAME actual cartesian right factor Arrow functor preserves the same original filtered colimits. -/
theorem cartesianFunctorialFactorization_right_isCardinalAccessible (B : SSet.{u}) :
    (cartesianFunctorialFactorization B).originalRightFactorFunctor.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : (cartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) :=
    cartesianFunctorialFactorization_Z_isCardinalAccessible B
  exact (cartesianFunctorialFactorization B).originalRightFactorFunctor_isCardinalAccessible _

/-- Every actual cocartesian generator Arrow retains its genuine source bound at the original chosen rank. -/
theorem cocartesian_toSet_source_presentable (B : SSet.{u}) (s : (cocartesianFixedBaseCells B).toSet) :
    IsCardinalPresentable s.1.left (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cocartesian_source_presentable B s

/-- Every actual cocartesian generator Arrow retains its whole original target bound. -/
theorem cocartesian_toSet_target_presentable (B : SSet.{u}) (s : (cocartesianFixedBaseCells B).toSet) :
    IsCardinalPresentable s.1.right (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cocartesian_target_presentable B s

/-- The SAME native original cocartesian middle factor functor preserves filtered colimits at its proved
  original rank. -/
theorem cocartesianFunctorialFactorization_Z_isCardinalAccessible (B : SSet.{u}) :
    (cocartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (FixedBaseCellIndex cocartesianCell.{u} B) := fixedBaseCellIndex_small _ B
  let _ (s : FixedBaseCellIndex cocartesianCell.{u} B) :
      IsCardinalPresentable (cocartesianFixedBaseCell B s).left (cardinal B) := cocartesian_source_presentable B s
  let _ : OrderBot (cardinal B).ord.ToType := sourceRankOrderBot (cardinal B)
  let _ : IsCardinalForSmallObjectArgument (cocartesianFixedBaseCells B) (cardinal B) :=
    ofHoms_isCardinalForSmallObjectArgument _ (cardinal B)
  let _ (s : (cocartesianFixedBaseCells B).toSet) : IsCardinalPresentable s.1.left (cardinal B) :=
    cocartesian_toSet_source_presentable B s
  let _ (s : (cocartesianFixedBaseCells B).toSet) : IsCardinalPresentable s.1.right (cardinal B) :=
    cocartesian_toSet_target_presentable B s
  change (SmallObject.functorialFactorizationData (cocartesianFixedBaseCells B) (cardinal
    B)).Z.IsCardinalAccessible (cardinal B)
  exact SmallObject.functorialFactorizationData_Z_isCardinalAccessible _ _ _

/-- The SAME actual cocartesian first factor Arrow functor preserves those original filtered colimits. -/
theorem cocartesianFunctorialFactorization_left_isCardinalAccessible (B : SSet.{u}) :
    (cocartesianFunctorialFactorization B).originalLeftFactorFunctor.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : (cocartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) :=
    cocartesianFunctorialFactorization_Z_isCardinalAccessible B
  exact (cocartesianFunctorialFactorization B).originalLeftFactorFunctor_isCardinalAccessible _

/-- The SAME actual cocartesian right factor Arrow functor preserves the same original filtered colimits. -/
theorem cocartesianFunctorialFactorization_right_isCardinalAccessible (B : SSet.{u}) :
    (cocartesianFunctorialFactorization B).originalRightFactorFunctor.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : (cocartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) :=
    cocartesianFunctorialFactorization_Z_isCardinalAccessible B
  exact (cocartesianFunctorialFactorization B).originalRightFactorFunctor_isCardinalAccessible _

end SSet.Marked.FixedBaseSmallObject
