/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeBoundarySmallObject
import MathlibExt.CategoryTheory.SmallObject.FactorizationAccessibility

/-!
# Accessibility of the actual completed relative factors

Both original completed endpoints have the genuinely proved common
presentability rank. The native attaching-cofan and transfinite iteration
accessibility theorems apply to the same completed-family ordinal and
whole original maps. This is an actual factor-functor accessibility
proof, not accessibility of all weak marked arrows.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked.RelativeBoundarySmallObject

local instance relativeBoundaryFactorAccessibilityCardinal (B : SSet.{u}) : Fact (cardinal B).IsRegular :=
  cardinal_regular B

/-- Every actual cartesian generator Arrow retains its genuine source bound at the original chosen rank. -/
theorem cartesian_toSet_source_presentable (B : SSet.{u}) (s : (cartesianRelativeBoundaryCells B).toSet) :
    IsCardinalPresentable s.1.left (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cartesian_source_presentable B s

/-- Every actual cartesian generator Arrow retains its whole original target bound. -/
theorem cartesian_toSet_target_presentable (B : SSet.{u}) (s : (cartesianRelativeBoundaryCells B).toSet) :
    IsCardinalPresentable s.1.right (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cartesian_target_presentable B s

/-- The SAME native original cartesian middle factor functor preserves filtered colimits at its proved original rank. -/
theorem cartesianFunctorialFactorization_Z_isCardinalAccessible (B : SSet.{u}) :
    (cartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (RelativeBoundaryCellIndex cartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ (s : RelativeBoundaryCellIndex cartesianCell.{u} B) :
      IsCardinalPresentable (cartesianRelativeBoundaryCell B s).left (cardinal B) := cartesian_source_presentable B s
  let _ : OrderBot (cardinal B).ord.ToType := sourceRankOrderBot (cardinal B)
  let _ : IsCardinalForSmallObjectArgument (cartesianRelativeBoundaryCells B) (cardinal B) :=
    ofHoms_isCardinalForSmallObjectArgument _ (cardinal B)
  let _ (s : (cartesianRelativeBoundaryCells B).toSet) : IsCardinalPresentable s.1.left (cardinal B) :=
    cartesian_toSet_source_presentable B s
  let _ (s : (cartesianRelativeBoundaryCells B).toSet) : IsCardinalPresentable s.1.right (cardinal B) :=
    cartesian_toSet_target_presentable B s
  change (SmallObject.functorialFactorizationData (cartesianRelativeBoundaryCells B) (cardinal
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
theorem cocartesian_toSet_source_presentable (B : SSet.{u}) (s : (cocartesianRelativeBoundaryCells B).toSet) :
    IsCardinalPresentable s.1.left (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cocartesian_source_presentable B s

/-- Every actual cocartesian generator Arrow retains its whole original target bound. -/
theorem cocartesian_toSet_target_presentable (B : SSet.{u}) (s : (cocartesianRelativeBoundaryCells B).toSet) :
    IsCardinalPresentable s.1.right (cardinal B) := by
  rcases s with ⟨⟨A, D, f⟩, hf⟩
  obtain ⟨s⟩ := hf
  exact cocartesian_target_presentable B s

/-- The SAME native original cocartesian middle factor functor preserves filtered colimits at its proved
  original rank. -/
theorem cocartesianFunctorialFactorization_Z_isCardinalAccessible (B : SSet.{u}) :
    (cocartesianFunctorialFactorization B).Z.IsCardinalAccessible (cardinal B) := by
  let _ : Fact (cardinal B).IsRegular := cardinal_regular B
  let _ : Small.{u} (RelativeBoundaryCellIndex cocartesianCell.{u} B) := relativeBoundaryCellIndex_small _ B
  let _ (s : RelativeBoundaryCellIndex cocartesianCell.{u} B) :
      IsCardinalPresentable (cocartesianRelativeBoundaryCell B s).left (cardinal B) :=
        cocartesian_source_presentable B s
  let _ : OrderBot (cardinal B).ord.ToType := sourceRankOrderBot (cardinal B)
  let _ : IsCardinalForSmallObjectArgument (cocartesianRelativeBoundaryCells B) (cardinal B) :=
    ofHoms_isCardinalForSmallObjectArgument _ (cardinal B)
  let _ (s : (cocartesianRelativeBoundaryCells B).toSet) : IsCardinalPresentable s.1.left (cardinal B) :=
    cocartesian_toSet_source_presentable B s
  let _ (s : (cocartesianRelativeBoundaryCells B).toSet) : IsCardinalPresentable s.1.right (cardinal B) :=
    cocartesian_toSet_target_presentable B s
  change (SmallObject.functorialFactorizationData (cocartesianRelativeBoundaryCells B) (cardinal
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

end SSet.Marked.RelativeBoundarySmallObject
