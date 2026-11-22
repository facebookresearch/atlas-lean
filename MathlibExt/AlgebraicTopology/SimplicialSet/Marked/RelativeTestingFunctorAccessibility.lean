/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeWeakLiftingTest
import MathlibExt.CategoryTheory.Presentable.LiftingTest

/-!
# Genuine accessibility of the complete original relative weak testing functors

The original endpoint replacement, the completed right factor and the
small tagged mono test each have proved original-universe preservation
bounds. The actual Arrow functor keeps both replacement endpoints and
all squares. Small-family presentability supplies the mono-test rank;
accessible composition combines the different ranks without identifying
or changing any original factor ordinal.
-/

noncomputable section
universe u
open CategoryTheory Limits MorphismProperty

namespace SSet.Marked

private theorem original_mapArrow_accessible {C : Type*} [Category C]
    [HasColimitsOfSize.{u, u} C] (F : C ⥤ C) (κ : Cardinal.{u}) [Fact κ.IsRegular]
    [F.IsCardinalAccessible κ] : F.mapArrow.IsCardinalAccessible κ := by
  let _ : (Arrow.leftFunc : Arrow C ⥤ C).IsCardinalAccessible κ :=
    inferInstanceAs ((Comma.fst (𝟭 C) (𝟭 C)).IsCardinalAccessible κ)
  let _ : (Arrow.rightFunc : Arrow C ⥤ C).IsCardinalAccessible κ :=
    inferInstanceAs ((Comma.snd (𝟭 C) (𝟭 C)).IsCardinalAccessible κ)
  let _ : (F.mapArrow ⋙ Arrow.leftFunc).IsCardinalAccessible κ := by
    change (Arrow.leftFunc ⋙ F).IsCardinalAccessible κ
    infer_instance
  let _ : (F.mapArrow ⋙ Arrow.rightFunc).IsCardinalAccessible κ := by
    change (Arrow.rightFunc ⋙ F).IsCardinalAccessible κ
    infer_instance
  exact Functor.isCardinalAccessible_toArrow _ κ

/-- Both whole original mono-cell endpoints have a genuine common original-universe presentability rank. -/
theorem exists_fixedBaseMono_source_target_cardinal (B : SSet.{u}) :
    ∃ (κ : Cardinal.{u}) (_ : Fact κ.IsRegular),
      ∀ s : FixedBaseMonoIndex B,
        IsCardinalPresentable (fixedBaseMonoCell B s).left κ ∧
          IsCardinalPresentable (fixedBaseMonoCell B s).right κ := by
  let _ : IsLocallyPresentable.{u} (Over (max B)) := over_isLocallyPresentable (max B)
  let I := FixedBaseMonoIndex B
  let _ : Small.{u} I := fixedBaseMonoIndex_small B
  let X : I ⊕ I → Over (max B)
    | .inl s => (fixedBaseMonoCell B s).left
    | .inr s => (fixedBaseMonoCell B s).right
  let _ (s : I ⊕ I) : IsPresentable.{u} (X s) := inferInstance
  obtain ⟨κ, hκ, hX⟩ := exists_cardinalPresentable_small_family X
  exact ⟨κ, hκ, fun s => ⟨hX (.inl s), hX (.inr s)⟩⟩

/-- The actual small original mono lifting functor is accessible from its proved source and target bounds. -/
theorem fixedBaseMonoLiftingTest_isAccessible (B : SSet.{u}) :
    Functor.IsAccessible.{u} (LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)) := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  obtain ⟨κ, hκ, hX⟩ := exists_fixedBaseMono_source_target_cardinal B
  let _ : Fact κ.IsRegular := hκ
  let _ (s : FixedBaseMonoIndex B) : IsCardinalPresentable (fixedBaseMonoCell B s).left κ := (hX s).1
  let _ (s : FixedBaseMonoIndex B) : IsCardinalPresentable (fixedBaseMonoCell B s).right κ := (hX s).2
  let _ : (LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)).IsCardinalAccessible κ :=
    CategoryTheory.Presentable.LiftingTest.smallFunctor_isCardinalAccessible _ κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

/-- The SAME actual Cartesian replacement acts accessibly on both endpoints and every original square. -/
theorem cartesianFixedBaseReplacement_mapArrow_isAccessible (B : SSet.{u}) :
    Functor.IsAccessible.{u} (cartesianFixedBaseReplacementFunctor B).mapArrow := by
  let κ := FixedBaseSmallObject.cardinal B
  let _ : Fact κ.IsRegular := FixedBaseSmallObject.cardinal_regular B
  let _ : (cartesianFixedBaseReplacementFunctor B).IsCardinalAccessible κ :=
    cartesianFixedBaseReplacementFunctor_isCardinalAccessible B
  let _ : (cartesianFixedBaseReplacementFunctor B).mapArrow.IsCardinalAccessible κ :=
    original_mapArrow_accessible _ κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

/-- The unchanged dual replacement retains its actual original all-square accessibility. -/
theorem cocartesianFixedBaseReplacement_mapArrow_isAccessible (B : SSet.{u}) :
    Functor.IsAccessible.{u} (cocartesianFixedBaseReplacementFunctor B).mapArrow := by
  let κ := FixedBaseSmallObject.cardinal B
  let _ : Fact κ.IsRegular := FixedBaseSmallObject.cardinal_regular B
  let _ : (cocartesianFixedBaseReplacementFunctor B).IsCardinalAccessible κ :=
    cocartesianFixedBaseReplacementFunctor_isCardinalAccessible B
  let _ : (cocartesianFixedBaseReplacementFunctor B).mapArrow.IsCardinalAccessible κ :=
    original_mapArrow_accessible _ κ
  exact Functor.isAccessible_of_isCardinalAccessible _ κ

/-- The actual Cartesian replaced-right-factor functor is accessible with its complete original maps and
  separate source ranks. -/
theorem cartesianRelativeTestRightFactor_isAccessible (B : SSet.{u}) :
    Functor.IsAccessible.{u} (cartesianRelativeTestRightFactor B) := by
  let _ : Functor.IsAccessible.{u} (cartesianFixedBaseReplacementFunctor B).mapArrow :=
    cartesianFixedBaseReplacement_mapArrow_isAccessible B
  let κ := RelativeBoundarySmallObject.cardinal B
  let _ : Fact κ.IsRegular := RelativeBoundarySmallObject.cardinal_regular B
  let _ : (RelativeBoundarySmallObject.cartesianFunctorialFactorization
    B).originalRightFactorFunctor.IsCardinalAccessible κ :=
    RelativeBoundarySmallObject.cartesianFunctorialFactorization_right_isCardinalAccessible B
  let _ : Functor.IsAccessible.{u}
      (RelativeBoundarySmallObject.cartesianFunctorialFactorization B).originalRightFactorFunctor :=
    Functor.isAccessible_of_isCardinalAccessible _ κ
  change Functor.IsAccessible.{u} (_ ⋙ _)
  infer_instance

/-- The whole original dual right-factor functor has the same genuinely combined accessibility proof. -/
theorem cocartesianRelativeTestRightFactor_isAccessible (B : SSet.{u}) :
    Functor.IsAccessible.{u} (cocartesianRelativeTestRightFactor B) := by
  let _ : Functor.IsAccessible.{u} (cocartesianFixedBaseReplacementFunctor B).mapArrow :=
    cocartesianFixedBaseReplacement_mapArrow_isAccessible B
  let κ := RelativeBoundarySmallObject.cardinal B
  let _ : Fact κ.IsRegular := RelativeBoundarySmallObject.cardinal_regular B
  let _ : (RelativeBoundarySmallObject.cocartesianFunctorialFactorization
    B).originalRightFactorFunctor.IsCardinalAccessible κ :=
    RelativeBoundarySmallObject.cocartesianFunctorialFactorization_right_isCardinalAccessible B
  let _ : Functor.IsAccessible.{u}
      (RelativeBoundarySmallObject.cocartesianFunctorialFactorization B).originalRightFactorFunctor :=
    Functor.isAccessible_of_isCardinalAccessible _ κ
  change Functor.IsAccessible.{u} (_ ⋙ _)
  infer_instance

/-- The genuine all-original-arrow Cartesian weak test is accessible; this is not inferred from the
  replacement alone. -/
theorem cartesianRelativeWeakLiftingTest_isAccessible (B : SSet.{u}) :
    Functor.IsAccessible.{u} (cartesianRelativeWeakLiftingTest B) := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  let _ : Functor.IsAccessible.{u} (cartesianRelativeTestRightFactor B) :=
    cartesianRelativeTestRightFactor_isAccessible B
  let _ : Functor.IsAccessible.{u} (LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)) :=
    fixedBaseMonoLiftingTest_isAccessible B
  change Functor.IsAccessible.{u} (_ ⋙ _)
  infer_instance

/-- Every original dual arrow and its whole test square belongs to this proved accessible composite. -/
theorem cocartesianRelativeWeakLiftingTest_isAccessible (B : SSet.{u}) :
    Functor.IsAccessible.{u} (cocartesianRelativeWeakLiftingTest B) := by
  let _ : Small.{u} (FixedBaseMonoIndex B) := fixedBaseMonoIndex_small B
  let _ : Functor.IsAccessible.{u} (cocartesianRelativeTestRightFactor B) :=
    cocartesianRelativeTestRightFactor_isAccessible B
  let _ : Functor.IsAccessible.{u} (LiftingTest.smallFunctor.{u} (fixedBaseMonoCell B)) :=
    fixedBaseMonoLiftingTest_isAccessible B
  change Functor.IsAccessible.{u} (_ ⋙ _)
  infer_instance

end SSet.Marked
