/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Sources.ChosenActionModels
import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Sources.PresentableCarrier
import MathlibExt.CategoryTheory.SmallObject.CardinalPresentableSources

/-!
# Actual common presentability rank of all original chosen free endpoints

The small family contains every original free I_n/J_n source and target in
every ordinary degree. The produced regular rank and bottom therefore apply
to both original ordinary and positive families without replacing any map.
-/

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty Opposite MonoidalCategory MonObj
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.Chosen

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C] [IsLocallyPresentable.{w} C]

local instance rankBaseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

local instance rankTensorLeftPreservesSmallColimits (X : C) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) := inferInstance
local instance rankTensorRightPreservesSmallColimits (X : C) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) := inferInstance

/-- The canonical Day structure preceding the source family rank construction. -/
local instance rankCanonicalDayMonoidal : MonoidalCategory (DayFunctor I C) := inferInstance

variable (models : ChosenActionModels.{w} C)

omit [SymmetricCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C]
  [IsLocallyPresentable.{w} C] in
/-- Each actual chosen I_n family is working-small by its genuine source small-object argument. -/
theorem I_isSmall (n : ℕ) : (models.I n).IsSmall.{w} := by
  let _ : (models.I n).HasSmallObjectArgument.{w} := models.I_smallObject n
  obtain ⟨κ, _, _, hc⟩ := HasSmallObjectArgument.exists_cardinal («I» := models.I n)
  exact hc.isSmall

omit [SymmetricCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C]
  [IsLocallyPresentable.{w} C] in
/-- Each original J_n family retains the same genuine source-small family evidence. -/
theorem J_isSmall (n : ℕ) : (models.J n).IsSmall.{w} := by
  let _ : (models.J n).HasSmallObjectArgument.{w} := models.J_smallObject n
  obtain ⟨κ, _, _, hc⟩ := HasSmallObjectArgument.exists_cardinal («I» := models.J n)
  exact hc.isSmall

/-- The unchanged ordinary degree, I/J label, and source/target label of every actual free endpoint. -/
abbrev FreeEndpointIndex := (Σ n : ℕ, (models.I n).toSet ⊕ (models.J n).toSet) × Bool

variable (R : DayFunctor I C) [MonObj R]

local instance rankModuleColimits : HasColimitsOfSize.{w, w} (CategoryTheory.Mod (DayFunctor I C) R) :=
    moduleHasColimits R
local instance rankModulePresentable : IsLocallyPresentable.{w} (CategoryTheory.Mod (DayFunctor I C) R) :=
  moduleIsLocallyPresentable R

/-- Every original actual free source and target occurs in the same complete endpoint family. -/
def freeEndpoint (q : FreeEndpointIndex models) : CategoryTheory.Mod (DayFunctor I C) R :=
  match q.1.2 with
  | .inl i => (degreeActionFreeAt R q.1.1).obj (if q.2 then i.1.right else i.1.left)
  | .inr j => (degreeActionFreeAt R q.1.1).obj (if q.2 then j.1.right else j.1.left)

/-- The actual produced common cardinal and its original ordinal bottom. -/
structure ModuleGenerationRank where
  /-- The actual common regular rank of all original ordinary free endpoints. -/
  cardinal : Cardinal.{w}
  regular : Fact cardinal.IsRegular
  /-- The original ordinal bottom selected with this common endpoint rank. -/
  orderBot : OrderBot cardinal.ord.ToType
  presentable : let _ := regular
    ∀ q : FreeEndpointIndex models, IsCardinalPresentable (freeEndpoint models R q) cardinal

/-- The original all-degree free source and target family produces a genuine common regular rank. -/
def moduleGenerationRank : ModuleGenerationRank models R := by
  apply Classical.choice
  let _ (n : ℕ) : Small.{w} (models.I n).toSet := (I_isSmall models n).small_toSet
  let _ (n : ℕ) : Small.{w} (models.J n).toSet := (J_isSmall models n).small_toSet
  let _ : Small.{w} (FreeEndpointIndex models) := inferInstance
  obtain ⟨κ, hκ, hSources⟩ := exists_cardinalPresentable_small_family (freeEndpoint models R)
  let _ : Fact κ.IsRegular := hκ
  let bottom : OrderBot κ.ord.ToType := sourceRankOrderBot κ
  exact ⟨⟨κ, hκ, bottom, hSources⟩⟩

namespace ModuleGenerationRank

variable (e : ModuleGenerationRank models R)
local instance chosenRankRegular : Fact e.cardinal.IsRegular := e.regular
/-- The actual ordinal bottom retained from the supplied free endpoint rank. -/
local instance chosenRankBottom : OrderBot e.cardinal.ord.ToType := e.orderBot

omit [HasLimitsOfSize.{0, 0} C] [IsLocallyPresentable.{w} C] in
/-- Every original free I_n source is presentable at the same actual chosen rank. -/
theorem I_source_presentable (n : ℕ) (i : (models.I n).toSet) :
    IsCardinalPresentable ((degreeActionFreeAt R n).obj i.1.left) e.cardinal :=
  e.presentable ⟨⟨n, .inl i⟩, false⟩

omit [HasLimitsOfSize.{0, 0} C] [IsLocallyPresentable.{w} C] in
/-- Every original free I_n target retains the same full rank witness. -/
theorem I_target_presentable (n : ℕ) (i : (models.I n).toSet) :
    IsCardinalPresentable ((degreeActionFreeAt R n).obj i.1.right) e.cardinal :=
  e.presentable ⟨⟨n, .inl i⟩, true⟩

omit [HasLimitsOfSize.{0, 0} C] [IsLocallyPresentable.{w} C] in
/-- Every original free J_n source has the same actual produced presentability rank. -/
theorem J_source_presentable (n : ℕ) (j : (models.J n).toSet) :
    IsCardinalPresentable ((degreeActionFreeAt R n).obj j.1.left) e.cardinal :=
  e.presentable ⟨⟨n, .inr j⟩, false⟩

omit [HasLimitsOfSize.{0, 0} C] [IsLocallyPresentable.{w} C] in
/-- Every original free J_n target is included without dropping its own original map label. -/
theorem J_target_presentable (n : ℕ) (j : (models.J n).toSet) :
    IsCardinalPresentable ((degreeActionFreeAt R n).obj j.1.right) e.cardinal :=
  e.presentable ⟨⟨n, .inr j⟩, true⟩

/-- All six original I-family eligibility fields hold at the actual rank, for either retained-degree variant. -/
theorem I_eligible (positive : Bool) : (actionGenerators R positive models.I).IsCardinalForSmallObjectArgument
    e.cardinal := by
  let _ (n : ℕ) : Small.{w} (models.I n).toSet := (I_isSmall models n).small_toSet
  let _ : Small.{w} (Σ n : {n : ℕ // positive = true → 0 < n}, (models.I n.1).toSet) := inferInstance
  let _ (q : Σ n : {n : ℕ // positive = true → 0 < n}, (models.I n.1).toSet) :
      IsCardinalPresentable ((degreeActionFreeAt R q.1.1).obj q.2.1.left) e.cardinal := I_source_presentable models R e
          q.1.1 q.2
  exact ofHoms_isCardinalForSmallObjectArgument
    (fun q : Σ n : {n : ℕ // positive = true → 0 < n}, (models.I n.1).toSet => (degreeActionFreeAt R q.1.1).map
        q.2.1.hom)
    e.cardinal

/-- The same actual rank supplies the full original J-family small-object argument in both variants. -/
theorem J_eligible (positive : Bool) : (actionGenerators R positive models.J).IsCardinalForSmallObjectArgument
    e.cardinal := by
  let _ (n : ℕ) : Small.{w} (models.J n).toSet := (J_isSmall models n).small_toSet
  let _ : Small.{w} (Σ n : {n : ℕ // positive = true → 0 < n}, (models.J n.1).toSet) := inferInstance
  let _ (q : Σ n : {n : ℕ // positive = true → 0 < n}, (models.J n.1).toSet) :
      IsCardinalPresentable ((degreeActionFreeAt R q.1.1).obj q.2.1.left) e.cardinal := J_source_presentable models R e
          q.1.1 q.2
  exact ofHoms_isCardinalForSmallObjectArgument
    (fun q : Σ n : {n : ℕ // positive = true → 0 < n}, (models.J n.1).toSet => (degreeActionFreeAt R q.1.1).map
        q.2.1.hom)
    e.cardinal

end ModuleGenerationRank
end HomotopicalAlgebra.PositiveLevelModel.Chosen
