/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Carrier
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.CellularProjective.CoefficientClasses
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.Sources.CellularRanks
public import MathlibExt.CategoryTheory.SmallObject.AdjointFamilySourceSmallness

/-!
# Both actual small-object arguments in the cellular projective branch

The original free/evaluation adjunctions and actual evaluated R-coefficient
cofibrations carry the established source and target rank to the same original
free generating objects. Every original I/J arrow and ordinal bottom is kept.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe w v u

open CategoryTheory Limits MorphismProperty MonoidalCategory MonObj Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj MonoidalClosed

namespace HomotopicalAlgebra.PositiveLevelModel.CellularProjective

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [ModelCategory C] [IsClosedSymmetricMonoidalModelCategory C]
  [HasColimitsOfSize.{w, w} C] [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (h : CellularSource d)

local instance baseSmallColimits : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, w, w} C

variable (R : DayFunctor I C) [MonObj R]
  (hR : ∀ n : ℕ, IsCofibrant (R.functor.obj (CategoryTheory.Operad.SmallFinBijGroupoid.card n)))

local instance originalModuleColimits : HasColimitsOfSize.{w, w} (CategoryTheory.Mod (DayFunctor I C) R) :=
  moduleHasColimits R
local instance originalModuleSmallColimits : HasColimitsOfSize.{0, 0} (CategoryTheory.Mod (DayFunctor I C) R) :=
  hasColimitsOfSizeShrink.{0, 0, w, w} _
local instance originalDiagramLocallySmall : LocallySmall.{w} (I ⥤ C) where
  hom_small F G := small_of_injective (f := fun f : F ⟶ G => f.app)
    (fun _ _ hfg => NatTrans.ext hfg)
local instance originalDayLocallySmall : LocallySmall.{w} (DayFunctor I C) :=
  locallySmall_of_faithful (DayFunctor.equiv I C).symm.inverse
local instance originalForgetFaithful : (CategoryTheory.Mod.forget (D := DayFunctor I C) R).Faithful where
  map_injective {_ _} f g hfg := CategoryTheory.Mod.hom_ext f g hfg
local instance originalModuleLocallySmall : LocallySmall.{w} (CategoryTheory.Mod (DayFunctor I C) R) :=
  locallySmall_of_faithful (CategoryTheory.Mod.forget (D := DayFunctor I C) R)

variable {S : Type} [Small.{w} S] (degree : S → ℕ)

/-- The actual original free R-module at every retained finite cardinal. -/
abbrev projectiveFreeFamily : S → C ⥤ CategoryTheory.Mod (DayFunctor I C) R :=
  fun s => CategoryTheory.Mod.dayFreeAt R (CategoryTheory.Operad.SmallFinBijGroupoid.card (degree s))

/-- The same original R-module evaluation at those same retained degrees. -/
abbrev projectiveEvaluationFamily : S → CategoryTheory.Mod (DayFunctor I C) R ⥤ C :=
  fun s => CategoryTheory.Mod.dayEvaluation R (CategoryTheory.Operad.SmallFinBijGroupoid.card (degree s))

/-- The actual original free/evaluation adjunctions at all retained degrees. -/
abbrev projectiveAdjunctionFamily : ∀ s, projectiveFreeFamily R degree s ⊣
    projectiveEvaluationFamily R degree s :=
  fun s => CategoryTheory.Mod.dayFreeAtEvaluationAdjunction R (CategoryTheory.Operad.SmallFinBijGroupoid.card (degree
      s))

local instance originalEvaluationPreservesColimits (s : S) :
    PreservesColimitsOfSize.{w, w} (projectiveEvaluationFamily R degree s) :=
  moduleEvaluationPreservesColimits R _

local instance originalEvaluationPreservesCardinalColimits (s : S) (mu : Cardinal.{w}) :
    PreservesColimitsOfShape mu.ord.ToType (projectiveEvaluationFamily R degree s) := inferInstance

local instance originalEvaluationPreservesContinuous (s : S) (mu : Cardinal.{w}) :
    PreservesWellOrderContinuousOfShape mu.ord.ToType (projectiveEvaluationFamily R degree s) where
  preservesColimitsOfShape _ _ := inferInstance

local instance baseCofibrationsCoproducts : (cofibrations C).IsStableUnderCoproducts.{w} :=
  IsStableUnderCoproducts.of_llp_eq _ _ (trivialFibrations_llp C)
local instance baseCofibrationsTransfinite : (cofibrations C).IsStableUnderTransfiniteComposition.{w} :=
  IsStableUnderTransfiniteComposition.of_llp_eq _ _ (trivialFibrations_llp C)
local instance baseTrivialCofibrationsCoproducts : (trivialCofibrations C).IsStableUnderCoproducts.{w} :=
  IsStableUnderCoproducts.of_llp_eq _ _ (fibrations_llp C)
local instance baseTrivialCofibrationsTransfinite : (trivialCofibrations C).IsStableUnderTransfiniteComposition.{w} :=
  IsStableUnderTransfiniteComposition.of_llp_eq _ _ (fibrations_llp C)

include hR in
omit [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C] [Small.{w} S] in
/-- Every literal original free generator has a cofibration at each actual retained evaluation. -/
theorem projectiveGenerators_evaluation_cofibrations (K : MorphismProperty C) (hK : K ≤ cofibrations C) (s : S) :
    adjointFamilyGenerators (projectiveFreeFamily R degree) K ≤
      (cofibrations C).inverseImage (projectiveEvaluationFamily R degree s) := by
  intro X Y f hf
  obtain ⟨q, hq⟩ := (adjointFamilyGenerators_iff _ _ f).mp hf
  have hBase := projectiveFreeAt_evaluated_cofibration R hR (degree q.1) (degree s) q.2.1.hom (hK _ q.2.2)
  exact ((cofibrations C).arrow_iso_iff
    ((projectiveEvaluationFamily R degree s).mapArrow.mapIso (eqToIso hq))).mpr hBase

include hR in
omit [HasLimitsOfSize.{0, 0} C] [LocallySmall.{w} C] [Small.{w} S] in
/-- Every original free J generator is a trivial cofibration at each original retained evaluation. -/
theorem projectiveJGenerators_evaluation_trivialCofibrations (s : S) :
    adjointFamilyGenerators (projectiveFreeFamily R degree) d.J ≤
      (trivialCofibrations C).inverseImage (projectiveEvaluationFamily R degree s) := by
  intro X Y f hf
  obtain ⟨q, hq⟩ := (adjointFamilyGenerators_iff _ _ f).mp hf
  have hJ : d.J ≤ trivialCofibrations C := by
    have hl := d.J.le_llp_rlp
    rwa [d.J_rlp, fibrations_llp C] at hl
  have hBase := projectiveFreeAt_evaluated_trivialCofibration R hR (degree q.1) (degree s) q.2.1.hom (hJ _ q.2.2)
  exact ((trivialCofibrations C).arrow_iso_iff
    ((projectiveEvaluationFamily R degree s).mapArrow.mapIso (eqToIso hq))).mpr hBase

variable (e : CellularModuleGenerationRank d h)

local instance actualRankRegular : Fact e.cardinal.IsRegular := e.regular
/-- The actual ordinal bottom retained by the cellular source rank. -/
local instance actualRankBottom : OrderBot e.cardinal.ord.ToType := e.orderBot
local instance baseISmall : d.I.IsSmall.{w} := d.I_smallObject.isSmall
local instance baseJSmall : d.J.IsSmall.{w} := d.J_smallObject.isSmall

include hR in
/-- All six original free-I eligibility fields are derived at the actual common source rank. -/
theorem projectiveI_eligible :
    (adjointFamilyGenerators (projectiveFreeFamily R degree) d.I).IsCardinalForSmallObjectArgument e.cardinal := by
  apply adjointFamily_isCardinalForSmallObjectArgument
    (projectiveFreeFamily R degree) (projectiveEvaluationFamily R degree) (projectiveAdjunctionFamily R degree)
    d.I (cofibrations C) e.cardinal
  · have hI : d.I ≤ cofibrations C := by
      have hl := d.I.le_llp_rlp
      rwa [d.I_rlp, trivialFibrations_llp C] at hl
    exact projectiveGenerators_evaluation_cofibrations R hR degree d.I hI
  · intro A B f hf F _ hF
    exact CellularModuleGenerationRank.I_source_preservesColimit d h e ⟨Arrow.mk f, hf⟩ F hF

include hR in
/-- All six original free-J eligibility fields use the same produced rank and original base J maps. -/
theorem projectiveJ_eligible :
    (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).IsCardinalForSmallObjectArgument e.cardinal := by
  apply adjointFamily_isCardinalForSmallObjectArgument
    (projectiveFreeFamily R degree) (projectiveEvaluationFamily R degree) (projectiveAdjunctionFamily R degree)
    d.J (cofibrations C) e.cardinal
  · have hJ : d.J ≤ cofibrations C := by
      have hl := d.J.le_llp_rlp
      rw [d.J_rlp, fibrations_llp C] at hl
      exact hl.trans inf_le_left
    exact projectiveGenerators_evaluation_cofibrations R hR degree d.J hJ
  · intro A B f hf F _ hF
    exact CellularModuleGenerationRank.J_source_preservesColimit d h e ⟨Arrow.mk f, hf⟩ F hF

include hR e in
/-- The same original J small-object left class is weak at every retained original evaluation. -/
theorem projectiveJ_generatedLeft_weak :
    (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).rlp.llp ≤
      EvaluationTransfer.evaluationProperty (projectiveEvaluationFamily R degree) (weakEquivalences C) := by
  let _ : (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J).IsCardinalForSmallObjectArgument e.cardinal :=
    projectiveJ_eligible d h R hR degree e
  intro X Y f hf
  apply (EvaluationTransfer.evaluationProperty_iff (projectiveEvaluationFamily R degree) (weakEquivalences C) f).mpr
  intro s
  exact (rlp_llp_le_inverseImage_of_cardinal_closure
    (adjointFamilyGenerators (projectiveFreeFamily R degree) d.J) (trivialCofibrations C)
    (projectiveEvaluationFamily R degree s) e.cardinal
    (projectiveJGenerators_evaluation_trivialCofibrations d R hR degree s) f hf).2

end HomotopicalAlgebra.PositiveLevelModel.CellularProjective
