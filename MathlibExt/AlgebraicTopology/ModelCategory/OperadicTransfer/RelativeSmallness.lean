/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.Basic
import MathlibExt.CategoryTheory.Operad.Tensor.FreeGeneratingSourceSmallness

/-!
# Presentable original free operadic sources

The actual color-supported I/J endpoint families are small. The existing
free-source presentability theorem supplies a common regular upper rank from
the original locally presentable coefficient category and actual filtered
colimit creation. The same free arrows have complete small-object eligibility
at that rank once the ordinary target colimit constructions are available.

This file remains classic to reuse the existing classic source-smallness API
without changing its source or forcing unrelated consumer migrations.
-/

set_option autoImplicit false
noncomputable section

universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject Opposite
open CategoryTheory.Operad CategoryTheory.Operad.Tensor

namespace HomotopicalAlgebra.OperadicTransfer

variable (S : SourceContext.{uW, v, u, us})

/-- Use the original finite tensor operations for the generating-source bounds. -/
local instance smallnessOriginalFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance smallnessOriginalTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance smallnessOriginalProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

/-- The produced regular rank retains the original lower bound and every original free endpoint. -/
structure PresentableFreeSourceBounds (O : ColoredOperadObj S.W S.C)
    (I J : MorphismProperty S.C) (κ₀ : Cardinal.{us}) where
  /-- The common presentability rank. -/
  cardinal : Cardinal.{us}
  /-- Regularity of the same rank. -/
  regular : Fact cardinal.IsRegular
  /-- The caller's original rank is retained as a lower bound. -/
  original_le : κ₀ ≤ cardinal
  /-- Both source and target endpoint families are the original supported free objects. -/
  endpoints_presentable : letI := regular;
    ∀ s, IsCardinalPresentable ((freeAlgebraFunctor O).obj
      (FreeGeneratingSource.endpoint
        (SemiModel.ColorSource.colorGenerators S.C S.W I)
        (SemiModel.ColorSource.colorGenerators S.C S.W J) s)) cardinal
  /-- The original free-I sources have complete uniform relative-cell smallness. -/
  I_relative : UniformRelativeSourceSmallness.{us} (freeGenerators S O I)
  /-- The original free-J sources have that same source-smallness predicate. -/
  J_relative : UniformRelativeSourceSmallness.{us} (freeGenerators S O J)

/-- Original local presentability and filtered-colimit creation produce free source bounds. -/
def presentableFreeSourceBounds (O : ColoredOperadObj S.W S.C)
    (I J : MorphismProperty S.C) [I.IsSmall.{us}] [J.IsSmall.{us}]
    [IsLocallyPresentable.{us} S.C]
    (κ₀ : Cardinal.{us}) [Fact κ₀.IsRegular] : PresentableFreeSourceBounds S O I J κ₀ := by
  let : (SemiModel.ColorSource.colorGenerators S.C S.W I).IsSmall.{us} :=
    SemiModel.ColorSource.colorGenerators_isSmall S.C S.W I
  let : (SemiModel.ColorSource.colorGenerators S.C S.W J).IsSmall.{us} :=
    SemiModel.ColorSource.colorGenerators_isSmall S.C S.W J
  apply Classical.choice
  obtain ⟨κ, hκ, hκ₀, hEndpoints, hI, hJ⟩ :=
    S.exists_operadicUniformFreeSourceSmallness O
      (SemiModel.ColorSource.colorGenerators S.C S.W I)
      (SemiModel.ColorSource.colorGenerators S.C S.W J) κ₀
  exact ⟨{
    cardinal := κ
    regular := hκ
    original_le := hκ₀
    endpoints_presentable := hEndpoints
    I_relative := hI
    J_relative := hJ }⟩

namespace PresentableFreeSourceBounds

variable {S} {O : ColoredOperadObj S.W S.C} {I J : MorphismProperty S.C}
  {κ₀ : Cardinal.{us}} (d : PresentableFreeSourceBounds S O I J κ₀)

/-- Every actual original free-I domain is presentable at the stored rank. -/
theorem I_sources_presentable : letI := d.regular;
    ∀ p : (freeGenerators S O I).toSet, IsCardinalPresentable p.1.left d.cardinal := by
  let := d.regular
  rintro ⟨⟨_, _, f⟩, hf⟩
  change ((SemiModel.ColorSource.colorGenerators S.C S.W I).strictMap
    (freeAlgebraFunctor O)) f at hf
  cases hf with
  | map hf => exact d.endpoints_presentable (.inl ⟨Arrow.mk _, hf⟩, false)

/-- Every actual original free-J domain is presentable at the same stored rank. -/
theorem J_sources_presentable : letI := d.regular;
    ∀ p : (freeGenerators S O J).toSet, IsCardinalPresentable p.1.left d.cardinal := by
  let := d.regular
  rintro ⟨⟨_, _, f⟩, hf⟩
  change ((SemiModel.ColorSource.colorGenerators S.C S.W J).strictMap
    (freeAlgebraFunctor O)) f at hf
  cases hf with
  | map hf => exact d.endpoints_presentable (.inr ⟨Arrow.mk _, hf⟩, false)

variable [OrderBot d.cardinal.ord.ToType]
  [LocallySmall.{us} (Algebra O)] [HasPushouts (Algebra O)] [HasCoproducts.{us} (Algebra O)]
  [HasIterationOfShape d.cardinal.ord.ToType (Algebra O)]

/-- The actual free-I family has all six small-object fields at the stored original rank. -/
theorem I_smallObject [I.IsSmall.{us}] : letI := d.regular;
    (freeGenerators S O I).IsCardinalForSmallObjectArgument d.cardinal := by
  let := d.regular
  let : (freeGenerators S O I).IsSmall.{us} := freeGenerators_isSmall S O I
  exact FreeGeneratingSource.eligibility_of_presentable_sources
    (freeGenerators S O I) d.cardinal d.I_sources_presentable

/-- The same rank and actual ordinal bottom supply all six free-J fields. -/
theorem J_smallObject [J.IsSmall.{us}] : letI := d.regular;
    (freeGenerators S O J).IsCardinalForSmallObjectArgument d.cardinal := by
  let := d.regular
  let : (freeGenerators S O J).IsSmall.{us} := freeGenerators_isSmall S O J
  exact FreeGeneratingSource.eligibility_of_presentable_sources
    (freeGenerators S O J) d.cardinal d.J_sources_presentable

end PresentableFreeSourceBounds


end HomotopicalAlgebra.OperadicTransfer
