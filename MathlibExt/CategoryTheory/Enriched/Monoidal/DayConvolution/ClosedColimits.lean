/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.Closed
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.BraidingMonoidal

/-!
# Colimit preservation by the actual enriched Day tensors

These proof families use the constructed right-translation end adjunction
directly. Right tensor preservation uses the actual coend braiding. Naming
the families permits native module constructions to retain their exact
prerequisite witnesses without rebuilding closed instances at each projection.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uV vV uI vI w z

open CategoryTheory Limits MonoidalCategory BraidedCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedDayKernel.Closed

attribute [local instance] Enriched.prodCategory ColimitMonoidal.smallestColimits

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (d : EnrichedMonoidalCategoryData V I)

/-- The selected left tensor preserves all colimit shapes by its constructed end adjunction. -/
theorem leftTensorPreserves (F : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    PreservesColimitsOfSize.{w, z} (tensorLeft F) := by
  let := ColimitMonoidal.monoidalCategory d
  change PreservesColimitsOfSize.{w, z} (leftFunctor d F)
  exact (adjunction d F).leftAdjoint_preservesColimits

variable [SymmetricCategory I] (b : EnrichedBraidedMonoidalCategoryData V I d)

include b in
/-- The selected right tensor preserves all colimit shapes through the original Day braid. -/
theorem rightTensorPreserves (F : EnrichedFunctorCat V I) :
    letI := ColimitMonoidal.monoidalCategory d
    PreservesColimitsOfSize.{w, z} (tensorRight F) := by
  let := ColimitMonoidal.monoidalCategory d
  let := BraidingMonoidal.symmetricCategory d b
  have h : tensorLeft F ⊣ rightFunctor d F := by
    change leftFunctor d F ⊣ rightFunctor d F
    exact adjunction d F
  exact (h.ofNatIsoLeft (tensorLeftIsoTensorRight F)).leftAdjoint_preservesColimits

include b in
/-- Both complete native small-colimit preservation supplier functions come from the actual
constructed end adjunction and original coend braid. -/
theorem smallTensorPreservationFamilies :
    letI := ColimitMonoidal.monoidalCategory d
    (∀ F : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft F)) ∧
      (∀ F : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight F)) := by
  exact ⟨leftTensorPreserves d, rightTensorPreserves d b⟩

end CategoryTheory.EnrichedDayKernel.Closed
