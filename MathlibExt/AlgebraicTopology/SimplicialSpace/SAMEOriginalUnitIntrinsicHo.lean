/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Intrinsic homotopy equivalence of the original completion unit.
import MathlibExt.AlgebraicTopology.SimplicialSpace.SAMECompletionSegalFromOriginalAllVertexImage
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHoEssentialSurjectivity
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHomotopyFunctor

/-!
# Homotopy-category equivalence of the completion unit

For a Segal space, the designated completion unit is weak on every prescribed mapping fibre and
induces an equivalence of intrinsic homotopy categories. Degree-zero component coverage
constructs essential-surjectivity witnesses, and the completion's Segal structure is supplied by
the preceding construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.RezkCompletionData

/-- Actual original Unit component surjectivity constructs intrinsic Ho essential
surjectivity after target Segalness has been derived, without any supplied Ho outcome. -/
theorem unit_intrinsicHo_essSurj (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.map (unit.app W) hW
      (RezkCompletionAllVertex.sameCompletion_segal W hW)).EssSurj :=
  SegalHomotopy.map_essSurj_of_componentSurjective (unit.app W) hW
    (RezkCompletionAllVertex.sameCompletion_segal W hW) (unit_components_surjective W 0)

/-- The same actual Unit is an intrinsic Ho equivalence from its derived full
mapping-fibre weakness and internally constructed essential-surjectivity witnesses. -/
theorem unit_intrinsicHo_isEquivalence (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (SegalHomotopy.map (unit.app W) hW
      (RezkCompletionAllVertex.sameCompletion_segal W hW)).IsEquivalence :=
  SegalHomotopy.map_isEquivalence_of_mappingFibreWeak_of_essSurj (unit.app W) hW
    (RezkCompletionAllVertex.sameCompletion_segal W hW)
    (RezkCompletionCoreDiagonal.sameOriginalUnit_mappingFibre_weak W hW)
    (unit_intrinsicHo_essSurj W hW)

/-- Both intrinsic certificates retain the literal original Unit and all actual
prescribed mapping fibres. No all-CSS-testing equivalence is assumed or supplied. -/
theorem unit_full_mapping_fibres_and_intrinsicHo (W : SimplicialSpace.{u}) (hW : segalSpaces W) :
    (∀ x y : (W.diagram _⦋0⦌) _⦋0⦌, SSet.realizationWeakEquivalences
      (mappingFibre.map (unit.app W) (x := x) (y := y) rfl rfl)) ∧
    (SegalHomotopy.map (unit.app W) hW
      (RezkCompletionAllVertex.sameCompletion_segal W hW)).IsEquivalence :=
  ⟨RezkCompletionCoreDiagonal.sameOriginalUnit_mappingFibre_weak W hW,
    unit_intrinsicHo_isEquivalence W hW⟩

end SimplicialSpace.RezkCompletionData
