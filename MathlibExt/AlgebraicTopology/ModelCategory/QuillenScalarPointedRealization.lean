/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHPointedAdjunctionRecords
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.CGWHRealizationUnitWeak
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure

/-!
# The actual scalar pointed realization Quillen adjunction

The original native CGWH right classes are the same underlying TopCat
right classes. Their actual singular images therefore satisfy the proved
TopCat Quillen laws. The unchanged pointed functor records and created
under-model classes earn pointed Quillenness. Its original whole unit is
weak by the saved arbitrary-source native realization-unit theorem.
No local presentability or uniform-smallness assertion is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen TopCat.modelCategory CGWH.modelCategory

namespace HomotopicalAlgebra.QuillenScalarPointedRealization

/-- The unchanged native singular functor preserves the actual original fibrations. -/
theorem singular_preservesFibrations : PreservesFibrations
    (C := CGWH.{u, v}) (D := SSet.{v}) (CGWH.cgwhToTop ⋙ TopCat.toSSet) := by
  intro X Y f hf
  have hTop : fibrations TopCat.{v} (CGWH.cgwhToTop.map f) := by
    change TopCat.realizedHornInclusions.rlp (CGWH.cgwhToTop.map f) at hf ⊢
    exact hf
  exact Adjunction.IsQuillenAdjunction.preservesFibrations (adj := sSetTopAdj) _ hTop

/-- The same native singular functor preserves the complete actual original trivial-fibration class. -/
theorem singular_preservesTrivialFibrations : PreservesTrivialFibrations
    (C := CGWH.{u, v}) (D := SSet.{v}) (CGWH.cgwhToTop ⋙ TopCat.toSSet) := by
  intro X Y f hf
  have hTop : trivialFibrations TopCat.{v} (CGWH.cgwhToTop.map f) := by
    change TopCat.realizedHornInclusions.rlp (CGWH.cgwhToTop.map f) ∧
      TopCat.weakHomotopyEquivalences (CGWH.cgwhToTop.map f) at hf ⊢
    exact hf
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := sSetTopAdj) _ hTop

/-- The complete unchanged pointed singular functor preserves the original created fibrations. -/
theorem pointedSingular_preservesFibrations : PreservesFibrations
    (C := PointedCGWH.{u, v}) (D := Under (Δ[0] : SSet.{v})) CGWH.pointedToSSet := by
  intro X Y f hf
  rw [fibrations_under_def] at hf ⊢
  change fibrations CGWH.{u, v} f.right at hf
  change fibrations SSet.{v} (TopCat.toSSet.map (CGWH.cgwhToTop.map f.right))
  exact singular_preservesFibrations _ hf

/-- Both full original pointed right classes are preserved by the same actual singular maps. -/
theorem pointedSingular_preservesTrivialFibrations : PreservesTrivialFibrations
    (C := PointedCGWH.{u, v}) (D := Under (Δ[0] : SSet.{v})) CGWH.pointedToSSet := by
  intro X Y f hf
  rw [trivialFibrations_under_eq] at hf ⊢
  change trivialFibrations CGWH.{u, v} f.right at hf
  change trivialFibrations SSet.{v} (TopCat.toSSet.map (CGWH.cgwhToTop.map f.right))
  exact singular_preservesTrivialFibrations _ hf

/-- The actual original pointed realization/singular adjunction is Quillen for the original models. -/
theorem isQuillen : SSet.pointedToCGWHAdjunction.{u, v}.IsQuillenAdjunction :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (adj := SSet.pointedToCGWHAdjunction) pointedSingular_preservesFibrations
      pointedSingular_preservesTrivialFibrations

/-- Every original pointed unit retains its actual native arbitrary-source weak underlying map. -/
theorem unit_weak (K : Under (Δ[0] : SSet.{v})) :
    weakEquivalences (Under (Δ[0] : SSet.{v})) (SSet.pointedToCGWHAdjunction.{u, v}.unit.app K) := by
  rw [weakEquivalences_under_def]
  change SSet.realizationWeakEquivalences (SSet.pointedToCGWHAdjunction.{u, v}.unit.app K).right
  rw [SSet.CGWHPointedAdjunctionRecords.unit_right]
  exact SSet.realizationWeakEquivalences_sSetCGWHAdj_unit K.right

end HomotopicalAlgebra.QuillenScalarPointedRealization
