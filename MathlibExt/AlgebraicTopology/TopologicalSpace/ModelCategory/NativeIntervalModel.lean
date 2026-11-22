/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.NativeIntervalArrows
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHModelStructure
public import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen

/-!
# Actual native interval classes from the original generators

The existing CGWH model and its inherited pointed model are selected
explicitly. Each original endpoint is transported from its actual original
costar horn through the whole proved Arrow isomorphism. The augmentation is
weak by the original endpoint section and two out of three. No model,
acyclicity, localization, or cylinder dictionary is supplied.

This follows the legacy importing route of the existing Quillen interface.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits MorphismProperty MonoidalCategory
open HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.IntervalCoefficient

/-- Every original costar horn is an actual native pointed acyclic cofibration. -/
theorem originalHorn_trivialCofibration (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations PointedCGWH.{u, v}
      ((Under.costar CGWH.point.{u, v}).map (CGWH.realizedHornInclusion.{v, u} n i)) := by
  have h : CGWH.realizedHornInclusions.{u, v}.rlp.llp
      (CGWH.realizedHornInclusion.{v, u} n i) :=
    CGWH.realizedHornInclusions.le_llp_rlp _ (CGWH.horn_mem_realizedHornInclusions n i)
  change CGWH.cofibrantGenerationData.{u, v}.J.rlp.llp
    (CGWH.realizedHornInclusion.{v, u} n i) at h
  rw [CGWH.cofibrantGenerationData.J_rlp, fibrations_llp] at h
  exact (Under.costarAdjForget_isQuillenAdjunction CGWH.point.{u, v}).preservesTrivialCofibrations
    _ h

/-- Both actual original interval endpoints are native pointed acyclic cofibrations. -/
theorem endpoint_trivialCofibration (i : Fin 2) :
    trivialCofibrations PointedCGWH.{u, v} (endpoint i) :=
  (endpoint_property_iff (trivialCofibrations PointedCGWH.{u, v}) i).mpr
    (originalHorn_trivialCofibration 0 i.rev)

/-- Each original native interval endpoint is a cofibration in the actual selected model. -/
theorem endpoint_cofibration (i : Fin 2) : Cofibration (endpoint.{u, v} i) :=
  (HomotopicalAlgebra.cofibration_iff _).mpr (endpoint_trivialCofibration i).1

/-- Each original native interval endpoint is weak in the actual selected model. -/
theorem endpoint_weakEquivalence (i : Fin 2) : WeakEquivalence (endpoint.{u, v} i) :=
  (HomotopicalAlgebra.weakEquivalence_iff _).mpr (endpoint_trivialCofibration i).2

/-- The literal original augmentation is weak, using the same endpoint section. -/
theorem augmentation_weakEquivalence : WeakEquivalence augmentation.{u, v} := by
  let _ : WeakEquivalence (endpoint.{u, v} 0) := endpoint_weakEquivalence 0
  exact weakEquivalence_of_precomp_of_fac (endpoint_augmentation 0)

/-- The original endpoint weakness is the actual native CGWH weak class on its right map. -/
theorem endpoint_nativeWeak (i : Fin 2) :
    CGWH.weakHomotopyEquivalences.{u, v} (endpoint.{u, v} i).right :=
  (CGWH.modelCategory.weakEquivalence_iff _).mp
    ((PointedCGWH.weakEquivalence_iff _).mp (endpoint_weakEquivalence i))

/-- The original augmentation weakness is the actual native CGWH weak class on its right map. -/
theorem augmentation_nativeWeak :
    CGWH.weakHomotopyEquivalences.{u, v} augmentation.{u, v}.right :=
  (CGWH.modelCategory.weakEquivalence_iff _).mp
    ((PointedCGWH.weakEquivalence_iff _).mp augmentation_weakEquivalence)

end PointedCGWH.IntervalCoefficient
