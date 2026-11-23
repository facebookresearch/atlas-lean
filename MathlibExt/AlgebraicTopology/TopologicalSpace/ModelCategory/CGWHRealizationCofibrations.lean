/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Original orthogonality proof credits: @toskua, Avocado.
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHRealizationLifting
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHCartesianMonoidalModel

/-!
# Native realization preserves cofibrations

The original simplicial realization functor preserves cofibrations and
trivial cofibrations in the selected native CGWH model structure. The
adjunction orthogonality proofs are shared with the cartesian model through
the focused realization-lifting producer.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory CategoryTheory.Functor
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped MonoidalCategory SSet.modelCategoryQuillen CGWH.modelCategory

namespace CGWH.modelCategory

/-- Direct native realization preserves every simplicial cofibration.
This uses the SAME shared adjunction orthogonality equality, with no
replacement model or source comparison witness. -/
public theorem toCGWH_map_cofibration
    {X Y : SSet.{v}} (f : X ⟶ Y) [Cofibration f] :
    Cofibration (SSet.toCGWH.{u, v}.map f) := by
  have hf : cofibrations SSet.{v} f :=
    (HomotopicalAlgebra.cofibration_iff f).mp (inferInstance : Cofibration f)
  have hm := (cofibrations SSet.{v}).map_mem_strictMap SSet.toCGWH.{u, v} f hf
  have h := ((cofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).le_llp_rlp _ hm
  rw [cgwhFreeCofibration_rlp_eq, trivialFibrations_llp] at h
  exact (HomotopicalAlgebra.cofibration_iff
    (SSet.toCGWH.{u, v}.map f)).mpr h

/-- Direct native realization preserves every simplicial trivial
cofibration through the SAME existing adjunction orthogonality proof. -/
public theorem toCGWH_map_mem_trivialCofibrations
    {X Y : SSet.{v}} (f : X ⟶ Y) (hf : trivialCofibrations SSet.{v} f) :
    trivialCofibrations CGWH.{u, v} (SSet.toCGWH.{u, v}.map f) := by
  have hm := (trivialCofibrations SSet.{v}).map_mem_strictMap SSet.toCGWH.{u, v} f hf
  have h := ((trivialCofibrations SSet.{v}).strictMap SSet.toCGWH.{u, v}).le_llp_rlp _ hm
  rw [cgwhFreeTrivialCofibration_rlp_eq, fibrations_llp] at h
  exact h

end CGWH.modelCategory
