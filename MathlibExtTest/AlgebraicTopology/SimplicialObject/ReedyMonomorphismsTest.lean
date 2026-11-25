/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialObject.ReedyModelCategory
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Consumers of the raw Reedy monomorphism theorem
-/

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject.ReedyMonomorphismsTest

/-- Consume the equality under the actual existing Kan and Reedy models. -/
theorem native_reedy_cofibration_iff_mono
    {X Y : SimplicialObject SSet.{u}} (f : X ⟶ Y) :
    let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
    let _ : ModelCategory (SimplicialObject SSet.{u}) :=
      CategoryTheory.SimplicialObject.reedyModelCategory
    Cofibration f ↔ Mono f := by
  let _ : ModelCategory SSet.{u} := SSet.modelCategoryQuillen.modelCategory
  let _ : ModelCategory (SimplicialObject SSet.{u}) :=
    CategoryTheory.SimplicialObject.reedyModelCategory
  dsimp only
  rw [HomotopicalAlgebra.cofibration_iff]
  change reedyLeft (MorphismProperty.monomorphisms SSet.{u}) f ↔ Mono f
  rw [reedyLeft_monomorphisms_eq]

/-- The original relative map is monic with both original injection equations. -/
theorem relative_map_and_legs {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) [Mono f] (n : ℕ) :
    Mono (relativeLatchingMap f n) ∧
      pushout.inl (latchingMap X n) ((latchingObjectFunctor n).map f) ≫
          relativeLatchingMap f n = f.app (op ⦋n⦌) ∧
      pushout.inr (latchingMap X n) ((latchingObjectFunctor n).map f) ≫
          relativeLatchingMap f n = latchingMap Y n := by
  have hr : reedyLeft (MorphismProperty.monomorphisms SSet.{u}) f := by
    rw [reedyLeft_monomorphisms_eq]
    exact inferInstance
  exact ⟨hr n, relativeLatchingMap_inl f n, relativeLatchingMap_inr f n⟩

/-- Degree zero is included without a nonempty latching index. -/
theorem relative_zero_mono {X Y : SimplicialObject SSet.{u}}
    (f : X ⟶ Y) [Mono f] : Mono (relativeLatchingMap f 0) :=
  (relative_map_and_legs f 0).1

end CategoryTheory.SimplicialObject.ReedyMonomorphismsTest
