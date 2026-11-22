/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealizationBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# Genuine all-mono cofibrations of the SAME quotient-cube realization

The SAME actual boundary map is its original monic latching-boundary
inclusion under both full original isomorphisms. Original scalar
boundary right-class recognition and the genuine adjunction then
give monicity of every SAME realized simplicial mono.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits HomotopicalAlgebra MorphismProperty
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- Every original simplicial boundary has its SAME realized map genuinely monic. -/
theorem boundary_map_mono (n : ℕ) : Mono (map (SSet.boundary.{u} n).ι) := by
  have h : Mono ((boundaryIso.{u} n).hom ≫ (RightCubeSupportBoundary.boundary n).ι) := inferInstance
  have h' : Mono (map (SSet.boundary.{u} n).ι ≫ (simplexIso ⦋n⦌).hom) :=
    boundaryIso_inclusion n ▸ h
  exact mono_of_mono (map (SSet.boundary.{u} n).ι) (simplexIso ⦋n⦌).hom

/-- The SAME original singular complex preserves genuine full scalar boundary right-class maps. -/
theorem singular_boundaryRLP {X Y : SSet.{u}} (p : X ⟶ Y) (hp : SSet.modelCategoryQuillen.I.rlp p) :
    SSet.modelCategoryQuillen.I.rlp (singular.map p) := by
  have hm : (monomorphisms SSet.{u}).rlp p := by rwa [SSet.rlp_monomorphisms]
  intro A B i hi
  obtain ⟨n⟩ := hi
  let _ : Mono (functor.map (SSet.boundary.{u} n).ι) := boundary_map_mono n
  exact (adjunction.hasLiftingProperty_iff (SSet.boundary.{u} n).ι p).mp
    (hm _ (show Mono (functor.map (SSet.boundary.{u} n).ι) from inferInstance))

/-- EVERY original simplicial mono has its SAME quotient-cube realization genuinely monic. -/
theorem map_mono {X Y : SSet.{u}} (i : X ⟶ Y) [Mono i] : Mono (map i) := by
  have h : (monomorphisms SSet.{u}).rlp.llp (map i) := by
    intro A B p hp
    have hSing := singular_boundaryRLP p (SSet.rlp_monomorphisms ▸ hp)
    have hM : (monomorphisms SSet.{u}).rlp (singular.map p) := by
      rwa [SSet.rlp_monomorphisms]
    exact (adjunction.hasLiftingProperty_iff i p).mpr (hM i inferInstance)
  have hEq : (monomorphisms SSet.{u}).rlp.llp = monomorphisms SSet.{u} := by
    rw [← SSet.modelCategoryQuillen.cofibrations_eq]
    rw [HomotopicalAlgebra.cofibrations_rlp]
    exact HomotopicalAlgebra.trivialFibrations_llp SSet.{u}
  exact (congrArg (fun W : MorphismProperty SSet.{u} => W (map i)) hEq).mp h

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
