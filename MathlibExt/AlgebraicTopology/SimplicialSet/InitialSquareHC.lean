/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.EmptyFaceTensorPullback

/-!
# Homotopy cartesian squares with initial left objects

A commutative square whose two left objects are initial has a weak pullback-to-homotopy-pullback comparison whenever its right map is sharp. The initiality hypotheses determine the square equation and allow arbitrary maps from those initial objects.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped Simplicial SSet.modelCategoryQuillen

namespace SSet.RezkEmptyFace
open SharpComparisonDraft RezkCompatiblePushout

/-- Actual initial source and target objects give the empty square HC.
Both original objects and all four original maps are retained by the two
initial-object Isos. No axiom, empty-record or body exemption is used. -/
theorem initialSquare_hc {A B X Y : SSet.{u}} (hA : IsInitial A) (hB : IsInitial B)
    (f : A ⟶ X) (i : A ⟶ B) (p : X ⟶ Y) (g : B ⟶ Y) (hp : Sharp p) :
    WeakEquivalence (pullback.lift f i (hA.hom_ext _ _) ≫ comparison p g) := by
  let E : SSet.{u} := Δ[0] ⊗ ((⊥ : (Δ[0] : SSet.{u}).Subcomplex) : SSet.{u})
  let hE : IsInitial E := emptyTensorInitial Δ[0] 0
  let eA : A ≅ E := hA.uniqueUpToIso hE
  let eB : B ≅ E := hB.uniqueUpToIso hE
  let f' := eA.inv ≫ f
  let i' := eA.inv ≫ i ≫ eB.hom
  let g' := eB.inv ≫ g
  let old : CommSq f i p g := CommSq.mk (hA.hom_ext _ _)
  let new : CommSq f' i' p g' := CommSq.mk (hE.hom_ext _ _)
  have actual := emptyTensor_hc f' i' p g' hp
  exact (hc_weakSquare_iff old new eA.hom (𝟙 X) eB.hom (𝟙 Y)
    (by simp [f']) (by simp [i'])
    (by simp) (by simp [g'])
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr actual

end SSet.RezkEmptyFace
