/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalTensorHC

/-!
# Pullback squares formed by product and tensor maps

For arbitrary maps of simplicial sets, the square formed by taking their cartesian products with identities is a pullback. Under the tensor-product identification, its pullback-to-homotopy-pullback comparison is a weak equivalence whenever the coefficient map is sharp.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalProduct
open SharpComparisonDraft RezkCompatiblePushout

/-- The two independent product coordinates form the actual strict boundary square. -/
theorem product_boundary_isPullback {X Y B K : SSet.{u}} (p : X ⟶ Y) (b : B ⟶ K) :
    IsPullback (prod.map (𝟙 X) b) (prod.map p (𝟙 B))
      (prod.map p (𝟙 K)) (prod.map (𝟙 Y) b) where
  w := by simp
  isLimit' := by
    refine ⟨PullbackCone.IsLimit.mk (by simp)
      (fun s => prod.lift (s.fst ≫ prod.fst) (s.snd ≫ prod.snd)) ?_ ?_ ?_⟩
    · intro s
      apply prod.hom_ext
      · simp [Category.assoc]
      · simpa only [Category.assoc, prod.lift_snd, prod.lift_snd_assoc, prod.map_snd,
          prod.map_snd_assoc, Category.comp_id] using
          (congrArg (fun z => z ≫ prod.snd) s.condition).symm
    · intro s
      apply prod.hom_ext
      · simpa only [Category.assoc, prod.lift_fst, prod.lift_fst_assoc, prod.map_fst,
          prod.map_fst_assoc, Category.comp_id] using
          congrArg (fun z => z ≫ prod.fst) s.condition
      · simp [Category.assoc]
    · intro s m hf hs
      apply prod.hom_ext
      · simpa only [Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id] using
          congrArg (fun z => z ≫ prod.fst) hf
      · simpa only [Category.assoc, prod.lift_snd, prod.map_snd, Category.comp_id] using
          congrArg (fun z => z ≫ prod.snd) hs

/-- The actual tensor boundary square is HC from factor Sharp and the strict
product square; no product/tensor boundary HC assertion is supplied. -/
theorem tensor_boundary_hc {X Y B K : SSet.{u}} (p : X ⟶ Y) (b : B ⟶ K) (hp : Sharp p) :
    WeakEquivalence
      (pullback.lift (X ◁ b) (p ▷ B) (by
        simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
          Category.id_comp, Category.comp_id]) ≫
        comparison (p ▷ K) (Y ◁ b)) := by
  let tensorSquare : CommSq (X ◁ b) (p ▷ B) (p ▷ K) (Y ◁ b) := CommSq.mk (by
    simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id])
  let productSquare := product_boundary_isPullback p b
  have hproduct := strictSquare_hc productSquare (product_map_sharp p K hp)
  exact (hc_weakSquare_iff tensorSquare productSquare.toCommSq
    (tensorProductIso X B).hom (tensorProductIso X K).hom
    (tensorProductIso Y B).hom (tensorProductIso Y K).hom
    (by apply prod.hom_ext <;> simp [tensorProductIso, Category.assoc])
    (tensorProductIso_naturality p B) (tensorProductIso_naturality p K)
    (by apply prod.hom_ext <;> simp [tensorProductIso, Category.assoc])
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr hproduct

end SSet.RezkSkeletalProduct
