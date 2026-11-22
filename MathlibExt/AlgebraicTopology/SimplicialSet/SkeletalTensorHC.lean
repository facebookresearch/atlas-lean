/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.SkeletalFiniteProductHC
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Tensor products and homotopy cartesian squares of simplicial sets

The simplicial tensor product is naturally isomorphic to the cartesian product, and tensoring a sharp map with an identity preserves sharpness. Tensoring a square by a finite simplicial set preserves its weak pullback-to-homotopy-pullback comparison when the right map is sharp.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkSkeletalProduct
open SharpComparisonDraft RezkCompatiblePushout

/-- The actual Cartesian tensor-to-product Iso for each original cell factor. -/
def tensorProductIso (X K : SSet.{u}) : X ⊗ K ≅ X ⨯ K :=
  (CartesianMonoidalCategory.tensorProductIsBinaryProduct X K).conePointUniqueUpToIso
    (limit.isLimit (pair X K))

/-- Tensor naturality retains both original factors and projections. -/
theorem tensorProductIso_naturality {X Y : SSet.{u}} (p : X ⟶ Y) (K : SSet.{u}) :
    (p ⊗ₘ 𝟙 K) ≫ (tensorProductIso Y K).hom =
      (tensorProductIso X K).hom ≫ prod.map p (𝟙 K) := by
  apply prod.hom_ext <;> simp [tensorProductIso, Category.assoc]

/-- Original tensor with the cell factor is sharp by actual product/pullback transport. -/
theorem tensor_map_sharp {X Y : SSet.{u}} (p : X ⟶ Y) (K : SSet.{u}) (hp : Sharp p) :
    Sharp (p ⊗ₘ 𝟙 K) := by
  let E : Arrow.mk (p ⊗ₘ 𝟙 K) ≅ Arrow.mk (prod.map p (𝟙 K)) :=
    Arrow.isoMk (tensorProductIso X K) (tensorProductIso Y K)
      (tensorProductIso_naturality p K).symm
  exact (SharpCoproductClosure.sharp_arrowIso_iff E).mpr (product_map_sharp p K hp)

/-- The actual original HC square with any finite simplex/boundary tensor factor. -/
theorem finite_tensor_hc {A X B Y K : SSet.{u}}
    {f : A ⟶ X} {s : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f s p g) (hp : Sharp p) [K.Finite]
    (hc : WeakEquivalence (pullback.lift f s sq.w ≫ comparison p g)) :
    WeakEquivalence
      (pullback.lift (f ⊗ₘ 𝟙 K) (s ⊗ₘ 𝟙 K) (by
        simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
        rw [sq.w]) ≫ comparison (p ⊗ₘ 𝟙 K) (g ⊗ₘ 𝟙 K)) := by
  let tensorSquare : CommSq (f ⊗ₘ 𝟙 K) (s ⊗ₘ 𝟙 K) (p ⊗ₘ 𝟙 K) (g ⊗ₘ 𝟙 K) :=
    CommSq.mk (by
      simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
      rw [sq.w])
  let productSquare : CommSq (prod.map f (𝟙 K)) (prod.map s (𝟙 K))
      (prod.map p (𝟙 K)) (prod.map g (𝟙 K)) := CommSq.mk (by
    apply prod.hom_ext
    · simpa only [Category.assoc, prod.map_fst, prod.map_fst_assoc] using
        congrArg (fun z => (prod.fst : A ⨯ K ⟶ A) ≫ z) sq.w
    · simp)
  have productHC := finite_product_hc (K := K) sq hp hc
  exact (hc_weakSquare_iff tensorSquare productSquare
    (tensorProductIso A K).hom (tensorProductIso X K).hom
    (tensorProductIso B K).hom (tensorProductIso Y K).hom
    (tensorProductIso_naturality f K) (tensorProductIso_naturality s K)
    (tensorProductIso_naturality p K) (tensorProductIso_naturality g K)
    (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)).mpr productHC

end SSet.RezkSkeletalProduct
