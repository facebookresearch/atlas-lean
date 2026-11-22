/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CartesianMonoidal
public import MathlibExt.Topology.Category.CGWH.Reflection
public import MathlibExt.Topology.Category.CompactlyGenerated.ClosedEmbeddingProduct

/-!
# Closed embeddings and the native CGWH product

The inclusion into compactly generated spaces preserves finite products as
the right adjoint of weak-Hausdorff reflection. Its actual product comparison
transports the existing closed-embedding theorem for native products.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory Topology

namespace CGWH

/-- The selected native product map of two closed embeddings is a closed
embedding. No ordinary product-topology identification is required. -/
theorem isClosedEmbedding_prodMap {A B X Y : CGWH.{u, v}}
    (f : A ⟶ B) (g : X ⟶ Y)
    (hf : IsClosedEmbedding (ConcreteCategory.hom f))
    (hg : IsClosedEmbedding (ConcreteCategory.hom g)) :
    IsClosedEmbedding (ConcreteCategory.hom (f ⊗ₘ g)) := by
  let F := cgwhToCompactlyGenerated.{u, v}
  let _ : F.IsRightAdjoint := weakHausdorffificationAdjunction.isRightAdjoint
  let _ : PreservesFiniteProducts F := inferInstance
  let eAX := CartesianMonoidalCategory.prodComparisonIso F A X
  let eBY := CartesianMonoidalCategory.prodComparisonIso F B Y
  have hProduct : IsClosedEmbedding (ConcreteCategory.hom (F.map f ⊗ₘ F.map g)) :=
    CompactlyGenerated.isClosedEmbedding_prodMap (F.map f) (F.map g) hf hg
  have hMap : F.map (f ⊗ₘ g) =
      eAX.hom ≫ (F.map f ⊗ₘ F.map g) ≫ eBY.inv := by
    apply (cancel_mono eBY.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact CartesianMonoidalCategory.prodComparison_natural F f g
  have hClosed := (CompactlyGenerated.homeoOfIso eBY.symm).isClosedEmbedding.comp
    (hProduct.comp (CompactlyGenerated.homeoOfIso eAX).isClosedEmbedding)
  change IsClosedEmbedding
    (ConcreteCategory.hom (eAX.hom ≫ (F.map f ⊗ₘ F.map g) ≫ eBY.inv)) at hClosed
  rw [← hMap] at hClosed
  exact hClosed

end CGWH
