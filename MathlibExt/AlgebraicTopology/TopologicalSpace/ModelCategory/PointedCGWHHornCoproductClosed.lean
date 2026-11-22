/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingCoproducts
public import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingSmash
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHHornCoproductAction
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellPushouts
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Closed native attaching coproducts of arbitrary pointed horn tensors

The individual native horn maps are closed, free basepoint preserves that
closed embedding, and arbitrary smash factors preserve it. The actual pointed
coproduct theorem then supplies closedness with the shared point and empty
family. Both original attaching cofans and every actual native pushout leg are
retained. No coefficient cofibrancy or weak-equivalence premise is supplied.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory Topology
open scoped Simplicial

namespace PointedCGWH

private theorem nativeHorn_isClosedEmbedding (n : ℕ) (i : Fin (n + 2)) :
    IsClosedEmbedding (ConcreteCategory.hom (CGWH.realizedHornInclusion.{v, u} n i)) := by
  let P := CGWH.realizedBoundaryInclusions.{u, v} ⊔ CGWH.realizedHornInclusions.{u, v}
  have h : P (CGWH.realizedHornInclusion.{v, u} n i) :=
    Or.inr (CGWH.horn_mem_realizedHornInclusions n i)
  exact CGWH.coproducts_realizedGenerators_le_closedEmbeddings _
    (P.le_coproducts _ h)

/-- The actual freely pointed horn tensor with an arbitrary coefficient is closed. -/
theorem freePointHornTensorInclusion_isClosedEmbedding
    (n : ℕ) (i : Fin (n + 2)) (K : PointedCGWH.{u, v}) :
    IsClosedEmbedding (ConcreteCategory.hom
      (((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} n i)) ⊗ₘ
        𝟙 K).right) := by
  rw [tensorHom_id]
  exact isClosedEmbedding_whiskerRight _ K
    (isClosedEmbedding_costarMap _ (nativeHorn_isClosedEmbedding n i))

private theorem closed_cobaseChange
    {A X Y P : PointedCGWH.{u, v}} {i : A ⟶ X} {f : A ⟶ Y}
    {g : X ⟶ P} {j : Y ⟶ P} (h : IsPushout i f g j)
    (hi : IsClosedEmbedding (ConcreteCategory.hom i.right)) :
    IsClosedEmbedding (ConcreteCategory.hom j.right) := by
  let U := pointedToCGWH.{u, v}
  let hU : IsPushout i.right f.right g.right j.right := h.map U
  let e := hU.isoIsPushout _ _ (IsPushout.of_hasPushout i.right f.right)
  have he : j.right ≫ e.hom = pushout.inr i.right f.right :=
    hU.inr_isoIsPushout_hom _ _ (IsPushout.of_hasPushout i.right f.right)
  have hClosed : IsClosedEmbedding (ConcreteCategory.hom (j.right ≫ e.hom)) := by
    rw [he]
    exact CGWH.isClosedEmbedding_pushout_inr i.right f.right hi
  exact (TopCat.closedEmbeddings.cancel_right_of_respectsIso
    (CGWH.cgwhToTop.map j.right) (CGWH.cgwhToTop.mapIso e).hom).mp hClosed

variable (J : Type v) (n : J → ℕ) (i : ∀ a, Fin (n a + 2))
  (K : J → PointedCGWH.{u, v})

/-- The original native pointed coproduct of all arbitrary horn-tensor maps is closed. -/
theorem freePointHornTensorCoproductInclusion_isClosedEmbedding :
    IsClosedEmbedding (ConcreteCategory.hom
      (freePointHornTensorCoproductInclusion J n i K).right) := by
  apply isClosedEmbedding_coproductMap
  intro a
  exact freePointHornTensorInclusion_isClosedEmbedding (n a) (i a) (K a)

/-- The actual new leg of any native pointed pushout of that coproduct is closed. -/
theorem freePointHornTensorCoproduct_cobaseChange_isClosedEmbedding
    {Y P : PointedCGWH.{u, v}}
    {f : freePointHornTensorCoproductSource J n i K ⟶ Y}
    {g : freePointHornTensorCoproductTarget J n K ⟶ P} {j : Y ⟶ P}
    (h : IsPushout (freePointHornTensorCoproductInclusion J n i K) f g j) :
    IsClosedEmbedding (ConcreteCategory.hom j.right) :=
  closed_cobaseChange h (freePointHornTensorCoproductInclusion_isClosedEmbedding J n i K)

/-- Both supplied original cofans induce the same closed horn-tensor attaching map. -/
theorem freePointHornTensorCofanMap_isClosedEmbedding
    (cA : Cofan (fun a => (Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (SSet.horn.{v} (n a + 1) (i a))) ⊗ K a))
    (cB : Cofan (fun a => (Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a))
    (hA : IsColimit cA) (hB : IsColimit cB) (m : cA.pt ⟶ cB.pt)
    (hm : ∀ a, cA.inj a ≫ m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)) ≫ cB.inj a) :
    IsClosedEmbedding (ConcreteCategory.hom m.right) :=
  isClosedEmbedding_cofanMap _ _ _ cA cB hA hB m hm
    (fun a => freePointHornTensorInclusion_isClosedEmbedding (n a) (i a) (K a))

/-- Closedness holds on the actual new leg, without replacing either original cofan. -/
theorem freePointHornTensorCofan_cobaseChange_isClosedEmbedding
    (cA : Cofan (fun a => (Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (SSet.horn.{v} (n a + 1) (i a))) ⊗ K a))
    (cB : Cofan (fun a => (Under.costar CGWH.point.{u, v}).obj
      (SSet.toCGWHOfFinite (Δ[n a + 1] : SSet.{v})) ⊗ K a))
    (hA : IsColimit cA) (hB : IsColimit cB) (m : cA.pt ⟶ cB.pt)
    (hm : ∀ a, cA.inj a ≫ m =
      ((Under.costar CGWH.point).map (CGWH.realizedHornInclusion.{v, u} (n a) (i a)) ⊗ₘ
        𝟙 (K a)) ≫ cB.inj a)
    {Y P : PointedCGWH.{u, v}} {f : cA.pt ⟶ Y} {g : cB.pt ⟶ P} {j : Y ⟶ P}
    (h : IsPushout m f g j) :
    IsClosedEmbedding (ConcreteCategory.hom j.right) :=
  closed_cobaseChange h (freePointHornTensorCofanMap_isClosedEmbedding J n i K cA cB hA hB m hm)

end PointedCGWH
