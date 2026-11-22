/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.ClosedEmbeddingCoproducts
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellTransfinite
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.CGWHClosedCellPushouts
public import MathlibExt.Topology.Category.TopCat.Embedding.ClosedEmbeddingTransfinite
public import MathlibExt.CategoryTheory.SmallObject.SelectiveMapping
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Native pointed closed-transition closure

These public instances give closure under pointed coproducts, pushouts and
transfinite compositions. Closed pushouts use the connected underlying square.
Only the original continuous witness is forgotten in the transfinite proof.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits Topology

namespace PointedCGWH

instance underlyingClosedEmbeddings_isStableUnderCoproducts :
    (TopCat.closedEmbeddings.inverseImage
      (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})).IsStableUnderCoproducts.{v} := by
  constructor
  intro J
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk _ _
  intro A B _ _ f hf
  exact isClosedEmbedding_coproductMap A B f hf

instance underlyingClosedEmbeddings_isStableUnderCobaseChange :
    (TopCat.closedEmbeddings.inverseImage
      (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})).IsStableUnderCobaseChange := by
  constructor
  intro X Y Y' Z f g f' g' sq hf
  let U := pointedToCGWH.{u, v}
  let sqU : IsPushout g.right f.right f'.right g'.right := sq.map U
  let h := sqU.flip
  let e := h.isoIsPushout _ _ (IsPushout.of_hasPushout f.right g.right)
  have he : f'.right ≫ e.hom = pushout.inr f.right g.right :=
    h.inr_isoIsPushout_hom _ _ (IsPushout.of_hasPushout f.right g.right)
  have hc : IsClosedEmbedding (ConcreteCategory.hom (f'.right ≫ e.hom)) := by
    rw [he]
    exact CGWH.isClosedEmbedding_pushout_inr f.right g.right hf
  exact (TopCat.closedEmbeddings.cancel_right_of_respectsIso
    (CGWH.cgwhToTop.map f'.right) (CGWH.cgwhToTop.mapIso e).hom).mp hc

variable {J : Type v} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

/-- Closedness of the exact original pointed transfinite endpoint. -/
theorem isClosedEmbedding_of_transfiniteComposition
    {X Y : PointedCGWH.{u, v}} {f : X ⟶ Y}
    (c : (TopCat.closedEmbeddings.inverseImage
      (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})).TransfiniteCompositionOfShape J f) :
    IsClosedEmbedding (ConcreteCategory.hom f.right) := by
  let U := pointedToCGWH.{u, v}
  let _ : IsFiltered J := inferInstance
  let _ : PreservesColimit c.F U := inferInstance
  have hLimit (m : J) (hm : Order.IsSuccLimit m) :
      PreservesColimit ((Set.principalSegIio m).monotone.functor ⋙ c.F) U := by
    let _ : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
    let _ : OrderBot (Set.Iio m) :=
      { bot := ⟨⊥, hm.bot_lt⟩
        bot_le := fun x => show (⊥ : J) ≤ x.1 from bot_le }
    let _ : IsFiltered (Set.Iio m) := inferInstance
    infer_instance
  let cu := c.toTransfiniteCompositionOfShape.mapOfPreserves U hLimit
  have hSucc : ∀ (t : J) (_ht : ¬ IsMax t), Function.Injective
      (CGWH.cgwhToCompactlyGenerated.map
        (cu.F.map (homOfLE (Order.le_succ t)))).hom := by
    intro t ht
    exact (c.map_mem t ht).injective
  let cc := cu.mapCgwhToCompactlyGeneratedOfInjective hSucc
  let T := CompactlyGenerated.compactlyGeneratedToTop.{u, v}
  let _ : PreservesColimitsOfSize.{v, v} T :=
    CompactlyGenerated.adj.leftAdjoint_preservesColimits
  let _ : PreservesWellOrderContinuousOfShape J T :=
    { preservesColimitsOfShape := fun _ _ => inferInstance }
  let ct := cc.map T
  have cTop : TopCat.closedEmbeddings.TransfiniteCompositionOfShape J
      (CGWH.cgwhToTop.map (U.map f)) :=
    { toTransfiniteCompositionOfShape := ct
      map_mem := by
        intro t ht
        change TopCat.closedEmbeddings
          (T.map (cc.F.map (homOfLE (Order.le_succ t))))
        rw [TransfiniteCompositionOfShape.mapCgwhToCompactlyGeneratedOfInjective_F]
        exact c.map_mem t ht }
  exact TopCat.isClosedEmbedding_of_transfiniteCompositionOfShape cTop

instance underlyingClosedEmbeddings_isStableUnderTransfiniteComposition :
    (TopCat.closedEmbeddings.inverseImage
      (pointedToCGWH.{u, v} ⋙ CGWH.cgwhToTop.{u, v})).IsStableUnderTransfiniteComposition.{v} := by
  constructor
  intro J _ _ _ _
  exact ⟨fun _ _ _ ⟨c⟩ => isClosedEmbedding_of_transfiniteComposition c⟩

end PointedCGWH
