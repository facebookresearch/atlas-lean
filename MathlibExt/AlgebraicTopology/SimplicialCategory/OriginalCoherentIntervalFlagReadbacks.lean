/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadInterval
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathEndpointTransport

/-!
# Both SAME full original endpoint-interval coefficient readbacks

The existing actual full interval Hom isomorphism keeps the direct image
and preimage of every original path flag. The inverse formula follows
from its actual whole inverse equation and injective original embedding;
no chosen comparison or weak outcome is supplied.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

variable {n : ℕ} (a b : Fin (n + 1)) (hab : a ≤ b) {q : SimplexCategoryᵒᵖ}

private theorem homIso_hom_native :
    (homIso.{u} a b hab).hom =
      OrderEmbeddingFace.imageMap (liftedEmbedding.{u} a b hab) (ULift.up 0)
        (ULift.up (Fin.last (length a b))) ≫
      nerveMap (PathEndpointTransport.retarget (lifted_zero.{u} a b hab) (lifted_last.{u} a b hab)) := by
  change (wholeHomIso.{u} a b hab).hom ≫
    eqToHom (congrArg₂ (fun x y : ULift.{u} (Fin (n + 1)) => nerve (SimplicialThickening.Path x y))
      (lifted_zero.{u} a b hab) (lifted_last.{u} a b hab)) = _
  rw [wholeHomIso, IntervalFaceCover.wholeHomIso_hom]
  exact congrArg (fun e => OrderEmbeddingFace.imageMap (liftedEmbedding.{u} a b hab) (ULift.up 0)
      (ULift.up (Fin.last (length a b))) ≫ e)
    (PathEndpointTransport.nerve_retarget (lifted_zero.{u} a b hab) (lifted_last.{u} a b hab)).symm

/-- The SAME whole interval forward map has its literal direct-image flag in every scalar. -/
theorem homIso_hom_flags
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} (0 : Fin (length a b + 1)))
      (ULift.up.{u} (Fin.last (length a b))))).obj q) (t : Fin (q.unop.len + 1)) :
    (((homIso.{u} a b hab).hom.app q p).obj t).I = liftedEmbedding.{u} a b hab '' (p.obj t).I := by
  exact congrArg (fun e => ((e.app q p).obj t).I) (homIso_hom_native.{u} a b hab)

/-- The SAME whole interval inverse retains precisely the complete original flag preimage. -/
theorem homIso_inv_flags
    (p : (nerve (SimplicialThickening.Path (ULift.up.{u} a) (ULift.up.{u} b))).obj q)
    (t : Fin (q.unop.len + 1)) :
    (((homIso.{u} a b hab).inv.app q p).obj t).I = liftedEmbedding.{u} a b hab ⁻¹' (p.obj t).I := by
  have h := congrArg (fun s => (s.obj t).I) (ConcreteCategory.congr_hom
    (congr_app (homIso.{u} a b hab).inv_hom_id q) p)
  change (((homIso.{u} a b hab).hom.app q ((homIso.{u} a b hab).inv.app q p)).obj t).I =
    (p.obj t).I at h
  rw [homIso_hom_flags] at h
  ext i
  constructor
  · intro hi
    rw [← h]
    exact ⟨i, hi, rfl⟩
  · intro hi
    change liftedEmbedding.{u} a b hab i ∈ (p.obj t).I at hi
    rw [← h] at hi
    obtain ⟨j, hj, he⟩ := hi
    exact (liftedEmbedding.{u} a b hab).injective he ▸ hj

end CategoryTheory.CoherentRealization.OriginalBeadInterval
