/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentIntervalOperator

/-!
# SAME full interval images and preimages under original operators

Every actual endpoint-supported subset keeps its whole original image
and preimage when the source operator is restricted to the two full
intervals. No injectivity or surjectivity of the original operator is
assumed, and every coefficient universe is retained.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

variable {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (a b : Fin (n + 1)) (hab : a ≤ b)

/-- EVERY lifted original interval vertex retains the same whole original operator square. -/
theorem intervalOperator_lifted_vertex (i : ULift.{u} (Fin (length a b + 1))) :
    liftedEmbedding.{u} (f.toOrderHom a) (f.toOrderHom b) (f.toOrderHom.monotone hab)
      ((intervalOperator f a b hab).toOrderHom.uliftMap i) =
        f.toOrderHom.uliftMap (liftedEmbedding.{u} a b hab i) :=
  ULift.ext (intervalOperator_vertex f a b hab i.down)

/-- The SAME full supported original subset retains exact interval image/preimage commutation. -/
theorem intervalOperator_image_preimage (S : Set (ULift.{u} (Fin (n + 1))))
    (hS : ∀ j ∈ S, ULift.up.{u} a ≤ j ∧ j ≤ ULift.up.{u} b) :
    (intervalOperator f a b hab).toOrderHom.uliftMap '' (liftedEmbedding.{u} a b hab ⁻¹' S) =
      liftedEmbedding.{u} (f.toOrderHom a) (f.toOrderHom b) (f.toOrderHom.monotone hab) ⁻¹'
        (f.toOrderHom.uliftMap '' S) := by
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    change liftedEmbedding.{u} (f.toOrderHom a) (f.toOrderHom b) (f.toOrderHom.monotone hab)
      ((intervalOperator f a b hab).toOrderHom.uliftMap j) ∈ f.toOrderHom.uliftMap '' S
    rw [intervalOperator_lifted_vertex]
    exact ⟨liftedEmbedding.{u} a b hab j, hj, rfl⟩
  · rintro ⟨j, hj, he⟩
    obtain ⟨k, hk⟩ := coverage.{u} a b hab j
      (by rw [lifted_zero]; exact (hS j hj).1)
      (by rw [lifted_last]; exact (hS j hj).2)
    refine ⟨k, (congrArg (fun s => s ∈ S) hk).mpr hj, ?_⟩
    apply (liftedEmbedding.{u} (f.toOrderHom a) (f.toOrderHom b) (f.toOrderHom.monotone hab)).injective
    rw [intervalOperator_lifted_vertex, hk]
    exact he

end CategoryTheory.CoherentRealization.OriginalBeadInterval
