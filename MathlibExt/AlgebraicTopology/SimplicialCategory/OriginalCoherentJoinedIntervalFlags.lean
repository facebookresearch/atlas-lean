/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentJoinedIntervals

/-!
# Full original flag gluing on joined endpoint intervals

The SAME joined ordinal takes both complete original interval preimages
to the complete original outer-interval preimage of their union. Every
original coefficient vertex is retained, with zero intervals included.
-/

noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBeadInterval

open SSet.OriginalTwoBead.OrdinalCharts

variable {n : ℕ} (a b c : Fin (n + 1)) (hab : a ≤ b) (hbc : b ≤ c)

/-- EVERY lifted original first-interval vertex keeps its same native joined image. -/
theorem joined_prefix_lifted (i : ULift.{u} (Fin (length a b + 1))) :
    liftedEmbedding.{u} a c (hab.trans hbc)
      ((joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u}
        ((prefixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} i)) =
          liftedEmbedding.{u} a b hab i :=
  ULift.ext (joined_prefix_vertex a b c hab hbc i.down)

/-- EVERY lifted original second-interval vertex keeps its same native joined image. -/
theorem joined_suffix_lifted (i : ULift.{u} (Fin (length b c + 1))) :
    liftedEmbedding.{u} a c (hab.trans hbc)
      ((joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u}
        ((suffixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} i)) =
          liftedEmbedding.{u} b c hbc i :=
  ULift.ext (joined_suffix_vertex a b c hab hbc i.down)

/-- The SAME complete first interval flag has its literal native joined preimage readback. -/
theorem joined_prefix_image_preimage (S : Set (ULift.{u} (Fin (n + 1))))
    (hS : ∀ i ∈ S, ULift.up.{u} a ≤ i ∧ i ≤ ULift.up.{u} b) :
    (joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u} ''
      ((prefixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} ''
        (liftedEmbedding.{u} a b hab ⁻¹' S)) =
      liftedEmbedding.{u} a c (hab.trans hbc) ⁻¹' S := by
  ext i
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
    change liftedEmbedding.{u} a c (hab.trans hbc)
      ((joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u}
        ((prefixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} k)) ∈ S
    rw [joined_prefix_lifted]
    exact hk
  · intro hi
    obtain ⟨k, hk⟩ := coverage.{u} a b hab (liftedEmbedding.{u} a c (hab.trans hbc) i)
      (by rw [lifted_zero]; exact (hS _ hi).1)
      (by rw [lifted_last]; exact (hS _ hi).2)
    refine ⟨(prefixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} k,
      ⟨k, (congrArg (fun j => j ∈ S) hk).mpr hi, rfl⟩, ?_⟩
    apply (liftedEmbedding.{u} a c (hab.trans hbc)).injective
    exact (joined_prefix_lifted a b c hab hbc k).trans hk

/-- The SAME complete second interval flag has its literal native joined preimage readback. -/
theorem joined_suffix_image_preimage (S : Set (ULift.{u} (Fin (n + 1))))
    (hS : ∀ i ∈ S, ULift.up.{u} b ≤ i ∧ i ≤ ULift.up.{u} c) :
    (joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u} ''
      ((suffixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} ''
        (liftedEmbedding.{u} b c hbc ⁻¹' S)) =
      liftedEmbedding.{u} a c (hab.trans hbc) ⁻¹' S := by
  ext i
  constructor
  · rintro ⟨j, ⟨k, hk, rfl⟩, rfl⟩
    change liftedEmbedding.{u} a c (hab.trans hbc)
      ((joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u}
        ((suffixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} k)) ∈ S
    rw [joined_suffix_lifted]
    exact hk
  · intro hi
    obtain ⟨k, hk⟩ := coverage.{u} b c hbc (liftedEmbedding.{u} a c (hab.trans hbc) i)
      (by rw [lifted_zero]; exact (hS _ hi).1)
      (by rw [lifted_last]; exact (hS _ hi).2)
    refine ⟨(suffixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} k,
      ⟨k, (congrArg (fun j => j ∈ S) hk).mpr hi, rfl⟩, ?_⟩
    apply (liftedEmbedding.{u} a c (hab.trans hbc)).injective
    exact (joined_suffix_lifted a b c hab hbc k).trans hk

/-- Both entire original flags glue to the SAME full outer-interval union preimage. -/
theorem joined_image_preimages (S T : Set (ULift.{u} (Fin (n + 1))))
    (hS : ∀ i ∈ S, ULift.up.{u} a ≤ i ∧ i ≤ ULift.up.{u} b)
    (hT : ∀ i ∈ T, ULift.up.{u} b ≤ i ∧ i ≤ ULift.up.{u} c) :
    (joinedOperator a b c hab hbc).toOrderHom.uliftMap.{0, 0, u, u} ''
      ((prefixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} ''
        (liftedEmbedding.{u} a b hab ⁻¹' S) ∪
        (suffixOperator (length a b) (length b c)).toOrderHom.uliftMap.{0, 0, u, u} ''
          (liftedEmbedding.{u} b c hbc ⁻¹' T)) =
      liftedEmbedding.{u} a c (hab.trans hbc) ⁻¹' (S ∪ T) := by
  rw [Set.image_union, joined_prefix_image_preimage a b c hab hbc S hS,
    joined_suffix_image_preimage a b c hab hbc T hT, Set.preimage_union]

end CategoryTheory.CoherentRealization.OriginalBeadInterval
