/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectCountableColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeSingleHomCountability
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFamilies
import MathlibExt.CategoryTheory.SmallObject.CountableAttachmentSquares

/-!
# Countability of the actual original boundary small-object successor

The original ordered-pair/dimension family surjects onto the SAME actual
arrow subset used by the native small-object construction. Every whole
top and bottom map is counted by the original free/evaluation adjunction.
The actual pushout of the full countable attachment coproducts then has
countable entire Hom simplices on the SAME original labels.
-/

noncomputable section
universe u
open CategoryTheory Limits SmallObject
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u} [Countable O]

/-- The SAME actual original boundary arrow subset, including every degree-zero and loop generator, is countable. -/
instance boundaryFamily_countable : Countable (boundaryFamily O).toSet := by
  let φ (i : O × O × ℕ) : (boundaryFamily O).toSet :=
    ⟨Arrow.mk ((FreeSingleHom.functor i.1 i.2.1).map (∂Δ[i.2.2]).ι), ⟨i⟩⟩
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨A, B, f⟩, hf⟩
    obtain ⟨i⟩ := hf
    exact ⟨i, rfl⟩
  exact hφ.countable

/-- Every actual original boundary source retains all countable full path Homs. -/
instance boundaryFamily_source_countable (i : (boundaryFamily O).toSet) :
    CountableHoms i.val.left := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨x, y, n⟩⟩ := hf
  change CountableHoms (FreeSingleHom.object x y (∂Δ[n] : SSet.{u}))
  infer_instance

/-- Every SAME actual original boundary target retains all countable full path Homs. -/
instance boundaryFamily_target_countable (i : (boundaryFamily O).toSet) :
    CountableHoms i.val.right := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨x, y, n⟩⟩ := hf
  change CountableHoms (FreeSingleHom.object x y (Δ[n] : SSet.{u}))
  infer_instance

/-- The entire original map set from an actual free boundary source is countable. -/
instance boundaryFamily_top_maps_countable (C : FixedObjects O) [CountableHoms C]
    (i : (boundaryFamily O).toSet) : Countable (i.val.left ⟶ C) := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨x, y, n⟩⟩ := hf
  exact FreeSingleHom.countable_boundary_maps x y C n

/-- Every entire original bottom map from an actual free simplex target is counted. -/
instance boundaryFamily_bottom_maps_countable (D : FixedObjects O) [CountableHoms D]
    (i : (boundaryFamily O).toSet) : Countable (i.val.right ⟶ D) := by
  rcases i with ⟨⟨A, B, f⟩, hf⟩
  obtain ⟨⟨x, y, n⟩⟩ := hf
  exact FreeSingleHom.countable_simplex_maps x y D n

/-- The actual countable whole source and target coproducts give countable entire Homs in the SAME original boundary
successor. -/
instance boundarySuccessor_countableHoms {C D : FixedObjects O}
    [CountableHoms C] [CountableHoms D] (p : C ⟶ D) :
    CountableHoms (functorObj (boundaryFamily O).homFamily p) := by
  infer_instance

end CategoryTheory.SimplicialEnrichment.FixedObjects
