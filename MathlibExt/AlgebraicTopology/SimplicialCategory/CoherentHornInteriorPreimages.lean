/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornInteriorFace

/-!
# The original supplied-face preimage of an ambient interior label

Every ambient interior vertex different from the omitted face label has
its actual ordinal-face preimage. That preimage is itself interior, and
its image is the same individual original vertex.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.CoherentRealization.HornInteriorPreimages
open HornBoxFaces HornInteriorFace
variable {n : ℕ} (k b : Interior.{u} n) (hb : HornBoxFaces.vertex b ≠ HornBoxFaces.vertex k)

include hb in
private theorem in_range : b.val ∈ Set.range (OrdinalFace.embedding (HornBoxFaces.vertex k)) :=
  (OrdinalFace.mem_range_embedding (HornBoxFaces.vertex k) b.val).mpr (fun h => hb (congrArg ULift.down h))

/-- The actual unique ordinal-face source vertex over the supplied ambient interior label. -/
def sourceVertex : ULift.{u} (Fin (n + 2)) := Classical.choose (in_range k b hb)

/-- The original ordinal operator reads back the whole supplied individual vertex. -/
theorem sourceVertex_image : (OrdinalFace.embedding (HornBoxFaces.vertex k)) (sourceVertex k b hb) = b.val :=
  Classical.choose_spec (in_range k b hb)

/-- The same original source vertex is interior in the actual supplied face. -/
def preimage : SourceInterior n := by
  refine ⟨(sourceVertex k b hb).down, ?_, ?_⟩
  · apply (OrdinalFace.embedding (HornBoxFaces.vertex k)).lt_iff_lt.mp
    change (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up.{u} (0 : Fin (n + 2))) <
      (OrdinalFace.embedding (HornBoxFaces.vertex k)) (sourceVertex k b hb)
    rw [sourceVertex_image]
    have h₀ : (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up.{u} (0 : Fin (n + 2))) =
        ULift.up (0 : Fin (n + 3)) := ULift.ext (source_zero k)
    rw [h₀]
    exact b.property.1
  · apply (OrdinalFace.embedding (HornBoxFaces.vertex k)).lt_iff_lt.mp
    change (OrdinalFace.embedding (HornBoxFaces.vertex k)) (sourceVertex k b hb) <
      (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up.{u} (Fin.last (n + 1)))
    rw [sourceVertex_image]
    have hₙ : (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up.{u} (Fin.last (n + 1))) =
        ULift.up (Fin.last (n + 2)) := ULift.ext (target_last k)
    rw [hₙ]
    exact b.property.2

/-- The supplied face interior preimage returns exactly the same individual ambient interior vertex. -/
theorem middle_preimage : middle k (preimage k b hb) = b := by
  apply Subtype.ext
  exact sourceVertex_image k b hb

/-- Equality of the original finite labels implies equality of the actual interior vertices. -/
theorem label_injective {b c : Interior.{u} n} (h : HornBoxFaces.vertex b = HornBoxFaces.vertex c) : b = c :=
  Subtype.ext (ULift.ext h)

end CategoryTheory.CoherentRealization.HornInteriorPreimages
