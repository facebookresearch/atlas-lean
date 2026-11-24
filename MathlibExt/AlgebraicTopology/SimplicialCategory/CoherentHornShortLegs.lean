/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxFaces

/-!
# Literal supplied endpoint faces of the actual short Hom maps

The two actual short-leg maps used on a positive Hom-box face are the
original last and first supplied horn-face extractions. Their preimage
vertices and both original endpoint equations remain explicit. No
compatibility or filler conclusion is an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornShortLegs
open SimplicialEnrichment HornBoxFaces
variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) (b : Interior.{u} n)

/-- The actual short Hom from zero to the supplied interior vertex is carried by its
original last-face preimages. -/
theorem leftMap_eq_lastFace : leftMap f hi₀ hiₙ b =
    HornOutsideIntervals.faceMap f (Fin.last (n + 2)) hiₙ.symm
      (ULift.up (0 : Fin (n + 2))) (ULift.up ((HornBoxFaces.vertex b).castPred (vertex_ne_last b)))
      (Or.inr (show (OrdinalFace.embedding (Fin.last (n + 2)))
          (ULift.up ((HornBoxFaces.vertex b).castPred (vertex_ne_last b))) <
        (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) from by
          change (Fin.last (n + 2)).succAbove ((HornBoxFaces.vertex b).castPred
            (vertex_ne_last b)) < Fin.last (n + 2)
          simpa only [Fin.succAbove_last] using Fin.castSucc_lt_last ((HornBoxFaces.vertex
            b).castPred
            (vertex_ne_last b))))
      (a := 0) (b := HornBoxFaces.vertex b) (by rw [Fin.succAbove_last]; rfl)
      (by simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (HornBoxFaces.vertex
        b) (vertex_ne_last b)) := by
  simp only [HornBoxFaces.leftMap, HornOutsideIntervals.homMap]
  rfl

/-- The actual short Hom from the interior vertex to the last endpoint is carried by its
original first-face
  preimages. -/
theorem rightMap_eq_firstFace : rightMap f hi₀ hiₙ b =
    HornOutsideIntervals.faceMap f (0 : Fin (n + 3)) hi₀.symm
      (ULift.up ((HornBoxFaces.vertex b).pred (vertex_ne_zero b))) (ULift.up (Fin.last (n + 1)))
      (Or.inl (show (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) <
        (OrdinalFace.embedding (0 : Fin (n + 3))) (ULift.up ((HornBoxFaces.vertex b).pred
          (vertex_ne_zero b))) from by
          change (0 : Fin (n + 3)) < ((HornBoxFaces.vertex b).pred (vertex_ne_zero b)).succ
          simpa only [Fin.succ_pred] using Fin.pos_iff_ne_zero.mpr (vertex_ne_zero b)))
      (a := HornBoxFaces.vertex b) (b := Fin.last (n + 2))
      (by
        simpa only [Fin.succAbove_zero] using
          Fin.succ_pred (HornBoxFaces.vertex b) (vertex_ne_zero b))
      (by rw [Fin.succAbove_zero]; rfl) := by
  simp only [HornBoxFaces.rightMap, HornOutsideIntervals.homMap, dite_eq_right (vertex_ne_zero b)]
  rfl

end CategoryTheory.CoherentRealization.HornShortLegs
