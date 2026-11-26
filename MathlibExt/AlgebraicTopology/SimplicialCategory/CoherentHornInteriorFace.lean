/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentTwoOutsideFaces

/-!
# Individual interior vertices in an original supplied horn face

An original interior vertex of a supplied nonendpoint face stays an
interior vertex of the ambient simplex. The first/last common charts
and their preimages preserve that same original finite label.
-/

noncomputable section
universe u
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornInteriorFace
open SimplicialEnrichment HornBoxFaces
variable {n : ℕ}

/-- An individual interior vertex of the original supplied face, including its literal empty smallest case. -/
abbrev SourceInterior (n : ℕ) := {t : Fin (n + 2) // 0 < t ∧ t < Fin.last (n + 1)}

/-- The supplied face has no interior vertex in its literal degree-one case. -/
theorem sourceInterior_zero_empty : IsEmpty (SourceInterior 0) := ⟨fun t => by
  have h₀ := t.property.1
  have h₁ := t.property.2
  change 0 < t.val.val at h₀
  change t.val.val < 1 at h₁
  omega⟩

/-- The same supplied interior vertex in the original ambient simplex. -/
def middle (k : Interior.{u} n) (t : SourceInterior n) : Interior.{u} n := by
  refine ⟨(OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up t.val), ?_, ?_⟩
  · have h := (OrdinalFace.embedding (HornBoxFaces.vertex k)).strictMono
      (show (ULift.up (0 : Fin (n + 2)) : ULift.{u} (Fin (n + 2))) < ULift.up t.val from t.property.1)
    have h₀ : (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (0 : Fin (n + 2))) =
        (ULift.up (0 : Fin (n + 3)) : ULift.{u} (Fin (n + 3))) := ULift.ext (source_zero k)
    exact h₀ ▸ h
  · have h := (OrdinalFace.embedding (HornBoxFaces.vertex k)).strictMono
      (show (ULift.up t.val : ULift.{u} (Fin (n + 2))) < ULift.up (Fin.last (n + 1)) from t.property.2)
    have hₙ : (OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1))) =
        (ULift.up (Fin.last (n + 2)) : ULift.{u} (Fin (n + 3))) := ULift.ext (target_last k)
    exact hₙ ▸ h

/-- The ambient middle label is exactly the original supplied face operator applied to the supplied vertex. -/
theorem middle_vertex (k : Interior.{u} n) (t : SourceInterior n) :
    HornBoxFaces.vertex (middle k t) = (HornBoxFaces.vertex k).succAbove t.val := rfl

/-- The first common last-face vertex keeps the same original zero endpoint. -/
theorem left_zero (k : Interior.{u} n) :
    TwoOutsideFaces.point (HornBoxFaces.vertex k) (Fin.last (n + 2)) k.property.2
      (ULift.up.{u} (0 : Fin (n + 1))) = ULift.up (0 : Fin (n + 3)) := by
  apply ULift.ext
  change (HornBoxFaces.vertex k).succAbove (((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt k.property.2)).succAbove 0) = 0
  have h : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt k.property.2) = Fin.last (n + 1) := rfl
  rw [h, Fin.succAbove_last]
  exact source_zero k

/-- The original common last-face chart keeps precisely the supplied interior middle vertex. -/
theorem left_middle (k : Interior.{u} n) (t : SourceInterior n) :
    TwoOutsideFaces.point (HornBoxFaces.vertex k) (Fin.last (n + 2)) k.property.2
      (ULift.up.{u} (t.val.castPred (ne_of_lt t.property.2))) = (middle k t).val := by
  apply ULift.ext
  change (HornBoxFaces.vertex k).succAbove (((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt k.property.2)).succAbove
    (t.val.castPred (ne_of_lt t.property.2))) = (HornBoxFaces.vertex k).succAbove t.val
  have h : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt k.property.2) = Fin.last (n + 1) := rfl
  rw [h, Fin.succAbove_last, Fin.castSucc_castPred]

/-- The original common first-face chart keeps that same individual supplied middle vertex. -/
theorem right_middle (k : Interior.{u} n) (t : SourceInterior n) :
    TwoOutsideFaces.point (0 : Fin (n + 3)) (HornBoxFaces.vertex k) k.property.1
      (ULift.up.{u} (t.val.pred (ne_of_gt t.property.1))) = (middle k t).val := by
  rw [TwoOutsideFaces.point_right]
  apply ULift.ext
  change (HornBoxFaces.vertex k).succAbove
    (((0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt k.property.1)).succAbove (t.val.pred (ne_of_gt t.property.1))) =
      (HornBoxFaces.vertex k).succAbove t.val
  have h : (0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt k.property.1) = (0 : Fin (n + 2)) := rfl
  rw [h, Fin.succAbove_zero, Fin.succ_pred]

/-- The other common first-face vertex keeps the same original last endpoint. -/
theorem right_last (k : Interior.{u} n) :
    TwoOutsideFaces.point (0 : Fin (n + 3)) (HornBoxFaces.vertex k) k.property.1
      (ULift.up.{u} (Fin.last n)) = ULift.up (Fin.last (n + 2)) := by
  rw [TwoOutsideFaces.point_right]
  apply ULift.ext
  change (HornBoxFaces.vertex k).succAbove
    (((0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt k.property.1)).succAbove (Fin.last n)) = Fin.last (n + 2)
  have h : (0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt k.property.1) = (0 : Fin (n + 2)) := rfl
  rw [h, Fin.succAbove_zero]
  exact target_last k

/-- The original last-face preimage is forced by its same individual ambient vertex. -/
theorem last_preimage (k : Interior.{u} n) (s : ULift.{u} (Fin (n + 1))) {a : Fin (n + 3)}
    (h : (TwoOutsideFaces.point (HornBoxFaces.vertex k) (Fin.last (n + 2)) k.property.2 s).down = a)
    (ha : a ≠ Fin.last (n + 2)) :
    (OrdinalFace.embedding ((HornBoxFaces.vertex k).castPred (vertex_ne_last k))) s = ULift.up (a.castPred ha) := by
  apply (OrdinalFace.embedding (Fin.last (n + 2))).injective
  have h₁ := (TwoOutsideFaces.point_right (HornBoxFaces.vertex k) (Fin.last (n + 2)) k.property.2 s).symm
  have h₂ : (OrdinalFace.embedding (Fin.last (n + 2))) (ULift.up.{u} (a.castPred ha)) = ULift.up a := by
    apply ULift.ext
    change (Fin.last (n + 2)).succAbove (a.castPred ha) = a
    simpa only [Fin.succAbove_last] using Fin.castSucc_castPred a ha
  exact h₁.trans ((ULift.ext h).trans h₂.symm)

/-- The original first-face preimage is forced by the same individual ambient vertex. -/
theorem first_preimage (k : Interior.{u} n) (s : ULift.{u} (Fin (n + 1))) {a : Fin (n + 3)}
    (h : (TwoOutsideFaces.point 0 (HornBoxFaces.vertex k) k.property.1 s).down = a) (ha : a ≠ 0) :
    (OrdinalFace.embedding ((HornBoxFaces.vertex k).pred (vertex_ne_zero k))) s = ULift.up (a.pred ha) := by
  apply (OrdinalFace.embedding (0 : Fin (n + 3))).injective
  have h₁ : (OrdinalFace.embedding (0 : Fin (n + 3)))
      ((OrdinalFace.embedding ((HornBoxFaces.vertex k).pred (vertex_ne_zero k))) s) =
        TwoOutsideFaces.point 0 (HornBoxFaces.vertex k) k.property.1 s := rfl
  have h₂ : (OrdinalFace.embedding (0 : Fin (n + 3))) (ULift.up.{u} (a.pred ha)) = ULift.up a := by
    apply ULift.ext
    change (0 : Fin (n + 3)).succAbove (a.pred ha) = a
    exact Fin.succ_pred a ha
  exact h₁.trans ((ULift.ext h).trans h₂.symm)

end CategoryTheory.CoherentRealization.HornInteriorFace
