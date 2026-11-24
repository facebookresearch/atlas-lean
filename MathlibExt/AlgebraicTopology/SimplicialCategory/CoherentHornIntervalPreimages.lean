/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentTwoOutsideFaces

/-!
# Original interval vertices in the two actual endpoint-face intersections

Removing a nonzero or nonlast face label preserves the corresponding
original endpoint. The actual first/last common-face preimages therefore
retain every supplied original interval vertex, not only short legs.
-/

noncomputable section
universe u
open CategoryTheory

namespace CategoryTheory.CoherentRealization.HornIntervalPreimages
variable {n : ℕ}

/-- A nonzero original source vertex remains nonzero in a face preserving zero. -/
theorem image_ne_zero (k : Fin (n + 3)) (hk : k ≠ 0) (a : Fin (n + 2)) (ha : a ≠ 0) : k.succAbove a ≠ 0 := by
  have h := (Fin.succAboveOrderEmb k).strictMono (Fin.pos_iff_ne_zero.mpr ha)
  change k.succAbove 0 < k.succAbove a at h
  rw [Fin.succAbove_ne_zero_zero hk] at h
  exact ne_of_gt h

/-- A source vertex before the last endpoint remains before it in a face preserving that last endpoint. -/
theorem image_ne_last (k : Fin (n + 3)) (hk : k ≠ Fin.last (n + 2))
    (a : Fin (n + 2)) (ha : a ≠ Fin.last (n + 1)) : k.succAbove a ≠ Fin.last (n + 2) := by
  have h := (Fin.succAboveOrderEmb k).strictMono (Fin.lt_last_iff_ne_last.mpr ha)
  change k.succAbove a < k.succAbove (Fin.last (n + 1)) at h
  rw [Fin.succAbove_ne_last_last hk] at h
  exact ne_of_lt h

/-- The actual first-face common vertex is precisely the supplied original nonzero face vertex. -/
theorem first_point (k : Fin (n + 3)) (hk : k ≠ 0) (a : Fin (n + 2)) (ha : a ≠ 0) :
    TwoOutsideFaces.point 0 k (Fin.pos_iff_ne_zero.mpr hk) (ULift.up.{u} (a.pred ha)) =
      (OrdinalFace.embedding k) (ULift.up.{u} a) := by
  rw [TwoOutsideFaces.point_right]
  apply ULift.ext
  change k.succAbove (((0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt (Fin.pos_iff_ne_zero.mpr
    hk))).succAbove (a.pred ha)) = k.succAbove a
  have h : (0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt (Fin.pos_iff_ne_zero.mpr hk)) = (0 : Fin (n + 2)) := rfl
  rw [h, Fin.succAbove_zero, Fin.succ_pred]

/-- The actual last-face common vertex is precisely the supplied original face vertex before its last endpoint. -/
theorem last_point (k : Fin (n + 3)) (hk : k ≠ Fin.last (n + 2)) (a : Fin (n + 2)) (ha : a ≠ Fin.last (n + 1)) :
    TwoOutsideFaces.point k (Fin.last (n + 2)) (Fin.lt_last_iff_ne_last.mpr hk) (ULift.up.{u} (a.castPred ha)) =
      (OrdinalFace.embedding k) (ULift.up.{u} a) := by
  apply ULift.ext
  change k.succAbove (((Fin.last (n + 2)).pred (Fin.ne_zero_of_lt (Fin.lt_last_iff_ne_last.mpr
    hk))).succAbove (a.castPred ha)) = k.succAbove a
  have h : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt (Fin.lt_last_iff_ne_last.mpr hk)) = Fin.last (n + 1) := rfl
  rw [h, Fin.succAbove_last, Fin.castSucc_castPred]

/-- The supplied first-face source preimage is the original predecessor of the same ambient vertex. -/
theorem first_preimage (k : Fin (n + 3)) (hk : k ≠ 0) (a : Fin (n + 2)) (ha : a ≠ 0) :
    (OrdinalFace.embedding (k.pred hk)) (ULift.up.{u} (a.pred ha)) =
      ULift.up ((k.succAbove a).pred (image_ne_zero k hk a ha)) := by
  apply (OrdinalFace.embedding (0 : Fin (n + 3))).injective
  have h₁ : (OrdinalFace.embedding (0 : Fin (n + 3))) ((OrdinalFace.embedding (k.pred hk)) (ULift.up.{u} (a.pred ha))) =
      TwoOutsideFaces.point 0 k (Fin.pos_iff_ne_zero.mpr hk) (ULift.up.{u} (a.pred ha)) := rfl
  have h₂ : (OrdinalFace.embedding (0 : Fin (n + 3)))
      (ULift.up.{u} ((k.succAbove a).pred (image_ne_zero k hk a ha))) = ULift.up (k.succAbove a) := by
    apply ULift.ext
    change ((k.succAbove a).pred (image_ne_zero k hk a ha)).succ = k.succAbove a
    exact Fin.succ_pred _ _
  exact h₁.trans ((first_point k hk a ha).trans h₂.symm)

/-- The supplied last-face source preimage is the original predecessor-of-last deletion of that same ambient vertex. -/
theorem last_preimage (k : Fin (n + 3)) (hk : k ≠ Fin.last (n + 2)) (a : Fin (n + 2)) (ha : a ≠ Fin.last (n + 1)) :
    (OrdinalFace.embedding (k.castPred hk)) (ULift.up.{u} (a.castPred ha)) =
      ULift.up ((k.succAbove a).castPred (image_ne_last k hk a ha)) := by
  apply (OrdinalFace.embedding (Fin.last (n + 2))).injective
  have h₁ := (TwoOutsideFaces.point_right k (Fin.last (n + 2)) (Fin.lt_last_iff_ne_last.mpr hk)
    (ULift.up.{u} (a.castPred ha))).symm
  have h₂ : (OrdinalFace.embedding (Fin.last (n + 2)))
      (ULift.up.{u} ((k.succAbove a).castPred (image_ne_last k hk a ha))) = ULift.up (k.succAbove a) := by
    apply ULift.ext
    change (Fin.last (n + 2)).succAbove ((k.succAbove a).castPred (image_ne_last k hk a ha)) = k.succAbove a
    simpa only [Fin.succAbove_last] using Fin.castSucc_castPred (k.succAbove a) (image_ne_last k hk a ha)
  exact h₁.trans ((last_point k hk a ha).trans h₂.symm)

end CategoryTheory.CoherentRealization.HornIntervalPreimages
