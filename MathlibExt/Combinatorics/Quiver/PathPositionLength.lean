/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Quiver.PathPositionWordMaps

/-!
# Actual original interval and word lengths

Every native original interval between cut positions has length equal
to the difference of those original positions. The SAME original
position word therefore retains exact lengths for EVERY ordinal Hom,
including repeated positions and all empty intervals.
-/

universe u v
open CategoryTheory
namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- The entire original interval length is the difference of its SAME original cut positions. -/
lemma IntervalCut.middle_length {p : Path x y} {i j : ℕ} (c : IntervalCut p i j) :
    c.middlePath.length = j - i := by
  have h := c.left_middle_length
  have hl := Quiver.Path.length_comp c.leftPath c.middlePath
  have ht : i + c.middlePath.length = j := (congrArg (fun k => k + c.middlePath.length) c.left_length).symm.trans
    (hl.symm.trans h)
  omega

/-- Actual original endpoint equality transport preserves the full native path length. -/
lemma homOfEq_length {a b a' b' : V} (p : Path a b) (ha : a = a') (hb : b = b') :
    (@Quiver.homOfEq (Paths V) (Paths.categoryPaths V).toCategoryStruct.toQuiver
      _ _ _ _ p ha hb).length = p.length := by
  cases ha
  cases hb
  rfl

/-- The original full interval transport retains its native original path length. -/
lemma positionPath_length (p : Path x y) (i j : Fin (p.length + 1)) (h : i ≤ j) :
    (positionPath (V := V) p i j h).length = j.val - i.val := by
  unfold positionPath
  have hm := (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).middle_length
  exact (homOfEq_length (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).middlePath
    (intervalCut_start_eq p i j h) (intervalCut_stop_eq p i j h)).trans hm

/-- EVERY actual original position-word Hom retains the complete native interval length. -/
lemma positionWord_map_length (p : Path x y) {i j : Fin (p.length + 1)} (f : i ⟶ j) :
    ((positionWord p).map f).length = j.val - i.val := by
  have h := positionWord_map p f
  exact (congrArg Quiver.Path.length h).trans (positionPath_length p i j (leOfHom f))

end Quiver.Path
