/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Quiver.PathPositionFunctor
import MathlibExt.Combinatorics.Quiver.PathCutNaturality

/-!
# Full native original position-path concatenation laws

The original prefix followed by the SAME full interval is exactly
its original longer prefix. Native uniqueness of full cuts proves
every original interval, including identity and complete concatenation.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- The actual original prefix at its individual original position vertex. -/
def positionPrefix (p : Path x y) (i : Fin (p.length + 1)) : Path x (positionVertex p i) :=
  (cut p i.val (Nat.le_of_lt_succ i.isLt)).leftPath

/-- The SAME complete original suffix at its individual original position vertex. -/
def positionSuffix (p : Path x y) (i : Fin (p.length + 1)) : Path (positionVertex p i) y :=
  (cut p i.val (Nat.le_of_lt_succ i.isLt)).rightPath

/-- Both actual original prefix and suffix retain the entire original native path. -/
lemma positionPrefix_suffix (p : Path x y) (i : Fin (p.length + 1)) :
    (positionPrefix p i).comp (positionSuffix p i) = p := cut_comp p i.val _

/-- The actual interval's original prefix is retained by the first native cut. -/
lemma intervalCut_left_heq (p : Path x y) (i j : Fin (p.length + 1)) (h : i ≤ j) :
    HEq (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).leftPath (positionPrefix p i) := by
  have he : IntervalCut.firstCut p i.val j.val (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)) =
      cut p i.val (Nat.le_of_lt_succ i.isLt) := Subsingleton.elim _ _
  exact Cut.leftPath_heq_of_eq he

/-- The actual original interval completes the SAME longer prefix. -/
lemma intervalCut_left_middle_heq (p : Path x y) (i j : Fin (p.length + 1)) (h : i ≤ j) :
    HEq ((intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).leftPath.comp
      (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).middlePath) (positionPrefix p j) := by
  have he : IntervalCut.secondCut p i.val j.val (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)) =
      cut p j.val (Nat.le_of_lt_succ j.isLt) := Subsingleton.elim _ _
  exact Cut.leftPath_heq_of_eq he

end Quiver.Path
