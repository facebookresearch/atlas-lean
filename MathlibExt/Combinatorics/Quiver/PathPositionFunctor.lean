/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.Combinatorics.Quiver.PathIntervals
import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# The whole original word as a native path-position functor

Every actual original path gives the complete ordinal word of its
individual original vertices and all native interval subpaths. Identity
and composition are proved by unique full cuts, including empty paths
and repeated vertices. Every generator is retained.
-/

noncomputable section
universe u v
open CategoryTheory

namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- The SAME individual original vertex at a position of the full path. -/
def positionVertex (p : Path x y) (i : Fin (p.length + 1)) : V :=
  (cut p i.val (Nat.le_of_lt_succ i.isLt)).vertex

/-- The actual full interval has the first original position vertex. -/
lemma intervalCut_start_eq (p : Path x y) (i j : Fin (p.length + 1)) (h : i ≤ j) :
    (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).start = positionVertex (V := V) p i :=
  congrArg Cut.vertex (Subsingleton.elim
    (IntervalCut.firstCut p i.val j.val (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)))
    (cut p i.val (Nat.le_of_lt_succ i.isLt)))

/-- The actual full interval has the second original position vertex. -/
lemma intervalCut_stop_eq (p : Path x y) (i j : Fin (p.length + 1)) (h : i ≤ j) :
    (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).stop = positionVertex (V := V) p j :=
  congrArg Cut.vertex (Subsingleton.elim
    (IntervalCut.secondCut p i.val j.val (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)))
    (cut p j.val (Nat.le_of_lt_succ j.isLt)))

/-- The SAME whole original interval subpath between two specified original positions. -/
def positionPath (p : Path x y) (i j : Fin (p.length + 1)) (h : i ≤ j) :
    Path (positionVertex (V := V) p i) (positionVertex (V := V) p j) :=
  @Quiver.homOfEq (Paths V) (Paths.categoryPaths V).toCategoryStruct.toQuiver
    _ _ _ _ (intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)).middlePath
    (intervalCut_start_eq p i j h) (intervalCut_stop_eq p i j h)

/-- The full original path-position word, with all original intermediate
vertices and complete native subpaths retained. -/
def positionWord (p : Path x y) : Fin (p.length + 1) ⥤ Paths V :=
  ComposableArrows.mkOfObjOfMapSucc (C := Paths V) (fun i => (positionVertex (V :=
    V) p i : Paths V))
    (fun i => positionPath (V := V) p i.castSucc i.succ (Fin.castSucc_le_succ i))

/-- Every original path-position word object is the SAME native cut vertex. -/
lemma positionWord_obj (p : Path x y) (i : Fin (p.length + 1)) :
    (positionWord p).obj i = positionVertex (V := V) p i := rfl

/-- Every original consecutive edge is the SAME full native original interval path. -/
lemma positionWord_map_succ (p : Path x y) (i : ℕ) (hi : i < p.length) :
    ComposableArrows.map' (positionWord p) i (i + 1) =
      positionPath (V := V) p (Fin.mk i (Nat.lt_trans hi (Nat.lt_succ_self _)))
        (Fin.mk (i + 1) (Nat.succ_lt_succ hi)) (Nat.le_succ i) :=
  ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi

end Quiver.Path
