/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveCoordinates
import MathlibExt.Combinatorics.Quiver.PathCutNaturality

/-!
# Lossless original full path-nerve word recovery

The entire original native word is recovered from its SAME source,
target, total path and all cumulative cut positions. Unique cuts give
every intermediate original vertex and complete prefix, and native
path cancellation recovers every original Hom between word positions.
-/

noncomputable section
universe u v
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- Original full word coordinates retain individual endpoints, the
SAME complete native path and EVERY original cumulative cut length. -/
structure WordCoordinates (n : ℕ) where
  /-- The SAME individual original source vertex. -/
  source : V
  /-- The SAME individual original target vertex. -/
  target : V
  /-- The complete original native path. -/
  path : Quiver.Path source target
  /-- Every original cumulative cut position. -/
  cuts : Fin (n + 1) → ℕ
  /-- Every actual original cut lies in the same full original path. -/
  cuts_le : ∀ i, cuts i ≤ path.length

/-- Read all lossless original coordinates of the SAME full native nerve word. -/
def coordinates (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) : WordCoordinates V n where
  source := w.obj 0
  target := w.obj (Fin.last n)
  path := totalPath V n w
  cuts := cutPosition V n w
  cuts_le := cutPosition_le V n w

/-- Recover the SAME actual original word vertex from its complete path coordinate. -/
def WordCoordinates.vertex {n : ℕ} (c : WordCoordinates V n) (i : Fin (n + 1)) : V :=
  (Quiver.Path.cut c.path (c.cuts i) (c.cuts_le i)).vertex

/-- The native original full word vertex is read back exactly at every original position. -/
lemma coordinates_vertex (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    (coordinates V n w).vertex V i = w.obj i :=
  (congrArg Quiver.Path.Cut.vertex (wordCut_eq V n w i)).symm

/-- Equal complete native path coordinates recover EVERY original word vertex. -/
lemma coordinates_vertices (n : ℕ) (w w' : (nerve (Paths V)) _⦋n⦌)
    (h : coordinates V n w = coordinates V n w') (i : Fin (n + 1)) : w.obj i = w'.obj i :=
  (coordinates_vertex V n w i).symm.trans
    ((congrArg (fun c => WordCoordinates.vertex V c i) h).trans (coordinates_vertex V n w' i))

/-- Recover the SAME complete original prefix from the total path and actual cut. -/
def WordCoordinates.leftPath {n : ℕ} (c : WordCoordinates V n) (i : Fin (n + 1)) :
    Quiver.Path c.source (WordCoordinates.vertex V c i) :=
  (Quiver.Path.cut c.path (c.cuts i) (c.cuts_le i)).leftPath

/-- Recover the SAME complete original suffix from the total path and actual cut. -/
def WordCoordinates.rightPath {n : ℕ} (c : WordCoordinates V n) (i : Fin (n + 1)) :
    Quiver.Path (WordCoordinates.vertex V c i) c.target :=
  (Quiver.Path.cut c.path (c.cuts i) (c.cuts_le i)).rightPath

/-- Whole original coordinate equality retains the complete native prefix. -/
lemma coordinates_leftPath_heq (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    HEq (WordCoordinates.leftPath V (coordinates V n w) i)
      (w.map (homOfLE (Fin.zero_le i))) :=
  (Quiver.Path.Cut.leftPath_heq_of_eq (wordCut_eq V n w i)).symm

/-- Whole original coordinate equality retains the complete native suffix. -/
lemma coordinates_rightPath_heq (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    HEq (WordCoordinates.rightPath V (coordinates V n w) i)
      (w.map (homOfLE (Fin.le_last i))) :=
  (Quiver.Path.Cut.rightPath_heq_of_eq (wordCut_eq V n w i)).symm

/-- Whole original coordinate equality preserves the complete dependent native prefix. -/
lemma WordCoordinates.leftPath_heq_of_eq {n : ℕ} {c d : WordCoordinates V n}
    (h : c = d) (i : Fin (n + 1)) :
    HEq (WordCoordinates.leftPath V c i) (WordCoordinates.leftPath V d i) := by
  cases h
  rfl

/-- Equality of entire original coordinates retains EVERY full original prefix. -/
lemma coordinates_prefix_heq (n : ℕ) (w w' : (nerve (Paths V)) _⦋n⦌)
    (h : coordinates V n w = coordinates V n w') (i : Fin (n + 1)) :
    HEq (w.map (homOfLE (Fin.zero_le i))) (w'.map (homOfLE (Fin.zero_le i))) := by
  have hp : HEq (WordCoordinates.leftPath V (coordinates V n w) i)
      (WordCoordinates.leftPath V (coordinates V n w') i) := by
    exact WordCoordinates.leftPath_heq_of_eq V h i
  exact (coordinates_leftPath_heq V n w i).symm.trans
    (hp.trans (coordinates_leftPath_heq V n w' i))

end CategoryTheory.FreePathNerveCoordinates
