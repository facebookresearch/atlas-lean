/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Quiver.PathCuts
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Full original path-nerve words and their cumulative cuts

Every actual nerve word of the native path category retains its entire
original total path and the length of every original initial subpath.
Each actual intermediate object and full prefix/suffix is recovered by
native unique cuts. No original word, generator or arity is replaced.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The full original native total path of an arbitrary original nerve word. -/
def totalPath (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) :
    @Quiver.Path V inferInstance (w.obj 0) (w.obj (Fin.last n)) :=
  w.map (homOfLE (Fin.zero_le (Fin.last n)))

/-- The original cumulative cut position of EVERY original word vertex. -/
def cutPosition (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) : ℕ :=
  (w.map (homOfLE (Fin.zero_le i))).length

/-- The SAME entire original word is the native concatenation of its full original prefix and suffix. -/
lemma totalPath_split (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    (w.map (homOfLE (Fin.zero_le i))).comp (w.map (homOfLE (Fin.le_last i))) = totalPath V n w := by
  exact (w.map_comp (homOfLE (Fin.zero_le i)) (homOfLE (Fin.le_last i))).symm

/-- Each original cumulative position lies inside the SAME complete original total path. -/
lemma cutPosition_le (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    cutPosition V n w i ≤ (totalPath V n w).length := by
  change Fin (n + 1) ⥤ Paths V at w
  have h := congrArg Quiver.Path.length (totalPath_split V n w i)
  have hlen := Quiver.Path.length_comp (w.map (homOfLE (Fin.zero_le i)))
    (w.map (homOfLE (Fin.le_last i)))
  exact (hlen.symm.trans h) ▸ Nat.le_add_right _ _

/-- The actual original full prefix and suffix form the SAME native unique cut of the total path. -/
def wordCut (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    Quiver.Path.Cut (totalPath V n w) (cutPosition V n w i) where
  vertex := w.obj i
  leftPath := w.map (homOfLE (Fin.zero_le i))
  rightPath := w.map (homOfLE (Fin.le_last i))
  comp_eq := totalPath_split V n w i
  left_length := rfl

/-- EVERY original intermediate vertex and entire prefix/suffix are
recovered by the native unique cut of the SAME original total path. -/
lemma wordCut_eq (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    wordCut V n w i = Quiver.Path.cut (totalPath V n w) (cutPosition V n w i)
      (cutPosition_le V n w i) := by
  change Fin (n + 1) ⥤ Paths V at w
  exact @Subsingleton.elim (Quiver.Path.Cut (totalPath V n w) (cutPosition V n w i))
    (Quiver.Path.Cut.subsingleton _ _) _ _

/-- The same cumulative cut positions are monotone under the entire original path-word order. -/
lemma cutPosition_monotone (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) :
    Monotone (cutPosition V n w) := by
  change Fin (n + 1) ⥤ Paths V at w
  intro i j h
  have he := w.map_comp (homOfLE (Fin.zero_le i)) (homOfLE h)
  have hl := congrArg Quiver.Path.length he
  change (w.map (homOfLE (Fin.zero_le j))).length =
    ((w.map (homOfLE (Fin.zero_le i))).comp (w.map (homOfLE h))).length at hl
  have hlen := Quiver.Path.length_comp (w.map (homOfLE (Fin.zero_le i))) (w.map (homOfLE h))
  change (w.map (homOfLE (Fin.zero_le i))).length ≤ (w.map (homOfLE (Fin.zero_le j))).length
  exact (hl.trans hlen).symm ▸ Nat.le_add_right _ _

end CategoryTheory.FreePathNerveCoordinates
