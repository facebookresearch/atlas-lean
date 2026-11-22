/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNervePositionRestriction
import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex

/-!
# The SAME original full path-nerve word-length filtration

Every original ordinal restriction retains the complete original
subinterval path. Its length is bounded by the SAME full total word.
The native length filtration keeps all original coefficients and
yields the actual generating graph as its length-one subcomplex.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- EVERY original interval subpath has length bounded by the SAME full original total path. -/
lemma wordMap_length_le (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) {i j : Fin (n + 1)} (f : i ⟶ j) :
    (w.map f).length ≤ (totalPath V n w).length := by
  change Fin (n + 1) ⥤ Paths V at w
  let c := wordIntervalCut V n w f
  have h := congrArg Quiver.Path.length c.comp_eq
  have hlen := Quiver.Path.length_comp (c.leftPath.comp c.middlePath) c.rightPath
  have hlen' := Quiver.Path.length_comp c.leftPath c.middlePath
  have htotal : c.leftPath.length + c.middlePath.length + c.rightPath.length = (totalPath V n w).length :=
    (congrArg (fun k => k + c.rightPath.length) hlen').symm.trans (hlen.symm.trans h)
  change c.middlePath.length ≤ (totalPath V n w).length
  omega

/-- EVERY actual original ordinal restriction retains a bounded full original total subpath. -/
lemma totalPath_operator_length_le {n m : SimplexCategory} (f : n ⟶ m)
    (w : (nerve (Paths V)).obj (op m)) :
    (totalPath V n.len ((nerve (Paths V)).map f.op w)).length ≤ (totalPath V m.len w).length :=
  wordMap_length_le V m.len w (homOfLE
    (f.toOrderHom.monotone (Fin.zero_le (Fin.last n.len))))

/-- The native original full path-nerve subcomplex retaining complete words of bounded total length. -/
def lengthStage (k : ℕ) : (nerve (Paths V)).Subcomplex where
  obj q := {w | (totalPath V q.unop.len w).length ≤ k}
  map {q r} f w hw := (totalPath_operator_length_le V (n := r.unop) (m := q.unop) f.unop w).trans hw

/-- The SAME actual original generating graph keeps the full length-zero/one native words. -/
abbrev generatingGraph : (nerve (Paths V)).Subcomplex := lengthStage V 1

/-- Every full original bounded word remains in the next actual native stage. -/
lemma lengthStage_mono {k l : ℕ} (h : k ≤ l) : lengthStage V k ≤ lengthStage V l :=
  fun _ _ hw => hw.trans h

/-- All original words occur in the entire native original length filtration. -/
lemma lengthStage_iSup : (⨆ k : ℕ, lengthStage V k) = ⊤ := by
  ext q w
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.top_obj, Set.mem_univ, iff_true]
  exact ⟨(totalPath V q.unop.len w).length, show (totalPath V q.unop.len w).length ≤ (totalPath V q.unop.len
    w).length from le_rfl⟩

end CategoryTheory.FreePathNerveCoordinates
