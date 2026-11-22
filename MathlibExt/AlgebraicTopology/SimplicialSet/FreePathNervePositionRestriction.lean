/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveCoordinatesInjective
import MathlibExt.Combinatorics.Quiver.PathPositionWordMaps

/-!
# Every entire original nerve word is an original path-position restriction

The original whole word supplies its actual full total path and
monotone cumulative cuts. Its complete native prefix, interval and
suffix are the unique original cuts. Every object and Hom coefficient
is recovered by restricting the SAME full original position word.
-/

noncomputable section
universe u v
open CategoryTheory
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- The SAME original cumulative cuts give the actual ordinal map into the full original total word. -/
def cutOrdinal (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) :
    Fin (n + 1) →o Fin ((totalPath V n w).length + 1) where
  toFun i := ⟨cutPosition V n w i, Nat.lt_succ_of_le (cutPosition_le V n w i)⟩
  monotone' := cutPosition_monotone V n w

/-- Every SAME original word vertex is the actual original total-path cut vertex. -/
lemma cutOrdinal_vertex (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) (i : Fin (n + 1)) :
    Quiver.Path.positionVertex (V := V) (totalPath V n w) (cutOrdinal V n w i) = w.obj i :=
  (congrArg Quiver.Path.Cut.vertex (wordCut_eq V n w i)).symm

/-- The full original interval Hom is retained by native total-path cuts. -/
def wordIntervalCut (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) {i j : Fin (n + 1)} (f : i ⟶ j) :
    Quiver.Path.IntervalCut (totalPath V n w) (cutPosition V n w i) (cutPosition V n w j) where
  start := w.obj i
  stop := w.obj j
  leftPath := w.map (homOfLE (Fin.zero_le i))
  middlePath := w.map f
  rightPath := w.map (homOfLE (Fin.le_last j))
  comp_eq := by
    change Fin (n + 1) ⥤ Paths V at w
    exact (congrArg (fun a => a.comp (w.map (homOfLE (Fin.le_last j))))
      (w.map_comp (homOfLE (Fin.zero_le i)) f).symm).trans (totalPath_split V n w j)
  left_length := rfl
  left_middle_length := by
    exact congrArg Quiver.Path.length (w.map_comp (homOfLE (Fin.zero_le i)) f).symm

/-- The actual whole original interval coefficient is the SAME unique native interval cut. -/
lemma wordIntervalCut_eq (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) {i j : Fin (n + 1)} (f : i ⟶ j) :
    wordIntervalCut V n w f = Quiver.Path.intervalCut (totalPath V n w)
      (cutPosition V n w i) (cutPosition V n w j)
        (cutPosition_monotone V n w (leOfHom f)) (cutPosition_le V n w j) :=
  by
    change Fin (n + 1) ⥤ Paths V at w
    exact @Subsingleton.elim
      (Quiver.Path.IntervalCut (totalPath V n w) (cutPosition V n w i) (cutPosition V n w j))
      (Quiver.Path.IntervalCut.subsingleton _ _ _) _ _

/-- Whole native interval-cut equality retains the complete original middle path. -/
lemma intervalCut_middlePath_heq {x y : V} {p : Quiver.Path x y} {i j : ℕ}
    {c d : Quiver.Path.IntervalCut p i j} (h : c = d) : HEq c.middlePath d.middlePath := by
  cases h
  rfl

/-- Every SAME original full interval Hom is the actual original total-word interval. -/
lemma cutOrdinal_map_heq (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) {i j : Fin (n + 1)} (f : i ⟶ j) :
    HEq (w.map f) (Quiver.Path.positionPath (V := V) (totalPath V n w)
      (cutOrdinal V n w i) (cutOrdinal V n w j) ((cutOrdinal V n w).monotone (leOfHom f))) := by
  have hm := intervalCut_middlePath_heq V (wordIntervalCut_eq V n w f)
  exact hm.trans
    (@Quiver.homOfEq_heq (Paths V) (Paths.categoryPaths V).toCategoryStruct.toQuiver
      _ _ _ _ _ _ _).symm

/-- The SAME original entire native word is exactly its cumulative-cut
restriction of the complete original path-position word. -/
theorem original_word_restriction (n : ℕ) (w : (nerve (Paths V)) _⦋n⦌) :
    w = (cutOrdinal V n w).toFunctor ⋙ Quiver.Path.positionWord (V := V) (totalPath V n w) := by
  change Fin (n + 1) ⥤ Paths V at w
  refine Functor.hext (fun i => (cutOrdinal_vertex V n w i).symm) ?_
  intro i j f
  have hm := cutOrdinal_map_heq V n w f
  have hp := Quiver.Path.positionWord_map (V := V) (totalPath V n w) ((cutOrdinal V n w).toFunctor.map f)
  exact hm.trans (heq_of_eq hp).symm

end CategoryTheory.FreePathNerveCoordinates
