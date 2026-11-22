/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveLengthCellCoordinates

/-!
# The SAME original full-span cell recovers its complete original word

Full-span ordinal coefficients retain zero and last positions. The
actual original position path between them is the SAME original total
path. All original cumulative cut coefficients then recover the
original path label and entire original ordinal coefficient.
-/

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial
namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- Every actual original zero cut retains the SAME individual source vertex. -/
lemma positionVertex_zero {x y : V} (p : Quiver.Path x y) :
    Quiver.Path.positionVertex (V := V) p 0 = x := by
  let c : Quiver.Path.Cut (V := V) p 0 := ⟨x, Quiver.Path.nil, p, Quiver.Path.nil_comp p, rfl⟩
  exact congrArg Quiver.Path.Cut.vertex (Subsingleton.elim (Quiver.Path.cut (V := V) p 0 (Nat.zero_le _)) c)

/-- Every actual original last cut retains the SAME individual target vertex. -/
lemma positionVertex_last {x y : V} (p : Quiver.Path x y) :
    Quiver.Path.positionVertex (V := V) p (Fin.last p.length) = y := by
  let c : Quiver.Path.Cut (V := V) p p.length := ⟨y, p, Quiver.Path.nil, Quiver.Path.comp_nil p, rfl⟩
  exact congrArg Quiver.Path.Cut.vertex (Subsingleton.elim (Quiver.Path.cut (V := V) p p.length le_rfl) c)

/-- The full original position word's total native path is the SAME original full path. -/
lemma positionWord_totalPath_heq {x y : V} (p : Quiver.Path x y) :
    HEq (totalPath V p.length (Quiver.Path.positionWord (V := V) p)) p := by
  have hm := Quiver.Path.positionWord_map (V := V) p (homOfLE (Fin.zero_le (Fin.last p.length)))
  let c : Quiver.Path.IntervalCut (V := V) p 0 p.length :=
    ⟨x, y, Quiver.Path.nil, p, Quiver.Path.nil,
      (Quiver.Path.comp_nil _).trans (Quiver.Path.nil_comp _), rfl,
      congrArg Quiver.Path.length (Quiver.Path.nil_comp p)⟩
  have hc : Quiver.Path.intervalCut (V := V) p 0 p.length (Nat.zero_le _) le_rfl = c :=
    Subsingleton.elim _ _
  have hmid := intervalCut_middlePath_heq V hc
  have ht := @Quiver.homOfEq_heq (Paths V) (Paths.categoryPaths V).toCategoryStruct.toQuiver
    _ _ _ _ (Quiver.Path.intervalCut_start_eq (V := V) p 0 (Fin.last p.length) (Fin.zero_le _))
      (Quiver.Path.intervalCut_stop_eq (V := V) p 0 (Fin.last p.length) (Fin.zero_le _))
      (Quiver.Path.intervalCut (V := V) p 0 p.length (Nat.zero_le _) le_rfl).middlePath
  exact (heq_of_eq hm).trans (ht.trans hmid)

/-- Actual original position equalities preserve the SAME full native interval path. -/
lemma positionPath_heq_of_positions {x y : V} (p : Quiver.Path x y)
    {i j i' j' : Fin (p.length + 1)} (hi : i = i') (hj : j = j') (h : i ≤ j) (h' : i' ≤ j') :
    HEq (Quiver.Path.positionPath (V := V) p i j h) (Quiver.Path.positionPath (V := V) p i' j' h') := by
  cases hi
  cases hj
  rfl

/-- The SAME full-span original cell coefficient retains the entire original native total path. -/
lemma wordCell_totalPath_heq {x y : V} (p : Quiver.Path x y) (n : ℕ)
    (a : (Δ[p.length] : SSet.{max u v}) _⦋n⦌)
    (h0 : a (0 : Fin (n + 1)) = 0) (hl : a (Fin.last n) = Fin.last p.length) :
    HEq (totalPath V n ((wordCell V p).app (op ⦋n⦌) a)) p := by
  have ht : HEq (totalPath V n ((wordCell V p).app (op ⦋n⦌) a))
      ((Quiver.Path.positionWord (V := V) p).map
        (homOfLE ((SSet.stdSimplex.asOrderHom a).monotone (Fin.zero_le (Fin.last n))))) := HEq.rfl
  have hm := Quiver.Path.positionWord_map (V := V) p
    (homOfLE ((SSet.stdSimplex.asOrderHom a).monotone (Fin.zero_le (Fin.last n))))
  have hp : HEq (Quiver.Path.positionPath (V := V) p (a (0 : Fin (n + 1))) (a (Fin.last n))
      ((SSet.stdSimplex.asOrderHom a).monotone (Fin.zero_le (Fin.last n))))
      (Quiver.Path.positionPath (V := V) p 0 (Fin.last p.length) (Fin.zero_le _)) := by
    exact positionPath_heq_of_positions V p h0 hl _ _
  have hwhole := positionWord_totalPath_heq V p
  have hm0 := Quiver.Path.positionWord_map (V := V) p (homOfLE (Fin.zero_le (Fin.last p.length)))
  exact ht.trans ((heq_of_eq hm).trans
    (hp.trans ((heq_of_eq hm0).symm.trans hwhole)))

/-- Every full-span coefficient has the SAME individual original source vertex. -/
lemma wordCell_source {x y : V} (p : Quiver.Path x y) (n : ℕ)
    (a : (Δ[p.length] : SSet.{max u v}) _⦋n⦌) (h0 : a (0 : Fin (n + 1)) = 0) :
    ((wordCell V p).app (op ⦋n⦌) a).obj 0 = x := by
  change Quiver.Path.positionVertex (V := V) p (a (0 : Fin (n + 1))) = x
  exact (congrArg (fun i => Quiver.Path.positionVertex (V := V) p i) h0).trans (positionVertex_zero V p)

/-- Every full-span coefficient has the SAME individual original target vertex. -/
lemma wordCell_target {x y : V} (p : Quiver.Path x y) (n : ℕ)
    (a : (Δ[p.length] : SSet.{max u v}) _⦋n⦌) (hl : a (Fin.last n) = Fin.last p.length) :
    ((wordCell V p).app (op ⦋n⦌) a).obj (Fin.last n) = y := by
  change Quiver.Path.positionVertex (V := V) p (a (Fin.last n)) = y
  exact (congrArg (fun i => Quiver.Path.positionVertex (V := V) p i) hl).trans (positionVertex_last V p)

end CategoryTheory.FreePathNerveCoordinates
