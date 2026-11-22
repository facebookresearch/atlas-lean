/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Combinatorics.Quiver.PathPositionFunctorLaws
import MathlibExt.Combinatorics.Quiver.PathCancellationTransport

/-!
# Complete original position-path identity and composition

Actual original prefix/interval concatenation follows from native
unique cuts and the exact endpoint transports. Native original path
cancellation gives every interval identity and composition law.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.Path
variable {V : Type u} [Quiver.{v} V] {x y : V}

/-- Native concatenation retains the SAME full paths under actual endpoint equalities. -/
lemma comp_heq_of_heq {a b c a' b' c' : V} (ha : a = a') (hb : b = b') (hc : c = c')
    {p : Path a b} {p' : Path a' b'} {q : Path b c} {q' : Path b' c'}
    (hp : HEq p p') (hq : HEq q q') : HEq (p.comp q) (p'.comp q') := by
  subst a'
  subst b'
  subst c'
  exact heq_of_eq (congrArg₂ Quiver.Path.comp (eq_of_heq hp) (eq_of_heq hq))

/-- The original full prefix followed by the SAME actual interval is
exactly the original longer prefix, with every generating arrow retained. -/
lemma positionPrefix_comp_positionPath (p : Path x y) (i j : Fin (p.length + 1)) (h : i ≤ j) :
    (positionPrefix (V := V) p i).comp (positionPath (V := V) p i j h) =
      positionPrefix (V := V) p j := by
  let c := intervalCut p i.val j.val h (Nat.le_of_lt_succ j.isLt)
  have hl := intervalCut_left_heq p i j h
  have hm : HEq c.middlePath (positionPath (V := V) p i j h) :=
    (@Quiver.homOfEq_heq (Paths V) (Paths.categoryPaths V).toCategoryStruct.toQuiver
      _ _ _ _ (intervalCut_start_eq p i j h) (intervalCut_stop_eq p i j h) c.middlePath).symm
  have hc := comp_heq_of_heq (V := V) rfl (intervalCut_start_eq p i j h)
    (intervalCut_stop_eq p i j h) hl hm
  exact eq_of_heq (hc.symm.trans (intervalCut_left_middle_heq p i j h))

/-- The SAME original interval at a single original position is the empty native path. -/
lemma positionPath_refl (p : Path x y) (i : Fin (p.length + 1)) :
    positionPath (V := V) p i i le_rfl = Quiver.Path.nil := by
  apply comp_injective_right (positionPrefix (V := V) p i)
  exact (positionPrefix_comp_positionPath p i i le_rfl).trans (Quiver.Path.comp_nil _).symm

/-- All full original interval paths compose as SAME native original subpaths. -/
lemma positionPath_comp (p : Path x y) (i j k : Fin (p.length + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    (positionPath (V := V) p i j hij).comp (positionPath (V := V) p j k hjk) =
      positionPath (V := V) p i k (hij.trans hjk) := by
  apply comp_injective_right (positionPrefix (V := V) p i)
  rw [← Quiver.Path.comp_assoc, positionPrefix_comp_positionPath,
    positionPrefix_comp_positionPath, positionPrefix_comp_positionPath]

end Quiver.Path
