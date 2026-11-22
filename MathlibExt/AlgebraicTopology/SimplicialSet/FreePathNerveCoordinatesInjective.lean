/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FreePathNerveWordRecovery
import MathlibExt.Combinatorics.Quiver.PathCancellationTransport

/-!
# Every complete original path-nerve word is recovered

The full original total path and all original cumulative cut positions
recover every actual intermediate object and complete prefix. Native
path cancellation then recovers EVERY original interval Hom map, so
the whole original nerve word is determined losslessly at all arities.
-/

noncomputable section
universe u v
open CategoryTheory
open scoped Simplicial

namespace CategoryTheory.FreePathNerveCoordinates
variable (V : Type u) [Quiver.{v} V]

/-- Equal complete original coordinates retain EVERY native interval path. -/
lemma coordinates_hom_heq (n : ℕ) (w w' : (nerve (Paths V)) _⦋n⦌)
    (h : coordinates V n w = coordinates V n w') {i j : Fin (n + 1)} (f : i ⟶ j) :
    HEq (w.map f) (w'.map f) := by
  change Fin (n + 1) ⥤ Paths V at w w'
  have ha := coordinates_prefix_heq V n w w' h i
  have hb := coordinates_prefix_heq V n w w' h j
  have hcomp : HEq
      ((w.map (homOfLE (Fin.zero_le i))).comp (w.map f))
      ((w'.map (homOfLE (Fin.zero_le i))).comp (w'.map f)) :=
    (heq_of_eq (w.map_comp (homOfLE (Fin.zero_le i)) f).symm).trans
      (hb.trans (heq_of_eq (w'.map_comp (homOfLE (Fin.zero_le i)) f)))
  exact Quiver.Path.comp_heq_cancel_left.{u, v} (V := V) (coordinates_vertices V n w w' h 0)
    (coordinates_vertices V n w w' h i) (coordinates_vertices V n w w' h j) ha hcomp

/-- The actual full native word-coordinate map is injective, retaining
EVERY original object, full path, interval arrow and nerve arity. -/
theorem coordinates_injective (n : ℕ) : Function.Injective (coordinates V n) := by
  intro w w' h
  change Fin (n + 1) ⥤ Paths V at w w'
  exact Functor.hext (coordinates_vertices V n w w' h)
    (fun _ _ f => coordinates_hom_heq V n w w' h f)

end CategoryTheory.FreePathNerveCoordinates
