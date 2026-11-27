/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.SheafHypercoverModels
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-! Degree zero has the actual terminal relative matching object.
The two degree-one projections are the two distinct original face maps,
with the native simplex indices. This checks the augmentation boundary
and orientation used by global hyperdescent comparisons.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.CategoryTheory.SheafHypercoverModels

noncomputable section

private instance : IsEmpty (SSet.boundary.{0} 0).toSSet.Elements := ⟨fun x ↦ by
  have hx : x.val.val ∈ (SSet.boundary.{0} 0).obj x.obj := x.val.property
  simp only [SSet.boundary_zero, Subfunctor.bot_obj, Set.mem_empty_iff_false] at hx⟩

variable {C : Type 1} [Category C] {J : GrothendieckTopology C}
  (F : Sheaf J (Type 1)) (H : Diagram F)

example : IsTerminal (matchingObject H 0) :=
  (isLimitEquivIsTerminalOfIsEmpty (Over F) (limit.cone (boundaryDiagram H 0)))
    (limit.isLimit (boundaryDiagram H 0))

private def vertex (i : Fin 2) : (SSet.boundary.{0} 1).toSSet.Elements :=
  { obj := op (SimplexCategory.mk 0)
    val := ⟨ULift.up (SimplexCategory.δ i), by
      rw [SSet.boundary_obj_eq_univ 0 1]
      trivial⟩ }

example : matchingMap H 1 ≫ limit.π (boundaryDiagram H 1) (vertex 0) =
    H.map (SimplexCategory.δ (0 : Fin 2)).op := by
  rw [matchingMap_projection]
  rfl

example : matchingMap H 1 ≫ limit.π (boundaryDiagram H 1) (vertex 1) =
    H.map (SimplexCategory.δ (1 : Fin 2)).op := by
  rw [matchingMap_projection]
  rfl

#print axioms MathlibExt.CategoryTheory.SheafHypercoverModels.matchingMap
#print axioms MathlibExt.CategoryTheory.SheafHypercoverModels.matchingMap_projection
