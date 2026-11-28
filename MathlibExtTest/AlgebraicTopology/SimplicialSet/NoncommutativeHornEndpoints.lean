/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/
module

import MathlibExt.AlgebraicTopology.SimplicialSet.SimplicialGroupKan
import Mathlib.GroupTheory.Perm.Basic

/-!
# First and last horn indices in a noncommutative simplicial group

The generic examples use the explicit filler and its face law without a commutativity
assumption. In the constant simplicial group on the permutations of Fin 3, two transpositions
do not commute. A lower correction replaces one by the other, and fillers with the first
and last missing indices recover the prescribed permutation on the remaining faces.
-/

noncomputable section

open CategoryTheory Opposite SSet.SimplicialGroupHorn
open scoped Simplicial

namespace MathlibExtTest.NoncommutativeHornEndpoints

attribute [local instance] SSet.SimplicialGroupHorn.underlyingGroup

universe u

example (G : SimplicialObject GrpCat.{u}) : SSet.KanComplex (underlying G) := inferInstance

example (G : SimplicialObject GrpCat.{u})
    (h : Fin 3 → (underlying G) _⦋1⦌) (hc : FaceCompatible G (0 : Fin 3) h) :
    (underlying G).δ (1 : Fin 3) (hornFiller G (0 : Fin 3) h) = h 1 :=
  hornFiller_face G 0 h hc 1 (by decide)

example (G : SimplicialObject GrpCat.{u})
    (h : Fin 3 → (underlying G) _⦋1⦌) (hc : FaceCompatible G (Fin.last 2) h) :
    (underlying G).δ (0 : Fin 3) (hornFiller G (Fin.last 2) h) = h 0 :=
  hornFiller_face G (Fin.last 2) h hc 0 (by decide)

private abbrev permutations : GrpCat.{0} := GrpCat.of (Equiv.Perm (Fin 3))
private abbrev constantGroup : SimplicialObject GrpCat.{0} :=
  (Functor.const (SimplexCategoryᵒᵖ)).obj permutations

private def a : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def b : Equiv.Perm (Fin 3) := Equiv.swap 1 2

example : a * b ≠ b * a := by decide

example : correctLower constantGroup (0 : Fin 1) a b = b := by
  have h := correctLower_face constantGroup (0 : Fin 1) a b
  change correctLower constantGroup (0 : Fin 1) a b = b at h
  exact h

private def faces : Fin 3 → (underlying constantGroup) _⦋1⦌ := fun _ => b

private theorem compatible (i : Fin 3) : FaceCompatible constantGroup i faces := by
  intro k j hkj hk hj
  rfl

example : hornFiller constantGroup (0 : Fin 3) faces = b := by
  have h := hornFiller_face constantGroup 0 faces (compatible 0) 1 (by decide)
  change hornFiller constantGroup (0 : Fin 3) faces = b at h
  exact h

example : hornFiller constantGroup (Fin.last 2) faces = b := by
  have h := hornFiller_face constantGroup (Fin.last 2) faces
    (compatible (Fin.last 2)) 0 (by decide)
  change hornFiller constantGroup (Fin.last 2) faces = b at h
  exact h

end MathlibExtTest.NoncommutativeHornEndpoints
