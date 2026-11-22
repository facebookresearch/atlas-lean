/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubePrefixCylinder

/-!
# Actual zero-prefix charts in the right-cube contraction

Adjoining the original zero source is actual union with the original
minimal zero-to-middle prefix. Its cylinder union with the supplied
suffix is the cylinder of that zero-adjoined suffix. The original
quotient relation can then remove that genuine prefix chain.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeZeroPrefix
open PathLastMaximum RightCubeRelations RightCubePrefixCylinder
variable {n : ℕ}

/-- The original minimal zero-to-middle prefix retaining precisely its two supplied original endpoints. -/
def minimal (i : Fin (n + 1)) : Prefix.{u} i where
  I := {ULift.up.{u} (0 : Fin (n + 2)), ULift.up.{u} i.castSucc}
  left := Or.inl rfl
  right := Or.inr rfl
  left_le k _ := Fin.zero_le k.down
  le_right k := by rintro (rfl | rfl); exacts [Fin.zero_le _, le_rfl]

/-- Original zero adjunction is exactly whole union with the supplied minimal original prefix. -/
theorem prepend_eq (i : Fin (n + 1)) (r : LastPath.{u} i) :
    compose 0 i (minimal.{u} i) r = prependZero i r := by
  apply SimplicialThickening.Path.ext
  ext k
  change ((k = ULift.up.{u} (0 : Fin (n + 2)) ∨ k = ULift.up i.castSucc) ∨ k ∈ r.I) ↔
    (k = ULift.up.{u} (0 : Fin (n + 2)) ∨ k ∈ r.I)
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl h
    · exact Or.inr (h.symm ▸ r.left)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

/-- The actual whole constant original minimal prefix chain. -/
def minimalChain (i : Fin (n + 1)) (q : SimplexCategoryᵒᵖ) : (nerve (Prefix.{u} i)).obj q :=
  (Functor.const (Fin (q.unop.len + 1))).obj (minimal i)

/-- The whole zero-adjoined suffix chain is the original union chain with its same supplied minimal prefix. -/
theorem chain_prepend (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ} (r : (nerve (LastPath.{u} i)).obj q) :
    (minimalChain i q).prod' r ⋙ RightCubePrefixCylinder.composeFunctor i =
      r ⋙ prependFunctor i := by
  refine Functor.ext (fun j => prepend_eq i (r.obj j)) ?_
  intro j k f
  apply InducedCategory.Hom.ext
  exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.RightCubeZeroPrefix
