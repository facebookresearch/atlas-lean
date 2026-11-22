/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeZeroPrefix

/-!
# Actual relation compatibility of the original right-cube cylinder

The simultaneous original prefix and suffix cylinders factor the whole
original union cylinder. The defining front-composition relation removes
that actual prefix. The minimal original zero-prefix gives the second
comparison. Both steps are proved on the same whole original scalar
chain, including changing interval labels.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeCylinderRelations
open PathLastMaximum RightCubeRelations RightCubeZeroPrefix
variable {n : ℕ}

/-- The actual original whole union cylinder is related to its same original contracted last factor. -/
theorem union_relation (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (RightCubePrefixCylinder.Prefix.{u} i)).obj q)
    (r : (nerve (LastPath.{u} i)).obj q) (t : (Δ[1] : SSet.{u}).obj q) :
    (setoid.{u} n q).r
      (RightCubeCylinder.chain 0 (p.prod' r ⋙ RightCubePrefixCylinder.composeFunctor i) t)
      (RightCubeCylinder.chain i r t ⋙ prependFunctor i) := by
  have h := RightCubePrefixCylinder.chain_union i p r t
  have hR := Relation.composition (n := n) i (RightCubePrefixCylinder.chain i p t) (RightCubeCylinder.chain i r t)
  exact h ▸ Relation.EqvGen.rel _ _ hR

/-- The actual cylinder of zero-adjoined original suffix is related to the same original contracted suffix
  with zero adjoined afterward. -/
theorem prepend_relation (i : Fin (n + 1)) {q : SimplexCategoryᵒᵖ}
    (r : (nerve (LastPath.{u} i)).obj q) (t : (Δ[1] : SSet.{u}).obj q) :
    (setoid.{u} n q).r (RightCubeCylinder.chain 0 (r ⋙ prependFunctor i) t)
      (RightCubeCylinder.chain i r t ⋙ prependFunctor i) := by
  have h := chain_prepend i r
  have hC := congrArg (fun p => RightCubeCylinder.chain 0 p t) h
  exact hC ▸ union_relation i (minimalChain i q) r t

/-- Every actual generating original front-prefix relation is preserved by the entire original cube cylinder. -/
theorem relation_compatible {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q} (h : Relation n a b)
    (t : (Δ[1] : SSet.{u}).obj q) :
    (setoid.{u} n q).r (RightCubeCylinder.chain 0 a t) (RightCubeCylinder.chain 0 b t) := by
  cases h with
  | composition i p r =>
    exact Relation.EqvGen.trans _ _ _ (union_relation i p r t)
      (Relation.EqvGen.symm _ _ (prepend_relation i r t))

/-- The entire actual equivalence closure of original right-cube relations is preserved by the same original
  scalar cylinder simplex. -/
theorem compatible {q : SimplexCategoryᵒᵖ}
    {a b : (nerve (LastPath.{u} (0 : Fin (n + 1)))).obj q} (h : (setoid.{u} n q).r a b)
    (t : (Δ[1] : SSet.{u}).obj q) :
    (setoid.{u} n q).r (RightCubeCylinder.chain 0 a t) (RightCubeCylinder.chain 0 b t) := by
  induction h with
  | rel a b h => exact relation_compatible h t
  | refl a => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c h h' ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

end CategoryTheory.CoherentRealization.RightCubeCylinderRelations
