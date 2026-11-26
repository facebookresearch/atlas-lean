/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontInsertion
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightHomResolution

/-!
# Whole original operator naturality of fixed-front insertion

Every actual right-join operator commutes with the distinguished
enriched insertion and realization of the structural quotient map.
The whole equality follows from the same original identity simplices
and actual unit naturality, retaining all original scalar Hom cells.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontInsertionOperators
open SimplicialEnrichment FixedFrontInsertion PathMaximumOperators
variable {n m : ℕ}

/-- Each actual quotient operator reads the same original distinguished successor simplex as the genuine
  right-join restriction. -/
theorem simplex_operator (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    (FixedFrontOperators.map.{u} θ).app (op ⦋n + 1⦌) (simplex n) =
      (FixedFrontCollapse.object m).map (extension θ).op (simplex m) := by
  apply _root_.Quotient.sound
  left
  apply SSet.stdSimplex.objEquiv.injective
  ext i : 3
  rfl

/-- The entire original enriched insertion is natural for every actual right-join operator, not only its
  vertices or components. -/
theorem functor_operator (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    FixedFrontInsertion.functor.{u} n ≫ realizationMap (FixedFrontOperators.map θ) =
      coherentSimplexMap (extension θ) ≫ FixedFrontInsertion.functor m :=
  (unit_simplex_naturality (FixedFrontOperators.map θ) (simplex n)).trans
    ((congrArg (simplexInto (FixedFrontCollapse.object m)) (simplex_operator θ)).trans
      (simplexInto_operator (FixedFrontCollapse.object m) (extension θ) (simplex m)).symm)

end CategoryTheory.CoherentRealization.FixedFrontInsertionOperators
