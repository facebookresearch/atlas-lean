/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathMaximumOperators
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Whole scalar naturality of original maximum Hom maps

The actual direct-image path nerve, followed by the original maximum
map, commutes with the supplied front simplex operator in every scalar
degree. The source and target retain the same lifted original endpoints.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.MaximumNerveOperators
open PathLastMaximum PathMaximumOperators
variable {n m : ℕ}

/-- The whole original maximum Hom map to the actual front standard simplex. -/
def maximumMap (i : Fin (n + 1)) : nerve (LastPath.{u} i) ⟶ (Δ[n] : SSet.{u}) :=
  nerveMap (maximumFunctor i) ≫ (SSet.stdSimplex.isoNerve.{u} n).inv

/-- The original front label at every scalar vertex is exactly the actual path maximum. -/
theorem maximumMap_vertex (i : Fin (n + 1)) {d : ℕ}
    (p : (nerve (LastPath.{u} i)) _⦋d⦌) (j : Fin (d + 1)) :
    ((maximumMap i).app (op ⦋d⦌) p) j = maximum i (p.obj j) := rfl

/-- Every actual right-join path image commutes with the supplied front simplex operator as
a whole simplicial map. -/
theorem maximumMap_naturality (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    nerveMap (imageFunctor.{u} θ i) ≫ maximumMap (θ.toOrderHom i) =
      maximumMap i ≫ SSet.stdSimplex.map θ := by
  apply SSet.hom_ext
  intro q
  induction q using Opposite.rec with
  | _ q =>
    induction q using SimplexCategory.rec with
    | _ d =>
      apply ConcreteCategory.hom_ext
      intro p
      apply SSet.stdSimplex.ext
      intro j
      exact maximum_image θ i (p.obj j)

/-- Postcomposition by an original Hom simplex preserves the same whole operator comparison. -/
theorem maximumMap_postcompose {Y : SSet.{u}} (τ : (Δ[m] : SSet.{u}) ⟶ Y)
    (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    nerveMap (imageFunctor.{u} θ i) ≫ (maximumMap (θ.toOrderHom i) ≫ τ) =
      maximumMap i ≫ (SSet.stdSimplex.map θ ≫ τ) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ τ) (maximumMap_naturality θ i)).trans (Category.assoc _ _ _))

end CategoryTheory.CoherentRealization.MaximumNerveOperators
