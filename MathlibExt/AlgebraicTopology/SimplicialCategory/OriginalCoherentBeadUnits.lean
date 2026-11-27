/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadCompositionLaws
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomUnitsAndEmpty

/-!
# The actual original zero-bead identity relation

A zero-dimensional original bead has the same two original vertices.
Its complete original singleton coefficient evaluates to the actual
original empty path, by the original identity relation.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead

open SimplicialEnrichment SimplicialQuiver

/-- A genuinely zero-dimensional original bead has the same actual original endpoints. -/
theorem zero_endpoints {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (b : Bead K x y q) (h : b.dimension = 0) : x = y := by
  cases b with
  | mk n σ hx hy p =>
    change n = 0 at h
    subst n
    exact hx.symm.trans hy

/-- The complete original zero bead is the actual original presented empty path. -/
theorem zero_evaluation {K : SSet.{u}} {x : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (b : Bead K x x q) (h : b.dimension = 0) :
    b.evaluation =
      _root_.Quotient.mk (congruence (relations K) q x x)
        (@Quiver.Path.nil (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x) := by
  cases b with
  | mk n σ hx hy p =>
    change n = 0 at h
    subst n
    change (simplexHom K σ (initial.{u} 0) (initial.{u} 0) hx hx).app q p = _
    have hp := HomUnitsAndEmpty.diagonalSimplex_unique
      (ULift.up.{u} (0 : Fin 1)) q p ((eId SSet.{u} (initial.{u} 0)).app q PUnit.unit)
    exact (congrArg ((simplexHom K σ (initial.{u} 0) (initial.{u} 0) hx hx).app q) hp).trans
      (_root_.Quotient.sound (Closure.relation (Equations.identity q σ (initial.{u} 0) hx)))

end CategoryTheory.CoherentRealization.OriginalBead
