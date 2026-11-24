/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCounitNaturality
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The genuine coherent realization and nerve adjunction

The left adjoint is the actual simplicial presentation on the original
input vertices. Its unit and evaluation counit are the constructed maps.
Both full triangle identities follow from literal generator evaluation
and original endpoint equations; neither is an assumption.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- The zero-simplex vertex is literally the same individual original input vertex. -/
theorem vertex_zero (K : SSet.{u}) (x : K _⦋0⦌) : vertex K x zeroPoint = x := by
  change K.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x = x
  rw [SimplexCategory.const_eq_id]
  exact congr($(K.map_id (op ⦋0⦌)) x)

/-- The realization triangle holds on every whole original coherent Hom with its exact
endpoint equations. -/
theorem realization_triangle_simplexHom (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) :
    (simplexHom K σ i j hx hy ≫ (realizationMap (unit K) ≫ counit (realization K)).map x y) ≫
      eqToHom (congrArg₂ (hom K) (vertex_zero K x) (vertex_zero K y)) =
        simplexHom K σ i j hx hy := by
  let η := unit K
  let hx' := vertex_image η σ i hx
  let hy' := vertex_image η σ j hy
  let Hx : vertex K σ i = vertex K x zeroPoint := congrArg (vertexOf (realization K)) hx'
  let Hy : vertex K σ j = vertex K y zeroPoint := congrArg (vertexOf (realization K)) hy'
  have hm := realizationMap_simplexHom η σ i j hx hy
  have hc := counit_simplexHom_reindex (realization K) (simplexInto K σ) i j hx' hy'
  change simplexHom (coherentNerveFunctor.obj (realization K)) (simplexInto K σ) i j hx' hy' ≫
    (counit (realization K)).map (η.app (op ⦋0⦌) x) (η.app (op ⦋0⦌) y) =
      simplexHom K σ i j rfl rfl ≫ eqToHom (congrArg₂ (hom K) Hx Hy) at hc
  have hj := (congrArg (fun t => t ≫ (counit (realization K)).map
    (η.app (op ⦋0⦌) x) (η.app (op ⦋0⦌) y)) hm).trans hc
  have hw := congrArg (fun t => t ≫ eqToHom (congrArg₂ (hom K) (vertex_zero K x) (vertex_zero K y)))
    (hj.trans (simplexHom_reindex K σ i j Hx Hy))
  change (simplexHom K σ i j hx hy ≫ ((realizationMap η).map x y ≫
    (counit (realization K)).map (η.app (op ⦋0⦌) x) (η.app (op ⦋0⦌) y))) ≫
      eqToHom (congrArg₂ (hom K) (vertex_zero K x) (vertex_zero K y)) = simplexHom K σ i j hx hy
  exact (congrArg (fun t => t ≫ eqToHom (congrArg₂ (hom K)
    (vertex_zero K x) (vertex_zero K y)))
      (Category.assoc (simplexHom K σ i j hx hy) ((realizationMap η).map x y)
        ((counit (realization K)).map (η.app (op ⦋0⦌) x) (η.app (op ⦋0⦌) y))).symm).trans
          (hw.trans (simplexHom_reindex_comp K σ i j Hx Hy (vertex_zero K x) (vertex_zero K y)))

/-- The whole realization triangle is the enriched identity, preserving every original input
vertex and Hom path. -/
theorem realization_triangle (K : SSet.{u}) :
    realizationMap (unit K) ≫ counit (realization K) = 𝟙 (realization K) := by
  refine CoherentRealization.hom_ext (funext (vertex_zero K)) ?_
  intro x y
  ext q a
  cases a with
  | mk n σ i j hx hy a =>
      exact congr($(realization_triangle_simplexHom K σ i j hx hy).app q a)

/-- The genuine original coherent realization and nerve adjunction, with both actual
triangles proved. -/
def realizationAdjunction : realizationFunctor.{u} ⊣ coherentNerveFunctor where
  unit := unitNatTrans
  counit := counitNatTrans
  left_triangle_components := realization_triangle
  right_triangle_components := nerve_triangle

/-- The actual adjunction unit is precisely the whole original simplex insertion map. -/
theorem realizationAdjunction_unit (K : SSet.{u}) : realizationAdjunction.unit.app K = unit K := rfl

/-- The actual adjunction counit is precisely the whole original enriched generator
evaluation map. -/
theorem realizationAdjunction_counit (C : Carrier.{u}) : realizationAdjunction.counit.app C
  = counit C := rfl

/-- The genuine coherent Hom equivalence is a natural bijection of actual strict maps. -/
def coherentHomEquiv (K : SSet.{u}) (C : Carrier.{u}) :
    (realization K ⟶ C) ≃ (K ⟶ coherentNerveFunctor.obj C) := realizationAdjunction.homEquiv K C

end CategoryTheory.CoherentRealization
