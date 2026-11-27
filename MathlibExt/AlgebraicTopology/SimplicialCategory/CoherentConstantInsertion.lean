/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomObjects

/-!
# Whole insertion of actual constant resolving simplices

The genuine coherent realization unit sends an original constant simplex
to the whole constant enriched functor at that same original vertex.
The proof uses the actual zero simplex and every original outer operator;
it does not assume a realization normal form.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.ConstantInsertion
open SimplicialEnrichment

/-- Inserting a supplied zero simplex retains its literal original vertex. -/
theorem zero_vertex (K : SSet.{u}) (x : K _⦋0⦌) (i : coherentSimplex.{u} ⦋0⦌) :
    vertex K x i = x := by
  have h : SimplexCategory.const ⦋0⦌ ⦋0⦌ i.as.down = 𝟙 ⦋0⦌ := by
    ext j : 3
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  change K.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ i.as.down).op x = x
  rw [h, op_id, K.map_id]
  rfl

/-- The whole original zero-simplex insertion is the constant enriched functor at that same
individual vertex. -/
theorem zero (K : SSet.{u}) (x : K _⦋0⦌) :
    simplexInto K x = constantSimplex (realization K) ⦋0⦌ x := by
  have h := constant_vertexOf (realization K) (simplexInto K x)
  have hv : vertexOf (realization K) (simplexInto K x) = x := zero_vertex K x zeroPoint
  exact h.symm.trans (congrArg (constantSimplex (realization K) ⦋0⦌) hv)

/-- Precomposition of the original constant enriched functor by any actual resolving
operator is constant at
  the same supplied object. -/
theorem precompose {C : Carrier.{u}} {n m : SimplexCategory} (θ : n ⟶ m) (x : C) :
    coherentSimplexMap θ ≫ constantSimplex C m x = constantSimplex C n x := by
  refine EnrichedFunctor.ext SSet.{u} (fun _ => rfl) ?_
  intro i j
  change ((coherentSimplexMap θ).map i j ≫ (toUnit _ ≫ eId SSet.{u} x)) ≫ 𝟙 _ =
    toUnit _ ≫ eId SSet.{u} x
  rw [Category.comp_id]
  ext q a
  rfl

/-- The actual realization unit inserts an entire original constant simplex as the constant enriched
  functor, including all original Hom maps. -/
theorem constant (K : SSet.{u}) (n : SimplexCategory) (x : K _⦋0⦌) :
    simplexInto K (K.map (SimplexCategory.const n ⦋0⦌ 0).op x) =
      constantSimplex (realization K) n x :=
  (simplexInto_operator K (SimplexCategory.const n ⦋0⦌ 0) x).symm.trans
    ((congrArg (fun F => coherentSimplexMap (SimplexCategory.const n ⦋0⦌ 0) ≫ F)
      (zero K x)).trans (precompose (C := realization K) (SimplexCategory.const n ⦋0⦌ 0) x))

end CategoryTheory.CoherentRealization.ConstantInsertion
