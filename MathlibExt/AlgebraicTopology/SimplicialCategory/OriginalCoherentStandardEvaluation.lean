/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRepresentables
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCounitNaturality

/-!
# The SAME original standard-simplex evaluation and full Hom readback

The existing adjunction-derived standard simplex isomorphism is the
SAME original evaluation composite. Every original generating Hom is
read through its actual coherent simplex and exact endpoint equations.
No global Quillen-equivalence or weak comparison outcome is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization

open SimplicialEnrichment

/-- The SAME native standard-simplex nerve chart of the original identity coherent simplex. -/
def standardChart (n : SimplexCategory) : SSet.stdSimplex.{u}.obj n ⟶
    coherentNerveFunctor.obj (coherentSimplex.{u} n) :=
  SSet.yonedaEquiv.symm (𝟙 (coherentSimplex.{u} n))

/-- The original standard-simplex Iso has precisely its SAME genuine evaluation composite. -/
theorem simplexIso_hom_evaluation (n : SimplexCategory) :
    (simplexIso.{u} n).hom = realizationMap (standardChart n) ≫ counit (coherentSimplex.{u} n) := by
  rw [simplexIso_hom_eq]
  rfl

/-- EVERY whole original standard-simplex Hom retains the actual evaluation chart and
original endpoint equations. -/
theorem simplexIso_hom_simplexHom (n : SimplexCategory) {m : SimplexCategory}
    (σ : (SSet.stdSimplex.{u}.obj n).obj (op m)) (i j : coherentSimplex.{u} m)
    {x y : (SSet.stdSimplex.{u}.obj n) _⦋0⦌}
    (hx : vertex (SSet.stdSimplex.obj n) σ i = x) (hy : vertex (SSet.stdSimplex.obj n) σ j = y) :
    simplexHom (SSet.stdSimplex.obj n) σ i j hx hy ≫ (simplexIso.{u} n).hom.map x y =
      ((standardChart n).app (op m) σ).map i j ≫
        eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} n => a ⟶[SSet.{u}] b)
          (congrArg (vertexOf (coherentSimplex.{u} n))
            (vertex_image (standardChart n) σ i hx))
          (congrArg (vertexOf (coherentSimplex.{u} n))
            (vertex_image (standardChart n) σ j hy))) := by
  have hm := realizationMap_simplexHom (standardChart n) σ i j hx hy
  have hc := counit_simplexHom_reindex (coherentSimplex.{u} n)
    ((standardChart n).app (op m) σ) i j
      (vertex_image (standardChart n) σ i hx) (vertex_image (standardChart n) σ j hy)
  change simplexHom (SSet.stdSimplex.obj n) σ i j hx hy ≫
    ((realizationMap (standardChart n)).map x y ≫ (counit (coherentSimplex.{u} n)).map
      ((standardChart n).app (op ⦋0⦌) x) ((standardChart n).app (op ⦋0⦌) y)) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun e => e ≫ (counit (coherentSimplex.{u} n)).map
      ((standardChart n).app (op ⦋0⦌) x) ((standardChart n).app (op ⦋0⦌) y)) hm).trans hc)

/-- The SAME entire original native identity chart retains the original simplex operator. -/
theorem standardChart_operator {n m : SimplexCategory} (f : m ⟶ n) :
    (standardChart.{u} n).app (op m) (SSet.stdSimplex.objEquiv.symm f) = coherentSimplexMap f := by
  change coherentSimplexMap f ≫ 𝟙 (coherentSimplex.{u} n) = coherentSimplexMap f
  exact Category.comp_id _

end CategoryTheory.CoherentRealization
