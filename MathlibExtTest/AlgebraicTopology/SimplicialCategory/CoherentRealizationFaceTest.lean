/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentSimplexInsertion

open CategoryTheory CategoryTheory.CoherentRealization CategoryTheory.SimplicialEnrichment
open scoped Simplicial

universe u

-- Going through the coherent 1- and 2-simplices gives the same whole enriched face map.
example (i : Fin 3) :
    (simplexIso.{u} ⦋1⦌).hom ≫
        (coherentSimplexMap (SimplexCategory.δ i) ≫
          simplexInto (SSet.stdSimplex.{u}.obj ⦋2⦌) (topSimplex.{u} ⦋2⦌)) =
      realizationMap (SSet.stdSimplex.{u}.map (SimplexCategory.δ i)) := by
  rw [← Category.assoc, ← simplexIso_naturality, ← simplexIso_inverse_insertion,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]
