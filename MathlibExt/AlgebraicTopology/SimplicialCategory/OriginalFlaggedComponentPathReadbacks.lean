/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentOperatorRelation
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalFlaggedComponentIdentityRelation

/-!
# SAME whole original path and operator interpretation readbacks

The actual original coherent-generator interpretation evaluates every
whole original path by the SAME zero necklace and native concatenation.
The original identity and every outer-operator equation are retained as
literal equalities of these original component labels.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components

open OriginalBead SimplicialEnrichment SimplicialQuiver

/-- EVERY SAME original coherent generator has its literal actual flagged-object component. -/
theorem interpretation_arrow {K : SSet.{u}} {x y : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (a : Arrow K x y q) :
    (interpretation K).evalPath q
      (arrowPath K a.simplex a.source a.target a.source_eq a.target_eq a.hom) =
        ConnectedComponents.mk (generatorObject a) :=
  ConcreteCategory.congr_hom (congr_app ((interpretation K).generator_eval x y) q) a

/-- The SAME complete original empty path retains the original zero necklace. -/
theorem interpretation_empty (K : SSet.{u}) (x : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (interpretation K).evalPath q (@Quiver.Path.nil (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x) =
      ConnectedComponents.mk (unit K q x) := rfl

/-- The SAME whole original path concatenation retains both complete original component labels. -/
theorem interpretation_comp {K : SSet.{u}} {x y z : K _⦋0⦌} {q : SimplexCategoryᵒᵖ}
    (p : SimplicialQuiver.Path (generatingQuiver K) q x y)
    (r : SimplicialQuiver.Path (generatingQuiver K) q y z) :
    (interpretation K).evalPath q
      (@Quiver.Path.comp (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x y z p r) =
        concatenate ((interpretation K).evalPath q p) ((interpretation K).evalPath q r) :=
  (interpretation K).evalPath_comp q p r

/-- The SAME actual original outer-operator equation is retained on the entire original paths. -/
theorem interpretation_operator {K : SSet.{u}} {n m : SimplexCategory}
    (f : n ⟶ m) (σ : K.obj (op m)) (i j : coherentSimplex.{u} n)
    {x y : K _⦋0⦌} (hx : vertex K (K.map f.op σ) i = x)
    (hy : vertex K (K.map f.op σ) j = y) {q : SimplexCategoryᵒᵖ}
    (a : (i ⟶[SSet.{u}] j).obj q) :
    (interpretation K).evalPath q (arrowPath K (K.map f.op σ) i j hx hy a) =
      (interpretation K).evalPath q
        (arrowPath K σ ((coherentSimplexMap f).obj i) ((coherentSimplexMap f).obj j)
          ((vertex_operator K f σ i).symm.trans hx) ((vertex_operator K f σ j).symm.trans hy)
          (((coherentSimplexMap f).map i j).app q a)) :=
  (interpretation_arrow (operatorSource f σ i j hx hy a)).trans
    ((operator_component f σ i j hx hy a).trans
      (interpretation_arrow (operatorTarget f σ i j hx hy a)).symm)

end CategoryTheory.CoherentRealization.OriginalFlaggedNecklace.Components
