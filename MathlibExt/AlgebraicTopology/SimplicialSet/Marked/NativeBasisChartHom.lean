/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBasisChartFunctor

/-!
# The complete original basis-chart Hom naturality

The actual universal Hom maps are the original basis unit followed by
the native unstraightening map. Original basis-map and target
naturality prove the whole source naturality square, retaining all
marked components and the original base equations.
-/

noncomputable section
universe u
open CategoryTheory

namespace SSet.Marked
open CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original basis-chart universal map is exactly the same basis unit and actual unstraightening map. -/
theorem nativeBasisChartEquiv_unit (B : SSet.{u}) (i : GeneratorBasis.Index (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (f : nativeBasisChartObject B i ⟶ F) :
    nativeBasisChartEquiv B i F f = nativeBasisChartUnit B i ≫ (nativeUnstraightening B).map f := by
  have h := nativeBasisRepresenterHomEquiv_natural_right B i.left i.hom
    (𝟙 (nativeBasisChartObject B i)) f
  exact (congrArg (nativeBasisRepresenterHomEquiv B i.left i.hom F) (Category.id_comp f)).symm.trans h

/-- The actual basis-chart Hom correspondence is natural for every original whole marked source basis map. -/
theorem nativeBasisChartEquiv_natural_left (B : SSet.{u})
    {i j : GeneratorBasis.Index (max B)} (f : i ⟶ j)
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : nativeBasisChartObject B j ⟶ F) :
    nativeBasisChartEquiv B i F (nativeBasisChartMap B f ≫ g) =
      (nativeBasisFunctor B).map f ≫ nativeBasisChartEquiv B j F g := by
  have h := nativeBasisRepresenterHomEquiv_natural_right B i.left i.hom (nativeBasisChartMap B f) g
  exact h.trans
    ((congrArg (fun t => t ≫ (nativeUnstraightening B).map g) (nativeBasisChartMap_equiv B f)).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => (nativeBasisFunctor B).map f ≫ t) (nativeBasisChartEquiv_unit B j F g).symm)))

end SSet.Marked
