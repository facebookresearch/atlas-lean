/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningHomConstruction

/-!
# The whole actual straightening/unstraightening Hom correspondence

The genuine marked chart-colimit and original basis-density maps have
the proved native injection equations. Those equations and the actual
chart Hom inverses prove both whole inverse laws, constructing the
straightening/unstraightening Hom equivalence on every original marked
total space and original simplicial base. No Hom-outcome field is used.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original marked basis leg retains its actual chart map under the forward universal map. -/
theorem nativeStraighteningForward_basis (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (f : nativeStraighteningObject B X ⟶ F)
    (i : GeneratorBasis.Index X.left) :
    (GeneratorBasis.originalOverCocone X).ι.app i ≫ nativeStraighteningForward B X F f =
      nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F
        (nativeStraighteningInjection B X i ≫ f) :=
  (GeneratorBasis.originalOverIsColimit X).fac (nativeStraighteningForwardCocone B X F f) i

/-- Every entire original chart injection retains its actual basis map under the backward universal map. -/
theorem nativeStraighteningBackward_chart (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : X ⟶ (nativeUnstraightening B).obj F)
    (i : GeneratorBasis.Index X.left) :
    nativeStraighteningInjection B X i ≫ nativeStraighteningBackward B X F g =
      (nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F).symm
        ((GeneratorBasis.originalOverCocone X).ι.app i ≫ g) :=
  (nativeStraighteningIsColimit B X).fac (nativeStraighteningBackwardCocone B X F g) i

/-- Native backward after forward recovers every whole original straightening map, by actual chart-colimit detection. -/
theorem nativeStraighteningBackward_forward (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (f : nativeStraighteningObject B X ⟶ F) :
    nativeStraighteningBackward B X F (nativeStraighteningForward B X F f) = f := by
  apply (nativeStraighteningIsColimit B X).hom_ext
  intro i
  exact (nativeStraighteningBackward_chart B X F (nativeStraighteningForward B X F f) i).trans
    ((congrArg (nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F).symm
      (nativeStraighteningForward_basis B X F f i)).trans
        ((nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F).symm_apply_apply _))

/-- Native forward after backward recovers the entire original marked same-base map, by original basis density. -/
theorem nativeStraighteningForward_backward (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : X ⟶ (nativeUnstraightening B).obj F) :
    nativeStraighteningForward B X F (nativeStraighteningBackward B X F g) = g := by
  apply (GeneratorBasis.originalOverIsColimit X).hom_ext
  intro i
  exact (nativeStraighteningForward_basis B X F (nativeStraighteningBackward B X F g) i).trans
    ((congrArg (nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F)
      (nativeStraighteningBackward_chart B X F g i)).trans
        ((nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F).apply_symm_apply _))

/-- The actual one-fold marked straightening/unstraightening Hom equivalence, with both original whole-map
  inverses proved. -/
def nativeStraighteningHomEquiv (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) :
    (nativeStraighteningObject B X ⟶ F) ≃ (X ⟶ (nativeUnstraightening B).obj F) where
  toFun := nativeStraighteningForward B X F
  invFun := nativeStraighteningBackward B X F
  left_inv := nativeStraighteningBackward_forward B X F
  right_inv := nativeStraighteningForward_backward B X F

end SSet.Marked
