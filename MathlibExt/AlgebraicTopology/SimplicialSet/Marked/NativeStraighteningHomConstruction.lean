/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningObject
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBasisChartHom
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.GeneratorBasisOriginalOver

/-!
# Actual universal maps between straightening and unstraightening

Whole chart maps give a cocone into native unstraightening on the
original marked basis. Its proved density supplies the actual
same-base forward map. Conversely each original same-base map gives
the entire native chart cocone, whose marked colimit supplies the
backward map. All maps are constructed on the original basis and
coherent-unit pullback, with no Hom-correspondence outcome input.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- A whole original straightening map determines its actual same-base marked basis cocone into unstraightening. -/
def nativeStraighteningForwardCocone (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (f : nativeStraighteningObject B X ⟶ F) :
    Cocone (GeneratorBasis.overDiagram X) where
  pt := (nativeUnstraightening B).obj F
  ι :=
    { app i := nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F
        (nativeStraighteningInjection B X i ≫ f)
      naturality i j g := by
        let gi := (CostructuredArrow.map X.hom).obj i
        let gj := (CostructuredArrow.map X.hom).obj j
        let h := (CostructuredArrow.map X.hom).map g
        have hc : nativeBasisChartMap B h ≫ nativeStraighteningInjection B X j =
            nativeStraighteningInjection B X i :=
          ((nativeStraighteningCocone B X).ι.naturality g).trans
            (Category.comp_id (nativeStraighteningInjection B X i))
        have he := nativeBasisChartEquiv_natural_left B h F (nativeStraighteningInjection B X j ≫ f)
        exact he.symm.trans
          ((congrArg (nativeBasisChartEquiv B gi F)
            ((Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ f) hc))).trans
              (Category.comp_id _).symm) }

/-- The native forward universal map is the original marked basis-density descent over the same actual base. -/
def nativeStraighteningForward (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (f : nativeStraighteningObject B X ⟶ F) :
    X ⟶ (nativeUnstraightening B).obj F :=
  (GeneratorBasis.originalOverIsColimit X).desc (nativeStraighteningForwardCocone B X F f)

/-- An original same-base marked map determines every whole native straightening chart map. -/
def nativeStraighteningBackwardCocone (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : X ⟶ (nativeUnstraightening B).obj F) :
    Cocone (nativeStraighteningDiagram B X) where
  pt := F
  ι :=
    { app i := (nativeBasisChartEquiv B ((CostructuredArrow.map X.hom).obj i) F).symm
        ((GeneratorBasis.originalOverCocone X).ι.app i ≫ g)
      naturality i j h := by
        let gi := (CostructuredArrow.map X.hom).obj i
        let gj := (CostructuredArrow.map X.hom).obj j
        let f := (CostructuredArrow.map X.hom).map h
        apply (nativeBasisChartEquiv B gi F).injective
        have hc : (nativeBasisFunctor B).map f ≫ (GeneratorBasis.originalOverCocone X).ι.app j =
            (GeneratorBasis.originalOverCocone X).ι.app i :=
          ((GeneratorBasis.originalOverCocone X).ι.naturality h).trans
            (Category.comp_id ((GeneratorBasis.originalOverCocone X).ι.app i))
        have he := nativeBasisChartEquiv_natural_left B f F
          ((nativeBasisChartEquiv B gj F).symm ((GeneratorBasis.originalOverCocone X).ι.app j ≫ g))
        exact he.trans
          ((congrArg (fun t => (nativeBasisFunctor B).map f ≫ t)
            ((nativeBasisChartEquiv B gj F).apply_symm_apply _)).trans
              ((Category.assoc _ _ _).symm.trans
                ((congrArg (fun t => t ≫ g) hc).trans
                  ((nativeBasisChartEquiv B gi F).apply_symm_apply _).symm))) }

/-- The actual native backward universal map is the entire marked chart-colimit descent. -/
def nativeStraighteningBackward (B : SSet.{u}) (X : Over (max B))
    (F : EnrichedDiagram (realization B)ᵒᵖ) (g : X ⟶ (nativeUnstraightening B).obj F) :
    nativeStraighteningObject B X ⟶ F :=
  (nativeStraighteningIsColimit B X).desc (nativeStraighteningBackwardCocone B X F g)

end SSet.Marked
