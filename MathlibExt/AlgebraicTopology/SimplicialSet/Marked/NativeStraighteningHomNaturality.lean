/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningHom

/-!
# Whole target naturality of native straightening/unstraightening

Original marked basis density detects the whole forward map. Each
basis leg uses the proved native chart Hom naturality, retaining the
same entire coefficient map and base projection. This proves the
actual universal Hom correspondence is natural in its target.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization

attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every whole native coefficient map commutes with the actual straightening/unstraightening universal
  correspondence. -/
theorem nativeStraighteningHomEquiv_natural_right (B : SSet.{u}) (X : Over (max B))
    {F G : EnrichedDiagram (realization B)ᵒᵖ}
    (f : nativeStraighteningObject B X ⟶ F) (φ : F ⟶ G) :
    nativeStraighteningHomEquiv B X G (f ≫ φ) =
      nativeStraighteningHomEquiv B X F f ≫ (nativeUnstraightening B).map φ := by
  apply (GeneratorBasis.originalOverIsColimit X).hom_ext
  intro i
  let j := (CostructuredArrow.map X.hom).obj i
  let k : nativeBasisChartObject B j ⟶ nativeStraighteningObject B X := nativeStraighteningInjection B X i
  let p : (nativeBasisFunctor B).obj j ⟶ X := (GeneratorBasis.originalOverCocone X).ι.app i
  have he := nativeBasisRepresenterHomEquiv_natural_right B j.left j.hom
    (k ≫ f) φ
  calc
    p ≫ nativeStraighteningHomEquiv B X G (f ≫ φ) =
        nativeBasisChartEquiv B j G (k ≫ (f ≫ φ)) :=
      nativeStraighteningForward_basis B X G (f ≫ φ) i
    _ = nativeBasisChartEquiv B j G ((k ≫ f) ≫ φ) :=
      congrArg (nativeBasisChartEquiv B j G) (Category.assoc _ _ _).symm
    _ = nativeBasisChartEquiv B j F (k ≫ f) ≫
        (nativeUnstraightening B).map φ := he
    _ = (p ≫ nativeStraighteningHomEquiv B X F f) ≫
        (nativeUnstraightening B).map φ :=
      congrArg (fun t => t ≫ (nativeUnstraightening B).map φ) (nativeStraighteningForward_basis B X F f i).symm
    _ = p ≫
        (nativeStraighteningHomEquiv B X F f ≫ (nativeUnstraightening B).map φ) := Category.assoc _ _ _

end SSet.Marked
