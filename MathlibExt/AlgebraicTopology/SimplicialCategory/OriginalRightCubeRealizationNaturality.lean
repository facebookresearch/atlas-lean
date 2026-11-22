/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealizationSimplex

/-!
# Full original standard-simplex naturality and all existing colimits

The SAME genuine quotient-cube realization adjunction preserves
every existing colimit. The actual standard-simplex comparison is
a whole cosimplicial isomorphism, with the original coefficient
operator and both original maps retained.
-/

noncomputable section
universe u v w
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The actual original quotient-cube realization is left adjoint by its genuine original Hom equivalence. -/
instance isLeftAdjoint : functor.{u}.IsLeftAdjoint := adjunction.isLeftAdjoint

/-- The SAME original realization preserves every existing diagram colimit at independent index object and Hom
universes. -/
instance preservesColimits : PreservesColimitsOfSize.{v,w} functor.{u} := inferInstance

/-- Every original ordinal map retains the complete SAME standard-simplex realization comparison square. -/
theorem simplexIso_naturality {n m : SimplexCategory} (θ : n ⟶ m) :
    map (SSet.stdSimplex.{u}.map θ) ≫ (simplexIso m).hom =
      (simplexIso n).hom ≫ RightCubeCosimplicial.diagram.map θ := by
  apply colimit.hom_ext
  intro e
  have hCoeff :
      (diagram (SSet.stdSimplex.{u}.obj m)).map
        (toIdentity m ((SSet.stdSimplex.map θ).mapElements.op.obj e)) =
      (diagram (SSet.stdSimplex.{u}.obj n)).map (toIdentity n e) ≫
        RightCubeCosimplicial.diagram.map θ := by
    change RightCubeCosimplicial.diagram.map
        (SSet.stdSimplex.objEquiv ((SSet.stdSimplex.map θ).app e.unop.obj e.unop.val)) =
      RightCubeCosimplicial.diagram.map (SSet.stdSimplex.objEquiv e.unop.val) ≫
        RightCubeCosimplicial.diagram.map θ
    exact RightCubeCosimplicial.diagram.map_comp _ θ
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ (simplexIso m).hom) (insertion_map (SSet.stdSimplex.map θ) e)).trans
      ((insertion_simplexMap m _).trans
        (hCoeff.trans
          ((congrArg (fun q => q ≫ RightCubeCosimplicial.diagram.map θ)
            (insertion_simplexMap n e).symm).trans (Category.assoc _ _ _)))))

/-- The actual whole original cosimplicial standard-simplex realization isomorphism. -/
def standardIso :
    SSet.stdSimplex.{u} ⋙ functor.{u} ≅ RightCubeCosimplicial.diagram.{u} :=
  NatIso.ofComponents simplexIso (fun θ => simplexIso_naturality θ)

/-- Each SAME standard-simplex coefficient isomorphism is the literal original full cube comparison. -/
theorem standardIso_app (n : SimplexCategory) : standardIso.{u}.app n = simplexIso n := rfl

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
