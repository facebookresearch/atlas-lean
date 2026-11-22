/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealizationAdjunction

/-!
# Same quotient-cube realization of every original standard simplex

The original complete element diagram has its original identity
simplex as terminal object. The genuine colimit is the SAME original
quotient cube, with both actual maps and every original coefficient
operator retained.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The original identity simplex as an actual original element of the standard simplex. -/
def identityElement (n : SimplexCategory) : (SSet.stdSimplex.{u}.obj n).Elementsᵒᵖ :=
  op ((SSet.stdSimplex.{u}.obj n).elementsMk (op n) (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 n)))

/-- Every original standard simplex cell has its SAME element arrow to the original identity cell. -/
def toIdentity (n : SimplexCategory) (e : (SSet.stdSimplex.{u}.obj n).Elementsᵒᵖ) :
    e ⟶ identityElement.{u} n :=
  (Functor.Elements.homMk (SSet.stdSimplex.objEquiv.{u} e.unop.val).op (by
    apply SSet.stdSimplex.objEquiv.injective
    change SSet.stdSimplex.objEquiv.{u} e.unop.val ≫ 𝟙 n = SSet.stdSimplex.objEquiv.{u} e.unop.val
    exact Category.comp_id _)).op

/-- The whole original standard-simplex coefficient cocone maps each complete cell by its SAME ordinal cube operator. -/
def simplexCocone (n : SimplexCategory) : Cocone (diagram (SSet.stdSimplex.{u}.obj n)) where
  pt := RightCubeCosimplicial.diagram.{u}.obj n
  ι := {
    app e := (diagram (SSet.stdSimplex.{u}.obj n)).map (toIdentity n e)
    naturality e d f := by
      have h : f ≫ toIdentity n d = toIdentity n e := by
        apply Quiver.Hom.unop_inj
        apply Functor.Elements.hom_ext
        apply Quiver.Hom.unop_inj
        exact congrArg SSet.stdSimplex.objEquiv.{u} f.unop.map_val
      exact (Functor.map_comp _ _ _).symm.trans
        ((congrArg (diagram (SSet.stdSimplex.{u}.obj n)).map h).trans (Category.comp_id _).symm) }

/-- The SAME whole original colimit-to-cube comparison on each original standard simplex. -/
def simplexMap (n : SimplexCategory) :
    object (SSet.stdSimplex.{u}.obj n) ⟶ RightCubeCosimplicial.diagram.{u}.obj n :=
  colimit.desc (diagram (SSet.stdSimplex.{u}.obj n)) (simplexCocone.{u} n)

/-- Every complete original standard coefficient is mapped by its literal original quotient-cube operator. -/
theorem insertion_simplexMap (n : SimplexCategory) (e : (SSet.stdSimplex.{u}.obj n).Elementsᵒᵖ) :
    insertion (SSet.stdSimplex.{u}.obj n) e ≫ simplexMap n =
      (diagram (SSet.stdSimplex.{u}.obj n)).map (toIdentity n e) :=
  colimit.ι_desc (simplexCocone.{u} n) e

/-- The original identity coefficient has exactly its original identity cube operator. -/
theorem toIdentity_identity (n : SimplexCategory) :
    toIdentity n (identityElement.{u} n) = 𝟙 (identityElement.{u} n) := by
  apply Quiver.Hom.unop_inj
  apply Functor.Elements.hom_ext
  change (SSet.stdSimplex.objEquiv.{u} (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 n))).op = (𝟙 n).op
  rw [Equiv.apply_symm_apply]

/-- The genuine full realization of the SAME original standard simplex is its original quotient cube. -/
def simplexIso (n : SimplexCategory) :
    object (SSet.stdSimplex.{u}.obj n) ≅ RightCubeCosimplicial.diagram.{u}.obj n where
  hom := simplexMap n
  inv := insertion (SSet.stdSimplex.{u}.obj n) (identityElement n)
  hom_inv_id := by
    apply colimit.hom_ext
    intro e
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ insertion _ (identityElement n)) (insertion_simplexMap n e)).trans
        ((insertion_naturality _ (toIdentity n e)).trans (Category.comp_id _).symm))
  inv_hom_id := (insertion_simplexMap n (identityElement n)).trans
    ((congrArg (diagram (SSet.stdSimplex.{u}.obj n)).map (toIdentity_identity n)).trans
      (Functor.map_id _ _))

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
