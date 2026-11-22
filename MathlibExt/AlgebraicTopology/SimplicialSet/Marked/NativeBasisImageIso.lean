/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningAdjunction
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeBasisChartHom

/-!
# Actual native straightening images of original marked basis charts

The native straightening unit and the original basis-chart unit define
both complete comparison maps through the proved Hom correspondences.
Their inverse laws and basis-map naturality follow from the actual
native unit and chart naturality, without an unspecified comparison
object or equivalence certificate.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- The actual straightening image maps to its original native chart by the original chart unit's native
  adjoint mate. -/
def nativeBasisImageToChart (B : SSet.{u}) (i : GeneratorBasis.Index (max B)) :
    (nativeStraightening B).obj ((nativeBasisFunctor B).obj i) ⟶ nativeBasisChartObject B i :=
  ((nativeStraighteningAdjunction B).homEquiv _ _).symm (nativeBasisChartUnit B i)

/-- The reverse whole native chart map is the original straightening unit read through the same exact chart
  correspondence. -/
def nativeBasisChartToImage (B : SSet.{u}) (i : GeneratorBasis.Index (max B)) :
    nativeBasisChartObject B i ⟶ (nativeStraightening B).obj ((nativeBasisFunctor B).obj i) :=
  (nativeBasisChartEquiv B i _).symm ((nativeStraighteningAdjunction B).unit.app ((nativeBasisFunctor B).obj i))

/-- The actual image-to-chart mate reads exactly the original basis-chart unit. -/
theorem nativeBasisImageToChart_homEquiv (B : SSet.{u}) (i : GeneratorBasis.Index (max B)) :
    (nativeStraighteningAdjunction B).homEquiv _ _ (nativeBasisImageToChart B i) = nativeBasisChartUnit B i :=
  ((nativeStraighteningAdjunction B).homEquiv _ _).apply_symm_apply _

/-- The original chart-to-image map reads precisely the actual whole native straightening unit. -/
theorem nativeBasisChartToImage_equiv (B : SSet.{u}) (i : GeneratorBasis.Index (max B)) :
    nativeBasisChartEquiv B i _ (nativeBasisChartToImage B i) =
      (nativeStraighteningAdjunction B).unit.app ((nativeBasisFunctor B).obj i) :=
  (nativeBasisChartEquiv B i _).apply_symm_apply _

/-- The two original comparison maps retain the identity of the entire native straightening image. -/
theorem nativeBasisImageToChart_toImage (B : SSet.{u}) (i : GeneratorBasis.Index (max B)) :
    nativeBasisImageToChart B i ≫ nativeBasisChartToImage B i = 𝟙 _ := by
  apply ((nativeStraighteningAdjunction B).homEquiv _ _).injective
  have h₁ := (nativeStraighteningAdjunction B).homEquiv_naturality_right
    (nativeBasisImageToChart B i) (nativeBasisChartToImage B i)
  have h₂ := (nativeBasisChartEquiv_unit B i _ (nativeBasisChartToImage B i)).symm.trans
    (nativeBasisChartToImage_equiv B i)
  rw [nativeBasisImageToChart_homEquiv] at h₁
  exact h₁.trans (h₂.trans (by simp [Adjunction.homEquiv_unit]))

/-- The same whole original chart-to-image and mate maps retain the identity of the actual native chart. -/
theorem nativeBasisChartToImage_toChart (B : SSet.{u}) (i : GeneratorBasis.Index (max B)) :
    nativeBasisChartToImage B i ≫ nativeBasisImageToChart B i = 𝟙 _ := by
  apply (nativeBasisChartEquiv B i _).injective
  have h := nativeBasisRepresenterHomEquiv_natural_right B i.left i.hom
    (nativeBasisChartToImage B i) (nativeBasisImageToChart B i)
  change nativeBasisChartEquiv B i (nativeBasisChartObject B i)
      (nativeBasisChartToImage B i ≫ nativeBasisImageToChart B i) =
    nativeBasisChartEquiv B i ((nativeStraightening B).obj ((nativeBasisFunctor B).obj i))
      (nativeBasisChartToImage B i) ≫ (nativeUnstraightening B).map (nativeBasisImageToChart B i) at h
  rw [nativeBasisChartToImage_equiv] at h
  exact h.trans
    (((nativeStraighteningAdjunction B).homEquiv_unit ((nativeBasisFunctor B).obj i)
      (nativeBasisChartObject B i) (nativeBasisImageToChart B i)).symm.trans (nativeBasisImageToChart_homEquiv B i))

/-- The actual native straightening image is its original full marked basis chart through these same
  original unit/mate maps. -/
def nativeBasisImageIso (B : SSet.{u}) (i : GeneratorBasis.Index (max B)) :
    (nativeStraightening B).obj ((nativeBasisFunctor B).obj i) ≅ nativeBasisChartObject B i where
  hom := nativeBasisImageToChart B i
  inv := nativeBasisChartToImage B i
  hom_inv_id := nativeBasisImageToChart_toImage B i
  inv_hom_id := nativeBasisChartToImage_toChart B i

/-- The native image comparison is natural on every original marked basis map, retaining its exact whole
  straightening and chart maps. -/
theorem nativeBasisImageIso_natural (B : SSet.{u}) {i j : GeneratorBasis.Index (max B)} (f : i ⟶ j) :
    (nativeStraightening B).map ((nativeBasisFunctor B).map f) ≫ (nativeBasisImageIso B j).hom =
      (nativeBasisImageIso B i).hom ≫ (nativeBasisChartFunctor B).map f := by
  apply ((nativeStraighteningAdjunction B).homEquiv _ _).injective
  change (nativeStraighteningAdjunction B).homEquiv _ _
      ((nativeStraightening B).map ((nativeBasisFunctor B).map f) ≫ nativeBasisImageToChart B j) =
    (nativeStraighteningAdjunction B).homEquiv _ _
      (nativeBasisImageToChart B i ≫ nativeBasisChartMap B f)
  have hl := (nativeStraighteningAdjunction B).homEquiv_naturality_left
    ((nativeBasisFunctor B).map f) (nativeBasisImageToChart B j)
  have hr := (nativeStraighteningAdjunction B).homEquiv_naturality_right
    (nativeBasisImageToChart B i) (nativeBasisChartMap B f)
  exact hl.trans
    ((congrArg (fun h => (nativeBasisFunctor B).map f ≫ h) (nativeBasisImageToChart_homEquiv B j)).trans
      ((nativeBasisChartUnit_natural B f).symm.trans
        ((congrArg (fun h => h ≫ (nativeUnstraightening B).map (nativeBasisChartMap B f))
          (nativeBasisImageToChart_homEquiv B i).symm).trans hr.symm)))

end SSet.Marked
