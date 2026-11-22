/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalRightCubeRealizationNaturality
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeWeakComparison

/-!
# The SAME original natural quotient-cube realization maximum

Every original coefficient cube maps by its actual maximum and
then the complete supplied simplex map. The genuine coefficient
colimit gives a natural transformation on every original simplicial
set, with the exact original standard-simplex readback.
-/

noncomputable section
universe u
open CategoryTheory Opposite Limits
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalRightCubeRealization

/-- The complete original maximum cocone, retaining every original coefficient simplex. -/
def maximumCocone (K : SSet.{u}) : Cocone (diagram K) where
  pt := K
  ι := {
    app e := RightCubeMaximum.map e.unop.obj.unop.len ≫ SSet.yonedaEquiv.symm e.unop.val
    naturality e d f := by
      have hQ := RightCubeMaximumNaturality.map.naturality f.unop.hom.unop
      have hY := SSet.yonedaEquiv_symm_naturality_left (X := K) f.unop.hom.unop d.unop.val
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ SSet.yonedaEquiv.symm d.unop.val) hQ).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun q => RightCubeMaximum.map e.unop.obj.unop.len ≫ q) hY).trans
              ((congrArg (fun q => RightCubeMaximum.map e.unop.obj.unop.len ≫ SSet.yonedaEquiv.symm q)
                f.unop.map_val).trans (Category.comp_id _).symm)))) }

/-- The whole SAME original maximum map from the full coefficient realization to its original simplicial set. -/
def maximum (K : SSet.{u}) : object K ⟶ K :=
  colimit.desc (diagram K) (maximumCocone K)

/-- Every original coefficient reads back precisely its actual maximum followed by the complete original simplex. -/
theorem insertion_maximum (K : SSet.{u}) (e : K.Elementsᵒᵖ) :
    insertion K e ≫ maximum K =
      RightCubeMaximum.map e.unop.obj.unop.len ≫ SSet.yonedaEquiv.symm e.unop.val :=
  colimit.ι_desc _ _

/-- The SAME entire original quotient-cube maximum is natural for every original source simplicial map. -/
theorem maximum_naturality {K L : SSet.{u}} (f : K ⟶ L) :
    map f ≫ maximum L = maximum K ≫ f := by
  apply colimit.hom_ext
  intro e
  have hL := insertion_maximum L (f.mapElements.op.obj e)
  have hR := insertion_maximum K e
  have hY := SSet.yonedaEquiv_symm_comp e.unop.val f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ maximum L) (insertion_map f e)).trans
      (hL.trans
        ((congrArg (fun q => RightCubeMaximum.map e.unop.obj.unop.len ≫ q) hY.symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun q => q ≫ f) hR.symm).trans (Category.assoc _ _ _))))))

/-- The SAME original natural comparison on the entire original coefficient realization functor. -/
def maximumNatTrans : functor.{u} ⟶ 𝟭 SSet.{u} where
  app := maximum
  naturality K L f := maximum_naturality (K := K) (L := L) f

/-- On every original standard simplex, the full realized comparison reads the SAME original quotient maximum under its
actual original cube isomorphism. -/
theorem maximum_simplex (n : SimplexCategory) :
    maximum (SSet.stdSimplex.{u}.obj n) =
      (simplexIso n).hom ≫ RightCubeMaximum.map n.len := by
  apply (cancel_epi (simplexIso n).inv).mp
  have hI := insertion_maximum (SSet.stdSimplex.{u}.obj n) (identityElement n)
  have hY : SSet.yonedaEquiv.symm (SSet.stdSimplex.objEquiv.{u}.symm (𝟙 n)) = 𝟙 (SSet.stdSimplex.obj n) :=
    (SSet.yonedaEquiv (X := SSet.stdSimplex.obj n) (n := n)).injective
      (SSet.yonedaEquiv.apply_symm_apply _)
  exact hI.trans
    ((congrArg (fun q => RightCubeMaximum.map n.len ≫ q) hY).trans
      ((Category.comp_id _).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (fun q => q ≫ _) (simplexIso n).inv_hom_id).trans
            (Category.id_comp _))).symm))

/-- The SAME actual whole original coefficient maximum is weak on every original standard simplex. -/
theorem maximum_simplex_weak (n : SimplexCategory) :
    SSet.realizationWeakEquivalences (maximum (SSet.stdSimplex.{u}.obj n)) :=
  (maximum_simplex n).symm ▸ SSet.realizationWeakEquivalences.comp_mem _ _
    (SSet.realizationWeakEquivalences.of_isIso (simplexIso n).hom)
    (RightCubeWeakComparison.maximum_weak n.len)

end CategoryTheory.CoherentRealization.OriginalRightCubeRealization
