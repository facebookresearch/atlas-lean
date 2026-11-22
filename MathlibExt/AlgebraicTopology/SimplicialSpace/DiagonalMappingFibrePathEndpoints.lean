/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.DiagonalMappingFibrePathFamily

/-!
# The original compact-open mapping-edge path endpoints

The realized whole interval family begins and ends at the realization of
the original prescribed diagonal source and target maps. The comparison
retains the whole original mapping parameter rather than only vertices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The actual zero-end evaluation retains the original complete diagonal source map. -/
theorem mappingFibreDiagonalPathFamily_zero (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibreDiagonalPathFamily W x y ≫
        TopCat.pathEvalZero (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) =
      SSet.toTop.map (mappingFibreDiagonalSource W x y) := by
  apply TopCat.ext
  intro z
  have h := ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_zero (mappingFibre W x y) _
      (mappingFibreDiagonalSource W x y) (mappingFibreDiagonalTarget W x y)
      (mappingFibreDiagonalHomotopy W x y)) z
  change mappingFibreDiagonalPathFamily W x y z (0 : TopCat.I.{u}) = _
  rw [mappingFibreDiagonalPathFamily_apply]
  have hp : (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))).inv (0, z) =
      prod.lift (TopCat.const (0 : TopCat.I.{u})) (𝟙 (SSet.toTop.obj (mappingFibre W x y))) z := by
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · exact (ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_fst TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))) (0, z)).trans
        (ConcreteCategory.congr_hom
          (prod.lift_fst (TopCat.const (0 : TopCat.I.{u}))
            (𝟙 (SSet.toTop.obj (mappingFibre W x y)))) z).symm
    · exact (ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_snd TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))) (0, z)).trans
        (ConcreteCategory.congr_hom
          (prod.lift_snd (TopCat.const (0 : TopCat.I.{u}))
            (𝟙 (SSet.toTop.obj (mappingFibre W x y)))) z).symm
  rw [hp]
  exact h

/-- The actual one-end evaluation retains the original complete diagonal target map. -/
theorem mappingFibreDiagonalPathFamily_one (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibreDiagonalPathFamily W x y ≫
        TopCat.pathEvalOne (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) =
      SSet.toTop.map (mappingFibreDiagonalTarget W x y) := by
  apply TopCat.ext
  intro z
  have h := ConcreteCategory.congr_hom
    (SSet.realizeHomotopyMap_one (mappingFibre W x y) _
      (mappingFibreDiagonalSource W x y) (mappingFibreDiagonalTarget W x y)
      (mappingFibreDiagonalHomotopy W x y)) z
  change mappingFibreDiagonalPathFamily W x y z (1 : TopCat.I.{u}) = _
  rw [mappingFibreDiagonalPathFamily_apply]
  have hp : (TopCat.prodIsoProd TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))).inv (1, z) =
      prod.lift (TopCat.const (1 : TopCat.I.{u})) (𝟙 (SSet.toTop.obj (mappingFibre W x y))) z := by
    apply Concrete.limit_ext
    rintro ⟨⟨⟩⟩
    · exact (ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_fst TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))) (1, z)).trans
        (ConcreteCategory.congr_hom
          (prod.lift_fst (TopCat.const (1 : TopCat.I.{u}))
            (𝟙 (SSet.toTop.obj (mappingFibre W x y)))) z).symm
    · exact (ConcreteCategory.congr_hom
        (TopCat.prodIsoProd_inv_snd TopCat.I.{u} (SSet.toTop.obj (mappingFibre W x y))) (1, z)).trans
        (ConcreteCategory.congr_hom
          (prod.lift_snd (TopCat.const (1 : TopCat.I.{u}))
            (𝟙 (SSet.toTop.obj (mappingFibre W x y)))) z).symm
  rw [hp]
  exact h

end SimplicialSpace.LeftDecalageObject
