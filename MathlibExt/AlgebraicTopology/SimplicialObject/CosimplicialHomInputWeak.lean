/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialHomInputNaturality
import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalSimplexIndexWeakMaps
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceHomotopyInvariance

/-!
# The SAME full cosimplicial input nerve restriction is weak

The proved original standard-simplex nerve-map recognition and both
complete original Hom-input equivalences retain every original input
object, arrow and map. The same actual scalar Hom weak restriction
therefore supplies weakness of its original full input nerve map.
-/

noncomputable section

universe u v

open CategoryTheory Opposite

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D E : CosimplicialObject C}

/-- The SAME full original input-category nerve restriction is weak whenever its actual original scalar Hom restriction
is weak. -/
theorem inputRestriction_nerve_weak (α : D ⟶ E) (X : C)
    (hHom : SSet.realizationWeakEquivalences (homSpaceRestriction α X)) :
    SSet.realizationWeakEquivalences (nerveMap (inputRestriction α X)) := by
  have hMap := SSet.originalSimplexIndexMap_nerve_weak (homSpaceRestriction α X) hHom
  have hTarget := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence (homInputEquivalence D X).functor
  have hRight := SSet.realizationWeakEquivalences.comp_mem _ _ hMap hTarget
  have hNatural := NatTrans.nerveHomotopy (homInputEquivalenceRestriction α X).hom
  have hRight' : SSet.realizationWeakEquivalences (nerveMap
      (CostructuredArrow.map (S := SSet.stdSimplex.{v}) (homSpaceRestriction α X) ⋙
        (homInputEquivalence D X).functor)) :=
    nerveMap_comp (CostructuredArrow.map (S := SSet.stdSimplex.{v}) (homSpaceRestriction α X))
        (homInputEquivalence D X).functor ▸ hRight
  have hLeft := (SSet.realizationWeakEquivalences_iff_of_homotopy hNatural).mpr hRight'
  have hSource := nerveMap_mem_realizationWeakEquivalences_of_isEquivalence (homInputEquivalence E X).functor
  exact SSet.realizationWeakEquivalences.of_precomp _ _ hSource
    ((nerveMap_comp (homInputEquivalence E X).functor (inputRestriction α X)).symm ▸ hLeft)

end CategoryTheory.CosimplicialObject
