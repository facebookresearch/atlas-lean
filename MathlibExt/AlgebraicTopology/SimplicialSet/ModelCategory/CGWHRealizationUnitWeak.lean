/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.CGWHRealization
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence

/-!
# The SAME actual native CGWH realization unit is weak

The original native realization/singular adjunction is the restriction
of the actual TopCat adjunction through its original whole identity
comparison Isos. Its SAME unit reads back the original realization unit.
The proved arbitrary-source realization-unit theorem therefore supplies
native unit weakness without a source Kan hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory

namespace SSet

/-- The SAME original restricted CGWH adjunction unit retains the actual TopCat realization-unit map. -/
theorem sSetCGWHAdj_unit_app_record (X : SSet.{v}) :
    sSetCGWHAdj.{u, v}.unit.app X = sSetTopAdj.unit.app X := by
  let η : X ⟶ TopCat.toSSet.obj (SSet.toTop.obj X) := sSetCGWHAdj.{u, v}.unit.app X
  let ηTop : X ⟶ TopCat.toSSet.obj (SSet.toTop.obj X) := sSetTopAdj.unit.app X
  have h := sSetTopAdj.map_restrictFullyFaithful_unit_app
    (Functor.FullyFaithful.id SSet.{v}) CGWH.fullyFaithfulCgwhToTop.{u, v}
    ((Functor.leftUnitor SSet.toTop) ≪≫ SSet.realizationToTopIso.{u, v}.symm)
    ((Functor.rightUnitor (CGWH.cgwhToTop.{u, v} ⋙ TopCat.toSSet.{v})).symm) X
  change η = ηTop ≫ TopCat.toSSet.map (𝟙 (SSet.toTop.obj X)) ≫
    𝟙 (TopCat.toSSet.obj (SSet.toTop.obj X)) at h
  simp only [TopCat.toSSet.map_id, Category.comp_id] at h
  exact h

/-- The SAME original native realization/singular unit is weak for every original simplicial source. -/
theorem realizationWeakEquivalences_sSetCGWHAdj_unit (X : SSet.{v}) :
    realizationWeakEquivalences (sSetCGWHAdj.{u, v}.unit.app X) := by
  rw [sSetCGWHAdj_unit_app_record]
  exact modelCategoryQuillen.unit_mem_realizationWeakEquivalences X

end SSet
