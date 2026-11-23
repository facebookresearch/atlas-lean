/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.WeakEquivalenceAddCommGrpChains
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Simplicial homology and singular homology of realization

The realization--singular unit of a simplicial set induces a
quasi-isomorphism on chains with coefficients in any additive commutative
group.  Its homology map therefore gives a canonical isomorphism from
simplicial homology to singular homology of geometric realization.

The comparison is natural in the simplicial set.  This file introduces no
specific category nerve, group-completion, telescope, or plus-construction
claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace SSet

/-- Simplicial homology agrees canonically with singular homology of
geometric realization. -/
noncomputable def realizationSingularHomologyIso
    (A : AddCommGrpCat.{u}) (X : SSet.{u}) (n : ℕ) :
    X.homology A n ≅
      ((AlgebraicTopology.singularHomologyFunctor
        AddCommGrpCat.{u} n).obj A).obj (SSet.toTop.obj X) := by
  let _ : QuasiIso
      (SSet.chainComplexMap (sSetTopAdj.unit.app X) A) :=
    SSet.realizationWeakEquivalences.quasiIso_chainComplexMap_addCommGrp
      (SSet.modelCategoryQuillen.unit_mem_realizationWeakEquivalences X) A
  exact isoOfQuasiIsoAt
    (SSet.chainComplexMap (sSetTopAdj.unit.app X) A) n

/-- The forward realization/singular homology comparison is the homology
map induced by the realization--singular unit. -/
@[simp]
theorem realizationSingularHomologyIso_hom
    (A : AddCommGrpCat.{u}) (X : SSet.{u}) (n : ℕ) :
    (realizationSingularHomologyIso A X n).hom =
      SSet.homologyMap (sSetTopAdj.unit.app X) A n :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The realization/singular homology comparison is natural, in the
map-first orientation. -/
@[reassoc]
theorem realizationSingularHomologyIso_hom_naturality
    (A : AddCommGrpCat.{u}) {X Y : SSet.{u}}
    (f : X ⟶ Y) (n : ℕ) :
    SSet.homologyMap f A n ≫
        (realizationSingularHomologyIso A Y n).hom =
      (realizationSingularHomologyIso A X n).hom ≫
        ((AlgebraicTopology.singularHomologyFunctor
          AddCommGrpCat.{u} n).obj A).map (SSet.toTop.map f) := by
  have hunit : f ≫ sSetTopAdj.unit.app Y =
      sSetTopAdj.unit.app X ≫
        TopCat.toSSet.map (SSet.toTop.map f) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      sSetTopAdj.unit.naturality f
  change SSet.homologyMap f A n ≫
      SSet.homologyMap (sSetTopAdj.unit.app Y) A n =
    SSet.homologyMap (sSetTopAdj.unit.app X) A n ≫
      SSet.homologyMap
        (TopCat.toSSet.map (SSet.toTop.map f)) A n
  rw [← SSet.homologyMap_comp, ← SSet.homologyMap_comp, hunit]

end SSet

end
