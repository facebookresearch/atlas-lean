/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ChainComplexColimits
public import MathlibExt.Algebra.Homology.ExactColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Category.ULift

/-!
# Homology and sequential colimits
-/

@[expose] public section

universe w v u vJ uJ

open CategoryTheory Limits

/-! ## Fixed-coefficient homology and sequential colimits -/

noncomputable section

namespace SSet

private theorem addCommGrpNatExactColimits :
    HasExactColimitsOfShape ℕ AddCommGrpCat.{u} := by
  let e : ℕ ≌ AsSmall.{u} ℕ := AsSmall.equiv
  letI : IsFiltered (AsSmall.{u} ℕ) := IsFiltered.of_equivalence e
  letI : HasExactColimitsOfShape (AsSmall.{u} ℕ) AddCommGrpCat.{u} := inferInstance
  exact HasExactColimitsOfShape.of_domain_equivalence AddCommGrpCat.{u} e.symm

private noncomputable def addCommGrpNatColimPreservesHomology :
    (colim (J := ℕ) (C := AddCommGrpCat.{u})).PreservesHomology := by
  letI : HasExactColimitsOfShape ℕ AddCommGrpCat.{u} := addCommGrpNatExactColimits
  letI : PreservesFiniteLimits (colim (J := ℕ) (C := AddCommGrpCat.{u})) := inferInstance
  letI : PreservesFiniteColimits (colim (J := ℕ) (C := AddCommGrpCat.{u})) := inferInstance
  infer_instance

attribute [local instance] addCommGrpNatColimPreservesHomology

/-- Fixed-coefficient simplicial homology of abelian groups preserves sequential colimits.
Exactness is derived internally for the original natural-number indexing category. -/
public instance homologyFunctor_preservesSequentialColimits (A : AddCommGrpCat.{u}) (q : ℕ) :
    PreservesColimitsOfShape ℕ (SSet.homologyFunctor (C := AddCommGrpCat.{u}) A q) := by
  change PreservesColimitsOfShape ℕ
    (((SSet.chainComplexFunctor AddCommGrpCat.{u}).obj A) ⋙
      HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) q)
  infer_instance

end SSet

end
