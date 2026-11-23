/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Homology.ExactFunctorConnecting
import MathlibExt.Algebra.Homology.ShortComplex.CokernelSequence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.Grp.Abelian

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

#check @HomologicalComplex.mapCycleClass_homologyIso
#print axioms HomologicalComplex.mapCycleClass_homologyIso
#check @CategoryTheory.ShortComplex.ShortExact.delta_mapFunctor
#print axioms CategoryTheory.ShortComplex.ShortExact.delta_mapFunctor

/-- The literal ModuleCat-to-AddCommGrp comparison carries the same degree-three
cycle representative and its original class through the canonical homology Iso. -/
example (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) {A : ModuleCat.{u} ℤ}
    (a : A ⟶ K.X 3) (ha : a ≫ K.d 3 2 = 0) :
    let U := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
    let KF := (U.mapHomologicalComplex (ComplexShape.down ℕ)).obj K
    let haF : U.map a ≫ KF.d 3 2 = 0 :=
      (U.map_comp a (K.d 3 2)).symm.trans
        ((congrArg U.map ha).trans (U.map_zero _ _))
    KF.liftCycles (U.map a) 2 (by simp) haF ≫ KF.homologyπ 3 ≫
      ((HomologicalComplex.mapHomologyFunctorIso 3 U).app K).hom =
        U.map (K.liftCycles a 2 (by simp) ha ≫ K.homologyπ 3) := by
  exact HomologicalComplex.mapCycleClass_homologyIso _ K 3 2 (by simp) a ha

/-- For an ACTUAL quotient short exact sequence, the same exact forgetful
functor preserves its original connecting map; no connecting equality is an input. -/
example {K L : ChainComplex (ModuleCat.{u} ℤ) ℕ} (m : K ⟶ L) [Mono m] :
    let S := ShortComplex.cokernelSequence m
    let hS : S.ShortExact := ShortComplex.ShortExact.mk'
      (ShortComplex.cokernelSequence_exact m) (inferInstance : Mono m)
        (inferInstance : Epi (cokernel.π m))
    let U := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
    ((HomologicalComplex.mapHomologyFunctorIso 3 U).app S.X₃).inv ≫
      (hS.map_of_exact (U.mapHomologicalComplex (ComplexShape.down ℕ))).δ 3 2 (by simp) ≫
        ((HomologicalComplex.mapHomologyFunctorIso 2 U).app S.X₁).hom =
          U.map (hS.δ 3 2 (by simp)) := by
  exact CategoryTheory.ShortComplex.ShortExact.delta_mapFunctor _ _ 3 2 (by rfl)

end
