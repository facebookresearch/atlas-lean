/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.NativeUnitPullbackCover

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u uC vC

#check SSet.KanComplex.nativeCoverToUnitPulledTotal
#print axioms SSet.KanComplex.nativeCoverToUnitPulledTotal
#check SSet.KanComplex.nativeCoverToUnitPulledTotal_fst
#print axioms SSet.KanComplex.nativeCoverToUnitPulledTotal_fst
#check SSet.KanComplex.nativeCoverToUnitPulledTotal_snd
#print axioms SSet.KanComplex.nativeCoverToUnitPulledTotal_snd
#check SSet.KanComplex.nativeCoverToUnitPulledTotal_original
#print axioms SSet.KanComplex.nativeCoverToUnitPulledTotal_original
#check SSet.KanComplex.nativeCoverToUnitPulledTotal_mem_realizationWeakEquivalences
#print axioms SSet.KanComplex.nativeCoverToUnitPulledTotal_mem_realizationWeakEquivalences
#check SSet.KanComplex.unitPulledCoverBaseDeckMap
#print axioms SSet.KanComplex.unitPulledCoverBaseDeckMap
#check SSet.KanComplex.unitPulledCoverDeckMap
#print axioms SSet.KanComplex.unitPulledCoverDeckMap
#check SSet.KanComplex.nativeCoverToUnitPulledTotal_deck
#print axioms SSet.KanComplex.nativeCoverToUnitPulledTotal_deck
#check TopCat.HSpaceHomotopyAction.unitPulledCoverDeckMap_homologyMap_eq_id
#print axioms TopCat.HSpaceHomotopyAction.unitPulledCoverDeckMap_homologyMap_eq_id
#check TopCat.HSpaceHomotopyAction.unitPulledCoverBaseDeckMap_homologyMap_eq_id
#print axioms TopCat.HSpaceHomotopyAction.unitPulledCoverBaseDeckMap_homologyMap_eq_id

namespace NativeUnitPullbackCoverTests

open SSet.KanComplex

example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌) :
    SSet.realizationWeakEquivalences (nativeCoverToUnitPulledTotal X x) :=
  nativeCoverToUnitPulledTotal_mem_realizationWeakEquivalences X x

example (X : SSet.{u}) (x : X _⦋0⦌) :
    nativeCoverToUnitPulledTotal X x ≫
      (pullback.fst (SSet.mappingPathTarget (nativeCoverUnit X))
          (nativeCoverProjection (CategoryTheory.nerve (SSet.FundamentalGroupoid X))
            ((nativeCoverUnit X).app (op ⦋0⦌) x)) ≫ SSet.mappingPathRetract (nativeCoverUnit X)) =
      nativeCoverProjection X x := nativeCoverToUnitPulledTotal_original X x

example (X : SSet.{u}) [SSet.KanComplex X] (x : X _⦋0⦌)
    (g : End (SSet.FundamentalGroupoid.mk x)) :
    nativeCoverDeckMap g ≫ nativeCoverToUnitPulledTotal X x =
      nativeCoverToUnitPulledTotal X x ≫ unitPulledCoverDeckMap g :=
  nativeCoverToUnitPulledTotal_deck x g

example (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X] (x : X)
    (g : End (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x)))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap (unitPulledCoverDeckMap g) R n = 𝟙 _ :=
  TopCat.HSpaceHomotopyAction.unitPulledCoverDeckMap_homologyMap_eq_id X x g R n

example (X : TopCat.{u}) [HSpace X] [PathConnectedSpace X] (x : X)
    (g : End (SSet.FundamentalGroupoid.mk
      ((nativeCoverUnit (TopCat.toSSet.obj X)).app (Opposite.op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm x))))
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasCoproducts.{u} C]
    [CategoryWithHomology C] (R : C) (n : ℕ) :
    SSet.homologyMap (unitPulledCoverBaseDeckMap g) R n = 𝟙 _ :=
  TopCat.HSpaceHomotopyAction.unitPulledCoverBaseDeckMap_homologyMap_eq_id X x g R n

end NativeUnitPullbackCoverTests
