/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpacePulledRelativeDeckHomology

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SSet.modelCategoryQuillen

universe u uC vC

#check SSet.KanComplex.nativeCoverMap_mem_realizationWeakEquivalences
#print axioms SSet.KanComplex.nativeCoverMap_mem_realizationWeakEquivalences
#check SSet.KanComplex.nativeCoverPullbackBaseMap
#print axioms SSet.KanComplex.nativeCoverPullbackBaseMap
#check SSet.KanComplex.nativeCoverPullbackBaseMap_fst
#print axioms SSet.KanComplex.nativeCoverPullbackBaseMap_fst
#check SSet.KanComplex.nativeCoverPullbackBaseMap_snd
#print axioms SSet.KanComplex.nativeCoverPullbackBaseMap_snd
#check SSet.KanComplex.nativeCoverPullbackBaseMap_isPullback
#print axioms SSet.KanComplex.nativeCoverPullbackBaseMap_isPullback
#check SSet.KanComplex.nativeCoverPullbackBaseMap_mem_realizationWeakEquivalences
#print axioms SSet.KanComplex.nativeCoverPullbackBaseMap_mem_realizationWeakEquivalences
#check SSet.KanComplex.nativeCoverPullbackBaseMap_deck
#print axioms SSet.KanComplex.nativeCoverPullbackBaseMap_deck
#check TopCat.HSpaceCommonUnitFibration.unitProjection_eq
#print axioms TopCat.HSpaceCommonUnitFibration.unitProjection_eq
#check TopCat.HSpaceCommonUnitFibration.baseMap_eq
#print axioms TopCat.HSpaceCommonUnitFibration.baseMap_eq
#check TopCat.HSpaceCommonUnitFibration.relativeProjection_eq
#print axioms TopCat.HSpaceCommonUnitFibration.relativeProjection_eq
#check SSet.KanComplex.unitPulledCoverBaseDeckMap_eq
#print axioms SSet.KanComplex.unitPulledCoverBaseDeckMap_eq
#check TopCat.HSpaceCommonUnitFibration.commonTargetPulledDeck_homologyMap_eq_id
#print axioms TopCat.HSpaceCommonUnitFibration.commonTargetPulledDeck_homologyMap_eq_id
#check TopCat.HSpaceCommonUnitFibration.relativeIntermediatePulledDeck_homologyMap_eq_id
#print axioms TopCat.HSpaceCommonUnitFibration.relativeIntermediatePulledDeck_homologyMap_eq_id

namespace HSpacePulledRelativeDeckHomologyTests

open SSet.KanComplex

variable {B C E : SSet.{u}} (h : B ⟶ C) (p : E ⟶ C) (b : B _⦋0⦌)

example : nativeCoverPullbackBaseMap h p b ≫
    pullback.snd p (nativeCoverProjection C (h.app (op ⦋0⦌) b)) =
    pullback.snd (pullback.fst h p) (nativeCoverProjection B b) ≫ nativeCoverMap h b :=
  nativeCoverPullbackBaseMap_snd h p b

example : IsPullback (nativeCoverPullbackBaseMap h p b)
    (pullback.snd (pullback.fst h p) (nativeCoverProjection B b))
    (pullback.snd p (nativeCoverProjection C (h.app (op ⦋0⦌) b))) (nativeCoverMap h b) :=
  nativeCoverPullbackBaseMap_isPullback h p b

example [Fibration p] (hh : SSet.realizationWeakEquivalences h) :
    SSet.realizationWeakEquivalences (nativeCoverPullbackBaseMap h p b) :=
  nativeCoverPullbackBaseMap_mem_realizationWeakEquivalences h p b hh

example [SSet.KanComplex B] [SSet.KanComplex C]
    (g : End (SSet.FundamentalGroupoid.mk b)) :
    nativeCoverBaseChangeDeckMap (pullback.fst h p) b g ≫ nativeCoverPullbackBaseMap h p b =
      nativeCoverPullbackBaseMap h p b ≫ nativeCoverBaseChangeDeckMap p (h.app (op ⦋0⦌) b)
        ((SSet.mapFundamentalGroupoid h).mapEnd (SSet.FundamentalGroupoid.mk b) g) :=
  nativeCoverPullbackBaseMap_deck h p b g

section Original

open TopCat.HSpaceCommonUnitFibration

variable {X Y : TopCat.{u}} [HSpace X] [HSpace Y]
  [PathConnectedSpace X] [PathConnectedSpace Y] (f : X ⟶ Y)
  (h1 : IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor 1).map f)) (x : X)
  (g : End (SSet.FundamentalGroupoid.mk
    ((nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
      (TopCat.toSSetObj₀Equiv.symm x))))
  {A : Type uC} [Category.{vC} A] [Preadditive A] [HasCoproducts.{u} A]
  [CategoryWithHomology A] (R : A) (n : ℕ)

example : SSet.homologyMap
    (nativeCoverBaseChangeDeckMap (pullback.fst (baseMap f) (unitProjection Y))
      ((nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm x)) g) R n = 𝟙 _ :=
  commonTargetPulledDeck_homologyMap_eq_id f h1 x g R n

example : SSet.homologyMap
    (nativeCoverBaseChangeDeckMap (relativeProjection f)
      ((nativeCoverUnit (TopCat.toSSet.obj X)).app (op ⦋0⦌)
        (TopCat.toSSetObj₀Equiv.symm x)) g) R n = 𝟙 _ :=
  relativeIntermediatePulledDeck_homologyMap_eq_id f h1 x g R n

end Original

end HSpacePulledRelativeDeckHomologyTests
