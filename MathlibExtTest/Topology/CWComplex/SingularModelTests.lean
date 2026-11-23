/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.CWComplex.SingularModel

noncomputable section

open CategoryTheory
open scoped ContinuousMap Simplicial

universe u v

#check @TopCat.counit_realizedVertex
#print axioms TopCat.counit_realizedVertex
#check @FundamentalGroup.mulEquivOfHomotopyEquivAt
#print axioms FundamentalGroup.mulEquivOfHomotopyEquivAt
#check @FundamentalGroup.mulEquivOfHomotopyEquivAt_apply
#print axioms FundamentalGroup.mulEquivOfHomotopyEquivAt_apply
#check @TopCat.singularRealizationHomotopyEquiv_of_CWType
#print axioms TopCat.singularRealizationHomotopyEquiv_of_CWType
#check @TopCat.singularRealizationCounit_pi1_bijective_of_CWType
#print axioms TopCat.singularRealizationCounit_pi1_bijective_of_CWType
#check @TopCat.singularRealization_pathConnected_of_connected_CWType
#print axioms TopCat.singularRealization_pathConnected_of_connected_CWType

example (X : TopCat.{u}) (x : X) :
    sSetTopAdj.counit.app X (SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)) = x :=
  (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
    (TopCat.toSSetObj₀Equiv.apply_symm_apply x)

example {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) (y : Y) (hxy : e x = y) :
    ∃ p : FundamentalGroup X x ≃* FundamentalGroup Y y,
      ∀ q, p q = FundamentalGroup.mapOfEq e.toFun hxy q :=
  ⟨FundamentalGroup.mulEquivOfHomotopyEquivAt e x y hxy,
    FundamentalGroup.mulEquivOfHomotopyEquivAt_apply e x y hxy⟩

example (X : TopCat.{u})
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X)) :
    ∃ e : SSet.toTop.obj (TopCat.toSSet.obj X) ≃ₕ X,
      e.toFun = (sSetTopAdj.counit.app X).hom :=
  TopCat.singularRealizationHomotopyEquiv_of_CWType X hCW

example (X : TopCat.{u})
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X)) (x : X) :
    Function.Bijective (FundamentalGroup.mapOfEq (sSetTopAdj.counit.app X).hom
      ((TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
        (TopCat.toSSetObj₀Equiv.apply_symm_apply x))) :=
  TopCat.singularRealizationCounit_pi1_bijective_of_CWType X hCW x

example (X : TopCat.{u}) [ConnectedSpace X]
    (hCW : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X)) :
    PathConnectedSpace (SSet.toTop.obj (TopCat.toSSet.obj X)) :=
  TopCat.singularRealization_pathConnected_of_connected_CWType X hCW

end
