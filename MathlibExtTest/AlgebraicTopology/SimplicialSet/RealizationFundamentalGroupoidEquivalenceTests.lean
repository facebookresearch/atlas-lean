/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidEquivalence

/-! Public consumers for direct-realization fundamental-groupoid equivalence. -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace RealizationFundamentalGroupoidEquivalenceTests

section Generic

variable (X : SSet.{u}) (z : X _⦋0⦌)

example : (SSet.realizationFundamentalGroupoidFunctor X).IsEquivalence :=
  SSet.realizationFundamentalGroupoidFunctor_isEquivalence X

example : (SSet.realizationFundamentalGroupoidFunctor X).FullyFaithful := by
  let _ : (SSet.realizationFundamentalGroupoidFunctor X).IsEquivalence :=
    SSet.realizationFundamentalGroupoidFunctor_isEquivalence X
  exact Functor.FullyFaithful.ofFullyFaithful _

example : CategoryTheory.End (SSet.FundamentalGroupoid.mk z) ≃*
    CategoryTheory.End
      (_root_.FundamentalGroupoid.mk (SSet.realizedVertex z)) :=
  SSet.realizationFundamentalGroupoidFunctorEndMulEquiv X z

example (f : CategoryTheory.End (SSet.FundamentalGroupoid.mk z)) :
    SSet.realizationFundamentalGroupoidFunctorEndMulEquiv X z f =
      (SSet.realizationFundamentalGroupoidFunctor X).mapEnd
        (SSet.FundamentalGroupoid.mk z) f := by
  exact SSet.realizationFundamentalGroupoidFunctor_endMulEquiv_apply X z f

example (e : X.Edge z z) :
    SSet.realizationFundamentalGroupoidFunctorEndMulEquiv X z
        (End.of (SSet.FundamentalGroupoid.homMk e)) =
      End.of (Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv (SSet.realizedEdgePath e))) := by
  apply End.ext
  change (SSet.realizationFundamentalGroupoidFunctor X).map
      (SSet.FundamentalGroupoid.homMk e) =
    Path.Homotopic.Quotient.mk
      (TopCat.pathEquiv (SSet.realizedEdgePath e))
  exact SSet.realizationFundamentalGroupoidFunctor_map_homMk X e

example : Function.Bijective
    ((SSet.realizationFundamentalGroupoidFunctor X).mapEnd
      (SSet.FundamentalGroupoid.mk z)) :=
  (SSet.realizationFundamentalGroupoidFunctorEndMulEquiv X z).bijective

/-- External callers may still use the original based-equivalence name and type. -/
example : CategoryTheory.End (SSet.FundamentalGroupoid.mk z) ≃*
    CategoryTheory.End
      (_root_.FundamentalGroupoid.mk (SSet.realizedVertex z)) :=
  SSet.realizationFundamentalGroupoidFunctor_endMulEquiv X z

/-- The persistent historical name denotes the exact current equivalence. -/
example : SSet.realizationFundamentalGroupoidFunctor_endMulEquiv X z =
    SSet.realizationFundamentalGroupoidFunctorEndMulEquiv X z := rfl

/-- The original name retains its complete original map-of-endomorphisms law. -/
example (f : CategoryTheory.End (SSet.FundamentalGroupoid.mk z)) :
    SSet.realizationFundamentalGroupoidFunctor_endMulEquiv X z f =
      (SSet.realizationFundamentalGroupoidFunctor X).mapEnd
        (SSet.FundamentalGroupoid.mk z) f :=
  SSet.realizationFundamentalGroupoidFunctor_endMulEquiv_apply X z f

end Generic

private abbrev emptySSet : SSet.{u} :=
  (⊥ : (Δ[0] : SSet.{u}).Subcomplex)

example :
    (SSet.realizationFundamentalGroupoidFunctor
      (Δ[0] : SSet.{u})).IsEquivalence :=
  SSet.realizationFundamentalGroupoidFunctor_isEquivalence Δ[0]

example :
    (SSet.realizationFundamentalGroupoidFunctor
      (Δ[1] : SSet.{u})).IsEquivalence :=
  SSet.realizationFundamentalGroupoidFunctor_isEquivalence Δ[1]

example :
    (SSet.realizationFundamentalGroupoidFunctor
      emptySSet).IsEquivalence :=
  SSet.realizationFundamentalGroupoidFunctor_isEquivalence emptySSet

private abbrev twoPointU1 : SSet.{1} :=
  TopCat.toSSet.obj (TopCat.of (ULift.{1} (Fin 2)))

example :
    (SSet.realizationFundamentalGroupoidFunctor
      twoPointU1).IsEquivalence :=
  SSet.realizationFundamentalGroupoidFunctor_isEquivalence twoPointU1

example (X : SSet.{0}) :
    (SSet.realizationFundamentalGroupoidFunctor X).IsEquivalence :=
  SSet.realizationFundamentalGroupoidFunctor_isEquivalence X

example (X : SSet.{1}) :
    (SSet.realizationFundamentalGroupoidFunctor X).IsEquivalence :=
  SSet.realizationFundamentalGroupoidFunctor_isEquivalence X

section NoGlobalInstance

variable (X : SSet.{u})

#guard_msgs (error, substring := true) in
#synth (SSet.realizationFundamentalGroupoidFunctor X).IsEquivalence

end NoGlobalInstance

#print axioms SSet.realizationFundamentalGroupoidFunctor_isEquivalence
#print axioms SSet.realizationFundamentalGroupoidFunctorEndMulEquiv
#print axioms SSet.realizationFundamentalGroupoidFunctor_endMulEquiv_apply

end RealizationFundamentalGroupoidEquivalenceTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet

end
