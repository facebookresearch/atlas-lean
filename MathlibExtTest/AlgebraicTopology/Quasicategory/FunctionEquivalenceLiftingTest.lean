/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.Quasicategory.FunctionEquivalenceLifting

/-!
# Clients for strict function equivalence lifting
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Limits MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.FunctionEquivalenceLiftingTest

open SSet


variable {A B X Y : SSet.{u}} {i : A ⟶ B} {p : X ⟶ Y}
  [Mono i] [InnerFibration p] [Quasicategory Y] [HasStrictEquivalenceLifting p]

/-- A public client extracts both strict equations for a supplied native packet. -/
example (sq : MonoidalClosed.internalHom.PullbackObjObj i p)
    {U : ((ihom B).obj X) _⦋0⦌} {V : sq.pt _⦋0⦌}
    (g : Edge (sq.π.app (op ⦋0⦌) U) V) (hg : g.IsEquivalence) :
    ∃ (U₁ : ((ihom B).obj X) _⦋0⦌) (_ : sq.π.app (op ⦋0⦌) U₁ = V)
      (f : Edge U U₁), f.IsEquivalence ∧ (f.map sq.π).edge = g.edge := by
  let : HasStrictEquivalenceLifting sq.π :=
    hasStrictEquivalenceLifting_pullbackObjObjπ sq
  exact HasStrictEquivalenceLifting.exists_lift g hg

/-- The literal limits-API comparison is a direct client of the public theorem. -/
example : HasStrictEquivalenceLifting
    (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p).π :=
  hasStrictEquivalenceLifting_pullbackObjObjπ
    (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i p)


end MathlibExtTest.AlgebraicTopology.Quasicategory.FunctionEquivalenceLiftingTest
