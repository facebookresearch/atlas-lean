/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidRealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidUnit

set_option linter.style.longLine false

/-!
# Fundamental groupoids and geometric realization

For every simplicial set, direct geometric realization induces an equivalence
of fundamental groupoids.  The proof transports the landed equivalences for
the realization--singular unit and the singular comparison across the
canonical natural isomorphism identifying their composite with direct
realization.

The result is exposed as a theorem, not a global instance.  The based
endomorphism equivalence is the reusable interface for one-fold Waldhausen
K-theory.  No finite, nonsingular, approximation, Waldhausen, or K-theory
hypothesis is used here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- Direct geometric realization induces an equivalence of fundamental
groupoids in every universe. -/
theorem realizationFundamentalGroupoidFunctor_isEquivalence
    (X : SSet.{u}) :
    (SSet.realizationFundamentalGroupoidFunctor X).IsEquivalence := by
  let U := SSet.mapFundamentalGroupoid (sSetTopAdj.unit.app X)
  let S := TopCat.singularFundamentalGroupoidFunctor (SSet.toTop.obj X)
  let R := SSet.realizationFundamentalGroupoidFunctor X
  let _ : U.IsEquivalence :=
    SSet.sSetTopAdj_unit_app_isEquivalence_mapFundamentalGroupoid X
  let _ : S.IsEquivalence :=
    (TopCat.singularFundamentalGroupoidEquivalence
      (SSet.toTop.obj X)).isEquivalence_functor
  let _ : (U ⋙ S).IsEquivalence := inferInstance
  change R.IsEquivalence
  exact Functor.isEquivalence_of_iso
    (SSet.realizationFundamentalGroupoidUnitComparison X)

/-- The equivalence on based endomorphism monoids induced by direct
realization. -/
noncomputable def realizationFundamentalGroupoidFunctorEndMulEquiv
    (X : SSet.{u}) (z : X _⦋0⦌) :
    CategoryTheory.End (SSet.FundamentalGroupoid.mk z) ≃*
      CategoryTheory.End
        (_root_.FundamentalGroupoid.mk (SSet.realizedVertex z)) := by
  let R := SSet.realizationFundamentalGroupoidFunctor X
  let _ : R.IsEquivalence :=
    SSet.realizationFundamentalGroupoidFunctor_isEquivalence X
  exact (Functor.FullyFaithful.ofFullyFaithful R).mulEquivEnd
    (SSet.FundamentalGroupoid.mk z)

/- The historical public name is a persistent export of the same declaration.
No additional definition or alternative equivalence is introduced. -/
open SSet renaming realizationFundamentalGroupoidFunctorEndMulEquiv →
  realizationFundamentalGroupoidFunctor_endMulEquiv in
export _root_ (realizationFundamentalGroupoidFunctor_endMulEquiv)

/-- The based endomorphism equivalence is literally the map of the direct
realization functor. -/
@[simp]
theorem realizationFundamentalGroupoidFunctor_endMulEquiv_apply
    (X : SSet.{u}) (z : X _⦋0⦌)
    (f : CategoryTheory.End (SSet.FundamentalGroupoid.mk z)) :
    SSet.realizationFundamentalGroupoidFunctorEndMulEquiv X z f =
      (SSet.realizationFundamentalGroupoidFunctor X).mapEnd
        (SSet.FundamentalGroupoid.mk z) f :=
  rfl

end SSet

end
