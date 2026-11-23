/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationFundamentalGroupoidEquivalence
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.FundamentalGroupIso

/-!
# The singular realization counit on fundamental groups

The original counit induces a fundamental-group isomorphism at every
canonical singular vertex for every space and every carrier universe.
The proof uses the realization and singular groupoid equivalences.
-/

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace TopCat

/-- The actual singular counit is bijective on fundamental groups at its
canonical original-point vertex for every space. Both comparison functors
are equivalences, so the counit functor is an equivalence by two-out-of-three. -/
public theorem singularRealizationCounit_pi1_bijective
    (X : TopCat.{u}) (x : X) :
    Function.Bijective (FundamentalGroup.mapOfEq (sSetTopAdj.counit.app X).hom
      ((TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
        (TopCat.toSSetObj₀Equiv.apply_symm_apply x))) := by
  let K := TopCat.toSSet.obj X
  let F := SSet.realizationFundamentalGroupoidFunctor K
  let G := _root_.FundamentalGroupoid.map (sSetTopAdj.counit.app X).hom
  let : F.IsEquivalence := SSet.realizationFundamentalGroupoidFunctor_isEquivalence K
  let : (F ⋙ G).IsEquivalence :=
    (TopCat.singularFundamentalGroupoidEquivalence X).isEquivalence_functor
  let : G.IsEquivalence := Functor.isEquivalence_of_comp_left F G
  let c := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
  let h : (sSetTopAdj.counit.app X) c = x :=
    (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
      (TopCat.toSSetObj₀Equiv.apply_symm_apply x)
  let changeBase : End (G.obj (_root_.FundamentalGroupoid.mk c)) ≃*
      End (_root_.FundamentalGroupoid.mk x) :=
    (eqToIso (congrArg _root_.FundamentalGroupoid.mk h)).conj
  let e := ((Functor.FullyFaithful.ofFullyFaithful G).mulEquivEnd
    (_root_.FundamentalGroupoid.mk c)).trans changeBase
  have he : FundamentalGroup.mapOfEq (sSetTopAdj.counit.app X).hom h =
      e.toMonoidHom := rfl
  rw [he]
  exact e.bijective

end TopCat

end
