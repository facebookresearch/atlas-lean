/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations

/-!
# Tests for actual continuous ringed-site operation normalization

The tests check the displayed coefficient ring maps on sections and the
native module-unit adjunction mate. They need no geometric realization,
constructibility or six-functor provider.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.AdicRingedSiteOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry
open AdicRingedSiteOperations ContinuousAdicRingModules
open ProEtaleCohomologyFunctoriality

variable (E F : Type) [CommRing E] [TopologicalSpace E]
  [IsTopologicalRing E] [CommRing F] [TopologicalSpace F]
  [IsTopologicalRing F]

example {Y X : Scheme} (f : Y ⟶ X) (U : X.ProEtᵒᵖ)
    (a : C(U.unop.left, ULift.{1} E))
    (x : (Limits.pullback U.unop.hom f : Scheme)) :
    (show C((Limits.pullback U.unop.hom f : Scheme), ULift.{1} E) from
      (coefficientPushforward E f).hom.app U a) x =
        a ((Limits.pullback.fst U.unop.hom f).base.hom x) := rfl

example {Y X : Scheme} (f : Y ⟶ X) (U : X.ProEtᵒᵖ)
    (a : (coefficientRing E X).obj.obj U) :
    (unitPushforward E f).val.app U a =
      (coefficientPushforward E f).hom.app U a := rfl

example (α : E →+* F) (hα : Continuous α) (X : Scheme)
    (U : X.ProEtᵒᵖ) (a : C(U.unop.left, ULift.{1} E))
    (x : U.unop.left) :
    (show C(U.unop.left, ULift.{1} F) from
      (coefficientMap E F α hα X).hom.app U a) x =
        ULift.up (α (a x).down) := rfl

example {Y X : Scheme} (f : Y ⟶ X)
    [(AdicRingedSiteOperations.pushforward E f).IsRightAdjoint] :
    (pullbackPushforwardAdjunction E f).homEquiv _ _ (unitPullback E f) =
      unitPushforward E f := unitPullback_mate E f

end MathlibExtTest.AlgebraicGeometry.AdicRingedSiteOperations
