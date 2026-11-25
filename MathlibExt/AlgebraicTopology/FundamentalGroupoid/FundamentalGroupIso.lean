/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Original based fundamental groups under homeomorphisms and isomorphisms

A homeomorphism between raw spaces with independent carrier universes,
together with an equality of selected basepoints, induces a multiplicative
equivalence of the original fundamental groups. The categorical version for
a `TopCat` isomorphism uses this same construction through its original
homeomorphism. Both forward maps are the original
`FundamentalGroup.mapOfEq` homomorphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe u v

namespace FundamentalGroup

/-- A homotopy equivalence of the original spaces induces the actual based
fundamental-group equivalence, retaining the specified image-point equality. -/
public def mulEquivOfHomotopyEquivAt {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (x : X) (y : Y) (hxy : e x = y) : FundamentalGroup X x ≃* FundamentalGroup Y y := by
  let F := FundamentalGroupoid.map e.toFun
  let E := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  let _ : F.IsEquivalence := E.isEquivalence_functor
  let changeBase : End (F.obj (FundamentalGroupoid.mk x)) ≃*
      End (FundamentalGroupoid.mk y) :=
    (eqToIso (congrArg FundamentalGroupoid.mk hxy)).conj
  exact ((Functor.FullyFaithful.ofFullyFaithful F).mulEquivEnd
    (FundamentalGroupoid.mk x)).trans changeBase

/-- The homotopy-equivalence comparison is the SAME original based map. -/
@[simp]
public theorem mulEquivOfHomotopyEquivAt_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (x : X) (y : Y) (hxy : e x = y) (q : FundamentalGroup X x) :
    mulEquivOfHomotopyEquivAt e x y hxy q =
      FundamentalGroup.mapOfEq e.toFun hxy q := rfl

/-- A homeomorphism of the original spaces induces an equivalence of their based End groups. -/
def mulEquivOfHomeomorphAt {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (x : X) (y : Y) (hxy : e x = y) : FundamentalGroup X x ≃* FundamentalGroup Y y :=
  mulEquivOfHomotopyEquivAt e.toHomotopyEquiv x y hxy

/-- The constructed equivalence is the original based map on every original group element. -/
@[simp]
theorem mulEquivOfHomeomorphAt_apply {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (x : X) (y : Y) (hxy : e x = y) (q : FundamentalGroup X x) :
    mulEquivOfHomeomorphAt e x y hxy q =
      FundamentalGroup.mapOfEq e.toHomotopyEquiv.toFun hxy q :=
  rfl

/-- A topological isomorphism and a basepoint equality induce an equivalence
of fundamental groups. -/
noncomputable def mulEquivOfIsoAt
    {X Y : TopCat.{u}} (e : X ≅ Y)
    (x : X) (y : Y) (hxy : e.hom x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  mulEquivOfHomeomorphAt (TopCat.homeoOfIso e) x y hxy

/-- The equivalence induced by a topological isomorphism is the usual based
fundamental-group map. -/
@[simp]
theorem mulEquivOfIsoAt_apply
    {X Y : TopCat.{u}} (e : X ≅ Y)
    (x : X) (y : Y) (hxy : e.hom x = y)
    (q : FundamentalGroup X x) :
    mulEquivOfIsoAt e x y hxy q =
      FundamentalGroup.mapOfEq e.hom.hom hxy q := by
  exact mulEquivOfHomeomorphAt_apply (TopCat.homeoOfIso e) x y hxy q

end FundamentalGroup

end
