/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy

@[expose] public section

/-!
# TopCat homotopy-equivalence weak-homotopy client

Compile-time consumer checks for the all-universe forward/inverse-leg packaging:
`TopCat.homotopyEquiv_toFun_mem` and `TopCat.homotopyEquiv_invFun_mem` plus
the `mem_of_eq_*` equality transports. States no horn/coproduct/pushout
closure, no WFS/model structure, and no KQ4 `SSet` weak-equivalence claim.
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHomotopyEquivWeakHomotopyTests

section ForwardLeg

theorem toFun_client {X Y : Type 0} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom e.toFun) :=
  TopCat.homotopyEquiv_toFun_mem e

#print axioms TopCat.homotopyEquiv_toFun_mem
#print axioms toFun_client

end ForwardLeg

section InverseLeg

theorem invFun_client {X Y : Type 0} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    TopCat.weakHomotopyEquivalences (TopCat.ofHom e.invFun) :=
  TopCat.homotopyEquiv_invFun_mem e

#print axioms TopCat.homotopyEquiv_invFun_mem
#print axioms invFun_client

end InverseLeg

section EqualLegs

theorem eqToFun_client {X Y : Type 0} [TopologicalSpace X] [TopologicalSpace Y]
    {f : TopCat.of X ⟶ TopCat.of Y} (e : ContinuousMap.HomotopyEquiv X Y)
    (hf : f = TopCat.ofHom e.toFun) : TopCat.weakHomotopyEquivalences f :=
  TopCat.mem_of_eq_toFun e hf

#print axioms TopCat.mem_of_eq_toFun
#print axioms eqToFun_client

theorem eqInvFun_client {X Y : Type 0} [TopologicalSpace X] [TopologicalSpace Y]
    {f : TopCat.of Y ⟶ TopCat.of X} (e : ContinuousMap.HomotopyEquiv X Y)
    (hf : f = TopCat.ofHom e.invFun) : TopCat.weakHomotopyEquivalences f :=
  TopCat.mem_of_eq_invFun e hf

#print axioms TopCat.mem_of_eq_invFun
#print axioms eqInvFun_client

end EqualLegs

section SymbolicUniverse

theorem toFun_symbolic {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    TopCat.weakHomotopyEquivalences.{u} (TopCat.ofHom e.toFun) :=
  TopCat.homotopyEquiv_toFun_mem e

theorem invFun_symbolic {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    TopCat.weakHomotopyEquivalences.{u} (TopCat.ofHom e.invFun) :=
  TopCat.homotopyEquiv_invFun_mem e

theorem eqToFun_symbolic {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : TopCat.of X ⟶ TopCat.of Y} (e : ContinuousMap.HomotopyEquiv X Y)
    (hf : f = TopCat.ofHom e.toFun) : TopCat.weakHomotopyEquivalences.{u} f :=
  TopCat.mem_of_eq_toFun e hf

theorem eqInvFun_symbolic {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f : TopCat.of Y ⟶ TopCat.of X} (e : ContinuousMap.HomotopyEquiv X Y)
    (hf : f = TopCat.ofHom e.invFun) : TopCat.weakHomotopyEquivalences.{u} f :=
  TopCat.mem_of_eq_invFun e hf

end SymbolicUniverse

section UniverseOne

theorem toFun_u1 {X Y : Type 1} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    TopCat.weakHomotopyEquivalences.{1} (TopCat.ofHom e.toFun) :=
  TopCat.homotopyEquiv_toFun_mem e

theorem invFun_u1 {X Y : Type 1} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) :
    TopCat.weakHomotopyEquivalences.{1} (TopCat.ofHom e.invFun) :=
  TopCat.homotopyEquiv_invFun_mem e

theorem eqToFun_u1 {X Y : Type 1} [TopologicalSpace X] [TopologicalSpace Y]
    {f : TopCat.of X ⟶ TopCat.of Y} (e : ContinuousMap.HomotopyEquiv X Y)
    (hf : f = TopCat.ofHom e.toFun) : TopCat.weakHomotopyEquivalences.{1} f :=
  TopCat.mem_of_eq_toFun e hf

theorem eqInvFun_u1 {X Y : Type 1} [TopologicalSpace X] [TopologicalSpace Y]
    {f : TopCat.of Y ⟶ TopCat.of X} (e : ContinuousMap.HomotopyEquiv X Y)
    (hf : f = TopCat.ofHom e.invFun) : TopCat.weakHomotopyEquivalences.{1} f :=
  TopCat.mem_of_eq_invFun e hf

end UniverseOne

end MathlibExtTest.AlgebraicTopology.ModelCategory.TopCatHomotopyEquivWeakHomotopyTests
