/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Topology.Homotopy.HomotopyGroupMap

/-!
# Tests for maps on cube-based homotopy groups

These tests pin mixed-universe generalized-loop postcomposition, quotient
descent, identity and composition, and multiplicativity in positive degree.
They also guard the intended boundary: degree zero receives no group
homomorphism, and no singular comparison or weak-equivalence theorem is
introduced here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

universe u v w z

namespace MathlibExtTest.Topology.Homotopy.HomotopyGroupMapTests

variable {N : Type w} {X : Type u} {Y : Type v} {Z : Type z}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} (f : C(X, Y)) (g : C(Y, Z))

/-- Representative postcomposition supports independent universes. -/
example (p : Ω^ N X x) : Ω^ N Y (f x) :=
  GenLoop.map f p

example (p : Ω^ N X x) (y : I^N) :
    GenLoop.map f p y = f (p y) :=
  GenLoop.map_apply f p y

example (p : Ω^ N X x) :
    GenLoop.map (ContinuousMap.id X) p = p :=
  GenLoop.map_id p

example (p : Ω^ N X x) :
    GenLoop.map (g.comp f) p =
      GenLoop.map g (GenLoop.map f p) :=
  GenLoop.map_comp f g p

example :
    GenLoop.map f (GenLoop.const : Ω^ N X x) = GenLoop.const :=
  GenLoop.map_const f

example {p q : Ω^ N X x} (h : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (GenLoop.map f p) (GenLoop.map f q) :=
  GenLoop.Homotopic.map h f

example : Function.Surjective
    (HomotopyGroup.mk : Ω^ N X x → HomotopyGroup N X x) :=
  HomotopyGroup.mk_surjective

example (p : Ω^ N X x) :
    HomotopyGroup.map f (HomotopyGroup.mk p) =
      HomotopyGroup.mk (GenLoop.map f p) :=
  HomotopyGroup.map_mk f p

example (a : HomotopyGroup N X x) :
    HomotopyGroup.map (ContinuousMap.id X) a = a :=
  HomotopyGroup.map_id a

example (a : HomotopyGroup N X x) :
    HomotopyGroup.map (g.comp f) a =
      HomotopyGroup.map g (HomotopyGroup.map f a) :=
  HomotopyGroup.map_comp f g a

section Positive

variable [DecidableEq N] [Nonempty N]

example :
    HomotopyGroup.map (N := N) f (1 : HomotopyGroup N X x) = 1 :=
  HomotopyGroup.map_one f

example (a b : HomotopyGroup N X x) :
    HomotopyGroup.map f (a * b) =
      HomotopyGroup.map f a * HomotopyGroup.map f b :=
  HomotopyGroup.map_mul f a b

example :
    HomotopyGroup N X x →* HomotopyGroup N Y (f x) :=
  HomotopyGroup.mapHom f

example (a : HomotopyGroup N X x) :
    HomotopyGroup.mapHom f a = HomotopyGroup.map f a :=
  HomotopyGroup.mapHom_apply f a

end Positive

/-- Degree one is a concrete positive-degree client. -/
example : π_ 1 X x →* π_ 1 Y (f x) :=
  HomotopyGroup.mapHom f

/-- Every degree written as `n + 1` is a positive-degree client. -/
example (n : ℕ) : π_ (n + 1) X x →* π_ (n + 1) Y (f x) :=
  HomotopyGroup.mapHom f

/-- No group structure, hence no multiplicative map, is installed in degree zero. -/
example : True := by
  fail_if_success
    have witness : Group (π_ 0 X x) := inferInstance
  trivial

/-- The guard fails when a group instance is present, as it is in degree one. -/
example : True := by
  fail_if_success
    fail_if_success
      have witness : Group (π_ 1 X x) := inferInstance
  trivial

#guard_msgs (error, substring := true) in
#check TopCat.homotopyGroupEquivSingular

#guard_msgs (error, substring := true) in
#check HomotopyGroup.map_mem_weakHomotopyEquivalences

#print axioms GenLoop.map
#print axioms GenLoop.map_apply
#print axioms GenLoop.map_id
#print axioms GenLoop.map_comp
#print axioms GenLoop.map_const
#print axioms GenLoop.map_transAt
#print axioms GenLoop.Homotopic.map
#print axioms HomotopyGroup.mk
#print axioms HomotopyGroup.mk_surjective
#print axioms HomotopyGroup.map
#print axioms HomotopyGroup.map_mk
#print axioms HomotopyGroup.map_id
#print axioms HomotopyGroup.map_comp
#print axioms HomotopyGroup.one_eq_mk_const
#print axioms HomotopyGroup.mul_mk
#print axioms HomotopyGroup.map_one
#print axioms HomotopyGroup.map_mul
#print axioms HomotopyGroup.mapHom
#print axioms HomotopyGroup.mapHom_apply

end MathlibExtTest.Topology.Homotopy.HomotopyGroupMapTests
