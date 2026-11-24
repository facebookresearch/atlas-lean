/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.Topology.Homotopy.StrictLoopMap

/-!
# Tests for strict topological loop postcomposition

These tests exercise the literal path formula, mixed universes, reflexive
loops, and strict identity/composition.  They make no basepoint-change,
singular-comparison, degree-shift, weak-equivalence, or Q/S claim.
-/

@[expose] public section

set_option autoImplicit false

open scoped Topology

universe u v w

namespace MathlibExtTest.Topology.Homotopy.StrictLoopMapTests

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X, Y)) (g : C(Y, Z)) (x : X)

example : C(LoopSpace X x, LoopSpace Y (f x)) :=
  ContinuousMap.strictLoopMap f x

example (gamma : LoopSpace X x) :
    ContinuousMap.strictLoopMap f x gamma =
      gamma.map f.continuous :=
  ContinuousMap.strictLoopMap_apply f x gamma

example :
    ContinuousMap.strictLoopMap (ContinuousMap.id X) x =
      ContinuousMap.id (LoopSpace X x) :=
  ContinuousMap.strictLoopMap_id x

example :
    (ContinuousMap.strictLoopMap g (f x)).comp
        (ContinuousMap.strictLoopMap f x) =
      ContinuousMap.strictLoopMap (g.comp f) x :=
  ContinuousMap.strictLoopMap_comp f g x

example :
    ContinuousMap.strictLoopMap f x (Path.refl x) =
      Path.refl (f x) :=
  ContinuousMap.strictLoopMap_refl f x

/- The import deliberately provides no later comparison or preservation
theorem. -/
#guard_msgs (error, substring := true) in
#check ContinuousMap.strictLoopMap_mem_weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check ContinuousMap.loopBasepointChange

#guard_msgs (error, substring := true) in
#check SSet.singularLoopComparison

#print axioms ContinuousMap.strictLoopMap
#print axioms ContinuousMap.strictLoopMap_apply
#print axioms ContinuousMap.strictLoopMap_id
#print axioms ContinuousMap.strictLoopMap_comp
#print axioms ContinuousMap.strictLoopMap_refl

end MathlibExtTest.Topology.Homotopy.StrictLoopMapTests
