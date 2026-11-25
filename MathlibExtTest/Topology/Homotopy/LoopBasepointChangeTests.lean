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

public import MathlibExt.Topology.Homotopy.LoopBasepointChange

/-!
# Tests for continuous loop basepoint change

The tests pin the conjugation orientation, the literal reversed-path inverse,
and both continuous-map homotopy inverse laws.  No strict-loop factorization,
singular comparison, loop shift, weak equivalence, or Q/S claim is made.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped Topology ContinuousMap

universe u

namespace MathlibExtTest.Topology.Homotopy.LoopBasepointChangeTests

variable {X : Type u} [TopologicalSpace X] {x y : X}
  (p : Path x y)

example : C(LoopSpace X x, LoopSpace X y) :=
  ContinuousMap.loopBasepointChange p

example : Continuous (ContinuousMap.loopBasepointChange p) :=
  (ContinuousMap.loopBasepointChange p).continuous

example (gamma : LoopSpace X x) :
    ContinuousMap.loopBasepointChange p gamma =
      p.symm.trans (gamma.trans p) :=
  ContinuousMap.loopBasepointChange_apply p gamma

example : LoopSpace X x ≃ₕ LoopSpace X y :=
  ContinuousMap.loopBasepointChangeHomotopyEquiv p

example :
    (ContinuousMap.loopBasepointChangeHomotopyEquiv p).toFun =
      ContinuousMap.loopBasepointChange p :=
  ContinuousMap.loopBasepointChangeHomotopyEquiv_toFun p

example :
    (ContinuousMap.loopBasepointChangeHomotopyEquiv p).invFun =
      ContinuousMap.loopBasepointChange p.symm :=
  ContinuousMap.loopBasepointChangeHomotopyEquiv_invFun p

example (gamma : LoopSpace X y) :
    (ContinuousMap.loopBasepointChangeHomotopyEquiv p).symm gamma =
      ContinuousMap.loopBasepointChange p.symm gamma :=
  rfl

example :
    ((ContinuousMap.loopBasepointChange p.symm).comp
      (ContinuousMap.loopBasepointChange p)).Homotopic
        (ContinuousMap.id (LoopSpace X x)) :=
  (ContinuousMap.loopBasepointChangeHomotopyEquiv p).left_inv

example :
    ((ContinuousMap.loopBasepointChange p).comp
      (ContinuousMap.loopBasepointChange p.symm)).Homotopic
        (ContinuousMap.id (LoopSpace X y)) :=
  (ContinuousMap.loopBasepointChangeHomotopyEquiv p).right_inv

/- The reflexive path gives an honest homotopy equivalence without a false
claim that its forward map is definitionally the identity. -/
example (z : X) : LoopSpace X z ≃ₕ LoopSpace X z :=
  ContinuousMap.loopBasepointChangeHomotopyEquiv (Path.refl z)

example : LoopSpace PUnit PUnit.unit ≃ₕ LoopSpace PUnit PUnit.unit :=
  ContinuousMap.loopBasepointChangeHomotopyEquiv (Path.refl PUnit.unit)

#guard_msgs (error, substring := true) in
#check ContinuousMap.loopBasepointChange_mem_weakHomotopyEquivalences

#guard_msgs (error, substring := true) in
#check ContinuousMap.weaklyPointedLoopMap_factorization

#guard_msgs (error, substring := true) in
#check SSet.singularLoopComparison

#guard_msgs (error, substring := true) in
#check ContinuousMap.loopHomotopyGroupShift

#guard_msgs (error, substring := true) in
#check quillenQSLoopWeakEquivalence

#guard_msgs (error, substring := true) in
#check ContinuousMap.loopPostTransMap

#print axioms ContinuousMap.loopBasepointChange
#print axioms ContinuousMap.loopBasepointChange_apply
#print axioms ContinuousMap.loopBasepointChangeHomotopyEquiv
#print axioms ContinuousMap.loopBasepointChangeHomotopyEquiv_toFun
#print axioms ContinuousMap.loopBasepointChangeHomotopyEquiv_invFun

end MathlibExtTest.Topology.Homotopy.LoopBasepointChangeTests
