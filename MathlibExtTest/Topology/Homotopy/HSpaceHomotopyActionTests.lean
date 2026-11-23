/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Homotopy.HSpaceHomotopyAction

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TopCat.HSpaceHomotopyAction
open scoped Topology Topology.Homotopy

universe u

namespace HSpaceHomotopyActionTests

#check loop_action_eq_self_of_unit_homotopies
#print axioms loop_action_eq_self_of_unit_homotopies
#check loop_action_eq_self
#print axioms loop_action_eq_self
#check loop_action_eq_self_at_point_of_unit_homotopies
#print axioms loop_action_eq_self_at_point_of_unit_homotopies
#check loop_action_eq_self_at_point
#print axioms loop_action_eq_self_at_point
#check exists_selfHomotopy_with_trace_of_unit_homotopies
#print axioms exists_selfHomotopy_with_trace_of_unit_homotopies
#check coherentLeftUnitHomotopy
#print axioms coherentLeftUnitHomotopy
#check coherentLeftUnitHomotopy_trace
#print axioms coherentLeftUnitHomotopy_trace

section BareUnits

variable (X : TopCat.{u}) (mu : C(X × X, X)) (e : X)
  (HL : ContinuousMap.Homotopy
    (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X))
  (HR : ContinuousMap.Homotopy
    (mu.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X e))) (ContinuousMap.id X))

example (n : ℕ) (p : _root_.Path e e) (a : HomotopyGroup.Pi (n + 1) X e) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p a = a :=
  loop_action_eq_self_of_unit_homotopies X mu e HL HR n p a

example (p : _root_.Path e e) (a : HomotopyGroup.Pi 1 X e) :
    TopCat.homotopyGroupBasepointChangeMulEquiv 0 X p a = a :=
  loop_action_eq_self_of_unit_homotopies X mu e HL HR 0 p a

example [PathConnectedSpace X] (n : ℕ) (x : X) (p : _root_.Path x x)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p a = a :=
  loop_action_eq_self_at_point_of_unit_homotopies X mu e HL HR n x p a

-- Every original loop is realized using only the two actual ordinary unit homotopies.
example (p : _root_.Path e e) :
    ∃ H : ContinuousMap.Homotopy (ContinuousMap.id X) (ContinuousMap.id X),
      (H.evalAt e).Homotopic p :=
  exists_selfHomotopy_with_trace_of_unit_homotopies X mu e HL HR p

-- The replacement is still a unit homotopy for the SAME multiplication and original unit.
example : ContinuousMap.Homotopy
    (mu.comp ((ContinuousMap.const X e).prodMk (ContinuousMap.id X))) (ContinuousMap.id X) :=
  coherentLeftUnitHomotopy X mu e HL HR

-- The required coherence is proved from the actual traces rather than assumed.
example : ((coherentLeftUnitHomotopy X mu e HL HR).evalAt e).Homotopic (HR.evalAt e) :=
  coherentLeftUnitHomotopy_trace X mu e HL HR

end BareUnits

section StandardHSpace

variable (X : TopCat.{u}) [HSpace X]

example (n : ℕ) (p : _root_.Path (HSpace.e : X) HSpace.e)
    (a : HomotopyGroup.Pi (n + 1) X HSpace.e) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p a = a :=
  loop_action_eq_self X n p a

example [PathConnectedSpace X] (n : ℕ) (x : X) (p : _root_.Path x x)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv n X p a = a :=
  loop_action_eq_self_at_point X n x p a

example [PathConnectedSpace X] (x : X) (p q : _root_.Path x x)
    (a : HomotopyGroup.Pi 2 X x) :
    TopCat.homotopyGroupBasepointChangeMulEquiv 1 X p a =
      TopCat.homotopyGroupBasepointChangeMulEquiv 1 X q a :=
  (loop_action_eq_self_at_point X 1 x p a).trans
    (loop_action_eq_self_at_point X 1 x q a).symm

end StandardHSpace

end HSpaceHomotopyActionTests
