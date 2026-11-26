/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Distributed.Byzantine.SignedMessages

/-! # Fixtures for signed-message Byzantine agreement -/

open Cslib.Distributed.Byzantine.SignedMessages

namespace SignedMessagesTests

private def choose : Choice Bool where
  retreat := false
  select known := decide (known = {true})
  select_singleton v := by cases v <;> decide
  select_empty := by decide

private def send {L : Type} (d : Message L Bool) : Event L Bool := ⟨.send, d⟩
private def recv {L : Type} (d : Message L Bool) : Event L Bool := ⟨.receive, d⟩

-- Each concrete history is checked against all the local and communication obligations.
private def silent : History (Fin 2) Bool := []

private theorem silentSM : silent.FollowsSM 1 {none} true := by
  constructor <;> decide

-- Both loyal lieutenants retreat when the faulty commander says nothing.
example : silent.decision choose 0 = false ∧ silent.decision choose 1 = false := by decide

example := sm_interactiveConsistency choose silentSM (by decide)

private def loyal : History (Fin 2) Bool :=
  let a := Message.initial true 0
  let b := Message.initial true 1
  let ab := a.relay 1
  [send a, send b, recv a, send ab, recv ab, recv b]

private theorem loyalSM : loyal.FollowsSM 0 ∅ true := by
  constructor <;> decide

-- A bare order still forwards when m = 0. The receiver of that relay learns the order
-- before its direct receipt, so the later direct receipt does not add or forward it again.
example : loyal.Learns ⟨2, by decide⟩ ∧ loyal.Learns ⟨4, by decide⟩ ∧
    ¬loyal.Learns ⟨5, by decide⟩ := by decide

example (i : Fin 2) : loyal.decision choose i = true :=
  (sm_interactiveConsistency choose loyalSM (by decide)).2 (by decide) i (by simp)

private def equivocating : History (Fin 2) Bool :=
  let a := Message.initial true 0
  let b := Message.initial false 1
  let ab := a.relay 1
  let ba := b.relay 0
  [send a, send b, recv a, recv b, send ab, send ba, recv ab, recv ba]

private theorem equivocatingSM : equivocating.FollowsSM 1 {none} true := by
  constructor <;> decide

-- Both orders survive a faulty commander's inconsistent choices. The shared selector
-- is not a requirement that a particular one of these two orders be chosen.
example : equivocating.orders 0 = {true, false} ∧ equivocating.orders 1 = {true, false} := by
  decide

example : equivocating.decision choose 0 = equivocating.decision choose 1 :=
  (sm_interactiveConsistency choose equivocatingSM (by decide)).1 0 1 (by decide) (by decide)

private def cutoff : History (Fin 3) Bool :=
  let a := Message.initial true 0
  let ab := a.relay 1
  let ac := a.relay 2
  let abc := ab.relay 2
  [send a, recv a, send ab, send ac, recv ab, send abc, recv abc, recv ac]

private theorem cutoffSM : cutoff.FollowsSM 2 {none} true := by
  constructor <;> decide

-- Lieutenant 2 first learns at the cutoff. Lieutenant 1 sent it the extension of `[0]`,
-- not sending that extension to lieutenant 0, which was already in the prefix.
example : cutoff.Learns ⟨6, by decide⟩ ∧ ¬cutoff.Learns ⟨7, by decide⟩ := by decide

example : cutoff.orders 2 = cutoff.orders 0 := cutoffSM.orders_eq (by decide) (by decide) (by decide)

private def faultyPrefix : History (Fin 3) Bool :=
  let a : Message (Fin 3) Bool := ⟨none, 0, true, [2], true⟩
  let b := a.relay 1
  [send a, recv a, send b, recv b]

private theorem faultyPrefixSM : faultyPrefix.FollowsSM 2 {none, some 2} true := by
  constructor <;> decide

-- No send by lieutenant 2 occurred: the faulty signature needs no provenance. The loyal
-- appended signature, however, comes from lieutenant 0's genuine nonempty shorter prefix.
example : faultyPrefix.orders 1 = faultyPrefix.orders 0 :=
  faultyPrefixSM.orders_eq (by decide) (by decide) (by decide)

private def unissued : History (Fin 3) Bool :=
  let a : Message (Fin 3) Bool := ⟨none, 1, true, [0], true⟩
  [send a, recv a]

-- Removing the genuine prefix makes a claim of verification with a loyal signer inadmissible.
example : ¬unissued.FollowsSM 1 {none} true := by
  intro H
  let r : Fin unissued.length := ⟨1, by decide⟩
  have ho := H.lieutenantSignature r (by decide) (by decide) ⟨0, by decide⟩ (by decide)
  exact (by decide : ¬∃ s : Fin unissued.length, s < r ∧ (unissued.get s).phase = .send ∧
    (unissued.get s).message.sender = some 0 ∧ (unissued.get s).message.order = true ∧
    (unissued.get s).message.chain = [0]) ho

-- Verification and all structural checks matter independently. A later bare order with
-- a different value still cannot be taken under (2)(A).
example :
    ¬(⟨some 0, 1, true, [0, 0], true⟩ : Message (Fin 2) Bool).Proper ∧
    ¬(⟨some 0, 0, true, [0], true⟩ : Message (Fin 2) Bool).Proper ∧
    ¬(⟨some 0, 1, true, [], true⟩ : Message (Fin 2) Bool).Proper ∧
    ¬(⟨none, 1, true, [], false⟩ : Message (Fin 2) Bool).Proper ∧
    ¬(recv (Message.initial false (1 : Fin 2))).Accepts {true} := by decide

end SignedMessagesTests
