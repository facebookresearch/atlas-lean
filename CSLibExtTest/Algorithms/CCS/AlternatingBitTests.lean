/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.CCS.AlternatingBit

/-!
# Tests for the alternating-bit protocol

* Initially the protocol can only accept; after accepting and transmitting,
  the data channel can lose the frame and the sender can time out and
  retransmit.
* A stale frame is not delivered twice: with the receiver already expecting
  the next bit, a duplicate frame is only acknowledged again.
* The protocol is not weakly bisimilar to a buffer that starts full: the
  buffer could deliver at once, the protocol cannot.
* The protocol can weakly accept, and the certificate has 108 pairs.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.AlternatingBit.Tests

open Cslib.CCS (Label)
open Cslib.CCS.Recursive Cslib.LTS

/-- Initially the only transition is accepting a message. -/
example : configSteps initial =
    [(.input .acc, (((.transmit false, .empty), .expect false), .empty))] := by
  decide +kernel

/-- After the frame is in the data channel, it can be lost (a silent step back
to an empty channel) or received. -/
example : configSteps (((.await false, .full false), .expect false), .empty) =
    [(.tau, (((.transmit false, .full false), .expect false), .empty)),
      (.tau, (((.await false, .empty), .expect false), .empty)),
      (.tau, (((.await false, .empty), .deliver false), .empty))] := by
  decide +kernel

/-- A duplicate frame tagged `false`, arriving when the receiver already
expects `true`, is acknowledged again but not delivered. -/
example : configSteps (((.await false, .full false), .expect true), .empty) =
    [(.tau, (((.transmit false, .full false), .expect true), .empty)),
      (.tau, (((.await false, .empty), .expect true), .empty)),
      (.tau, (((.await false, .empty), .reply false), .empty))] := by
  decide +kernel

/-- The empty buffer cannot weakly deliver. -/
theorem buf_not_hasOutLabel_del : ¬ lts.saturate.HasOutLabel buf (.output .del) := by
  rintro ⟨target, hweak⟩
  rw [saturate_tr_sTr, STr.iff_exists_of_ne (by simp)] at hweak
  obtain ⟨before, after, hsilent, hstep, -⟩ := hweak
  have hbefore : before = buf := by
    rcases Relation.ReflTransGen.cases_head hsilent with h | ⟨mid, hmid, -⟩
    · exact h.symm
    · obtain ⟨y, hy, -⟩ := (realizes_buffer false _ _).1 hmid
      simp [bufferSteps] at hy
  subst hbefore
  obtain ⟨y, hy, -⟩ := (realizes_buffer false _ _).1 hstep
  simp [bufferSteps] at hy

/-- The full buffer can deliver. -/
theorem buffer_true_hasOutLabel_del :
    lts.saturate.HasOutLabel (buffer true) (.output .del) :=
  ⟨buffer false, STr.single
    ((realizes_buffer true _ _).2 ⟨false, by simp [bufferSteps], rfl⟩)⟩

/-- The protocol is not weakly bisimilar to a buffer that starts full. -/
example : ¬ lts.HomWeakBisimilarity abp (buffer true) := fun h =>
  buf_not_hasOutLabel_del
    ((HomWeakBisimilarity.hasOutLabel_saturate_iff (abp_weaklyBisimilar_buffer.symm.trans h) _).2
      buffer_true_hasOutLabel_del)

/-- The protocol can weakly accept. -/
example : lts.saturate.HasOutLabel abp (.input .acc) :=
  (abp_weaklyBisimilar_buffer.hasOutLabel_saturate_iff _).2
    ⟨buffer true, STr.single
      ((realizes_buffer false _ _).2 ⟨true, by simp [bufferSteps], rfl⟩)⟩

/-- The certificate covers the 54 reachable configurations in each phase. -/
example : certificate.length = 108 := by decide +kernel

end Cslib.Algorithms.CCS.AlternatingBit.Tests
