/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.CCS.GoBackN

/-!
# Tests for go-back-N

* Initially only `acc` is possible; after two accepts the window is full and a
  third accept is refused until an acknowledgement slides the window.
* A timeout goes back to the base of the window, and a lost frame leaves the
  channel empty.
* The receiver discards an out-of-order frame and acknowledges again the frame
  it expects; the sender ignores an acknowledgement outside its window.
* The protocol is not weakly bisimilar to a buffer that starts with one message.
* The lossy-acknowledgement variant: acknowledgements pass through a channel
  that may lose them.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.GoBackN.Tests

open Cslib.CCS (Label)
open Cslib.CCS.Recursive Cslib.LTS

example : configSteps initial = [(.input .acc, ((⟨0, 1, 0⟩, none), .expect 0))] := by
  decide +kernel

/-- With two outstanding messages the sender does not accept a third. -/
example : (senderSteps ⟨0, 2, 2⟩).all (fun y => y.1 != .input .acc) = true := by decide

/-- A timeout resets the transmission offset to the base. -/
example : (.tau, ⟨1, 2, 0⟩) ∈ senderSteps ⟨1, 2, 2⟩ := by decide

/-- The acknowledgement `2` acknowledges both outstanding frames `0` and `1`. -/
example : ackUpdate ⟨0, 2, 2⟩ 2 = ⟨2, 0, 0⟩ := by decide

/-- The acknowledgement `0` acknowledges nothing when the base is `0`: ignored. -/
example : ackUpdate ⟨0, 2, 2⟩ 0 = ⟨0, 2, 2⟩ := by decide

/-- A frame in the channel may be lost. -/
example : (.tau, none) ∈ dataSteps (some 1) := by decide

/-- Expecting `0`, the receiver discards frame `1` and acknowledges `0` again. -/
example : (.input (.recv 1), .reply 0) ∈ receiverSteps (.expect 0) := by decide

/-- The empty buffer cannot weakly deliver. -/
theorem buf_not_hasOutLabel_del : ¬ lts.saturate.HasOutLabel buf (.output .del) := by
  rintro ⟨target, hweak⟩
  rw [saturate_tr_sTr, STr.iff_exists_of_ne (by simp)] at hweak
  obtain ⟨before, after, hsilent, hstep, -⟩ := hweak
  have hbefore : before = buf := by
    rcases Relation.ReflTransGen.cases_head hsilent with h | ⟨mid, hmid, -⟩
    · exact h.symm
    · obtain ⟨y, hy, -⟩ := (realizes_buffer 0 _ _).1 hmid
      simp [bufferSteps] at hy
  subst hbefore
  obtain ⟨y, hy, -⟩ := (realizes_buffer 0 _ _).1 hstep
  simp [bufferSteps] at hy

/-- The protocol is not weakly bisimilar to a buffer holding one message. -/
example : ¬ lts.HomWeakBisimilarity goBackN (buffer 1) := fun h =>
  buf_not_hasOutLabel_del
    ((HomWeakBisimilarity.hasOutLabel_saturate_iff (goBackN_weaklyBisimilar_buffer.symm.trans h) _).2
      ⟨buffer 0, STr.single
        ((realizes_buffer 1 _ _).2 ⟨0, by simp [bufferSteps], rfl⟩)⟩)

/-- The certificate covers the 147 reachable configurations. -/
example : certificate.length = 147 := by decide +kernel

/-- The acknowledgement channel of the lossy variant may lose an
acknowledgement. -/
example : (.tau, none) ∈ ackChannelSteps (some 1) := by decide

/-- In the lossy variant the receiver hands its acknowledgement to the channel,
which passes it on to the sender. -/
example : (.output (.reply 1), .expect 1) ∈ lossyReceiverSteps (.reply 1) ∧
    (.output (.ack 1), none) ∈ ackChannelSteps (some 1) := by decide

/-- Composed: the receiver's acknowledgement enters the channel silently ... -/
example : (.tau, (((⟨0, 2, 1⟩, none), .expect 1), some 1)) ∈
    lossyConfigSteps (((⟨0, 2, 1⟩, none), .reply 1), none) := by
  decide +kernel

/-- ... and reaches the sender, which slides its window past frame `0`. -/
example : (.tau, (((⟨1, 1, 1⟩, none), .expect 1), none)) ∈
    lossyConfigSteps (((⟨0, 2, 2⟩, none), .expect 1), some 1) := by
  decide +kernel

/-- The lossy variant starts like the reliable one. -/
example : lossyConfigSteps (initial, none) =
    [(.input .acc, (((⟨0, 1, 0⟩, none), .expect 0), none))] := by
  decide +kernel

end Cslib.Algorithms.CCS.GoBackN.Tests
