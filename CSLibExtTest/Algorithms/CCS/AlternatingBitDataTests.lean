/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.CCS.AlternatingBitData

/-!
# Tests for the alternating-bit protocol with data

* Initially the protocol accepts either bit and nothing else.
* A frame carries the data bit; the receiver delivers the bit of the frame it
  expects and only acknowledges a duplicate.
* The protocol is not weakly bisimilar to the buffer that already holds a bit,
  nor does the certificate pass if one data bit in it is flipped: the data are
  tracked.
-/

@[expose] public section

namespace Cslib.Algorithms.CCS.AlternatingBitData.Tests

open Cslib.CCS (Label)
open Cslib.CCS.Recursive Cslib.LTS

-- The labelled configurations are deep products: instance synthesis needs a
-- larger size bound to find their decidable equality.
set_option synthInstance.maxSize 1024 in
/-- Initially the protocol only accepts. -/
example : configSteps initial =
    [(.input (.acc false), (((.transmit false false, none), .expect false), none)),
     (.input (.acc true), (((.transmit false true, none), .expect false), none))] := by
  decide +kernel

/-- The receiver delivers the data bit of the expected frame ... -/
example : (.input (.recv false true), .deliver false true) ∈ receiverSteps (.expect false) ∧
    receiverSteps (.deliver false true) = [(.output (.del true), .reply false)] := by decide

/-- ... and only acknowledges a duplicate. -/
example : (.input (.recv true false), .reply true) ∈ receiverSteps (.expect false) := by decide

/-- The empty buffer cannot weakly deliver. -/
theorem buf_not_hasOutLabel_del (d : Bool) :
    ¬ lts.saturate.HasOutLabel buf (.output (.del d)) := by
  rintro ⟨target, hweak⟩
  rw [saturate_tr_sTr, STr.iff_exists_of_ne (by simp)] at hweak
  obtain ⟨before, after, hsilent, hstep, -⟩ := hweak
  have hbefore : before = buf := by
    rcases Relation.ReflTransGen.cases_head hsilent with h | ⟨mid, hmid, -⟩
    · exact h.symm
    · obtain ⟨y, hy, -⟩ := (realizes_buffer none _ _).1 hmid
      simp [bufferSteps] at hy
  subst hbefore
  obtain ⟨y, hy, -⟩ := (realizes_buffer none _ _).1 hstep
  simp [bufferSteps] at hy

/-- The protocol is not weakly bisimilar to a buffer holding a bit. -/
example (d : Bool) : ¬ lts.HomWeakBisimilarity abpData (buffer (some d)) := fun h =>
  buf_not_hasOutLabel_del d
    ((HomWeakBisimilarity.hasOutLabel_saturate_iff (abpData_weaklyBisimilar_buffer.symm.trans h) _).2
      ⟨buffer none, STr.single
        ((realizes_buffer (some d) _ _).2 ⟨none, by simp [bufferSteps], rfl⟩)⟩)

/-- Flipping the simulated data bit of every pair breaks the certificate. -/
example : certCheck configSteps bufferSteps
    (certificate.map fun p => (p.1, p.2.map (!·))) = false := by
  decide +kernel

example : certificate.length = 220 := by decide +kernel

end Cslib.Algorithms.CCS.AlternatingBitData.Tests
