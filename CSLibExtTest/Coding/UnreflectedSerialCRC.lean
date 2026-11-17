/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Coding.UnreflectedSerialCRC

@[expose] public section

open CSLibExt.Coding.UnreflectedSerialCRC

namespace CSLibExtTest.Coding.UnreflectedSerialCRC

/-- The CRC-3 fixture payloads, through the public theorems: `101`
gives `X^2`. The payload `011` is the reverse of `110`; the two
reversed payloads give different remainders (`X^2 + 1` versus `1`),
as the unreflected convention requires. -/
example : registerToPoly 3 (finalRegister crc3Generator 3 [true, false, true])
    = Polynomial.X ^ 2 :=
  final_register_crc3_payload_101

example : registerToPoly 3 (finalRegister crc3Generator 3 [true, true, false])
    = 1 :=
  final_register_crc3_payload_110

example : registerToPoly 3 (finalRegister crc3Generator 3 [false, true, true])
    ≠ registerToPoly 3 (finalRegister crc3Generator 3 [true, true, false]) := by
  rw [final_register_crc3_payload_011, final_register_crc3_payload_110]
  intro h
  have h0 := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 2) h
  simp at h0

/-- The canonical Mealy-machine run reaches the CRC-3 fixture
register: `MealyMachine.runState` of `serialLFSR` is `finalRegister`. -/
example : Cslib.Automata.MealyMachine.runState (serialLFSR crc3Generator 3)
      (initialRegister 3) ([true, false, true] ++ List.replicate 3 false)
    = finalRegister crc3Generator 3 [true, false, true] := by
  rw [runState_serialLFSR]
  rfl

end CSLibExtTest.Coding.UnreflectedSerialCRC
