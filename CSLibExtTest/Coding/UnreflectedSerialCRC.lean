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
gives `X^2`, and the reversed payload `011` gives a different
remainder, as the unreflected convention requires. -/
example : registerToPoly 3 (finalRegister crc3Generator 3 [true, false, true])
    = Polynomial.X ^ 2 :=
  final_register_crc3_payload_101

example : registerToPoly 3 (finalRegister crc3Generator 3 [true, true, false])
    = 1 :=
  final_register_crc3_payload_110

example : registerToPoly 3 (finalRegister crc3Generator 3 [false, true, true])
    ≠ registerToPoly 3 (finalRegister crc3Generator 3 [true, false, true]) := by
  rw [final_register_crc3_payload_011, final_register_crc3_payload_101]
  intro h
  have h0 := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 0) h
  simp at h0

end CSLibExtTest.Coding.UnreflectedSerialCRC
