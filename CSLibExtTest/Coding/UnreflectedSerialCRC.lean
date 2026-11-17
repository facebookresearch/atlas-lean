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

/-- The CRC-3 fixtures as executable bit words: payload `101`
leaves register `0b100`, `110` leaves `0b001`, and its reverse
`011` leaves `0b101`. -/
example : finalRegister 3 crc3Taps [true, false, true] = 0b100#3 :=
  final_register_crc3_payload_101_bits

example : finalRegister 3 crc3Taps [true, true, false] = 0b001#3 :=
  final_register_crc3_payload_110_bits

example : finalRegister 3 crc3Taps [false, true, true] = 0b101#3 :=
  final_register_crc3_payload_011_bits

/-- The same fixtures read as polynomials: `101` gives `X^2`. The
payload `011` is the reverse of `110`; the two reversed payloads
give different remainders (`X^2 + 1` versus `1`), as the
unreflected convention requires. -/
example : (finalRegister 3 crc3Taps [true, false, true]).toPolynomial
    = Polynomial.X ^ 2 :=
  final_register_crc3_payload_101

example : (finalRegister 3 crc3Taps [true, true, false]).toPolynomial = 1 :=
  final_register_crc3_payload_110

example : (finalRegister 3 crc3Taps [false, true, true]).toPolynomial
    ≠ (finalRegister 3 crc3Taps [true, true, false]).toPolynomial := by
  rw [final_register_crc3_payload_011, final_register_crc3_payload_110]
  intro h
  have h0 := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 2) h
  simp at h0

/-- The CRC-3 taps word is the modulus `X^3 + X + 1`. -/
example : crc3Taps.monicModulus = Polynomial.X ^ 3 + Polynomial.X + 1 :=
  monicModulus_crc3Taps

end CSLibExtTest.Coding.UnreflectedSerialCRC
