/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QuantumGates.InputFraming

/-!
# Tests: Shor input framing decoding
-/

@[expose] public section

namespace Cslib.Complexity.Classes.QuantumGates.InputFramingTests

set_option autoImplicit false

open Cslib.Complexity.Classes

#print axioms qNumOf_measuredBits
#print axioms qNumOf_nat_bits
#print axioms qNumOf_measuredBits_take

/-- The outcome `6` on three qubits reads as `[false, true, true]`
(least-significant bit first) and decodes back to `6`. -/
theorem measuredBits_six :
    measuredBits 3 (6 : Fin (2 ^ 3)) = [false, true, true] ∧
      qNumOf (measuredBits 3 (6 : Fin (2 ^ 3))) = 6 := by
  decide

/-- Framed recovery at `N = 6` with two extra high qubits set: the low
three measured bits still decode to `6`. -/
theorem framed_recovery_six :
    qNumOf ((measuredBits ((Nat.bits 6).length + 2)
      (22 : Fin (2 ^ ((Nat.bits 6).length + 2)))).take (Nat.bits 6).length) = 6 := by
  decide

end Cslib.Complexity.Classes.QuantumGates.InputFramingTests
