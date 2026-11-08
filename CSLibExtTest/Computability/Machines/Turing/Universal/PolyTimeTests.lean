/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.Universal.PolyTime
public meta import CSLibExt.Computability.Machines.Turing.Universal.PolyTime

@[expose] public section

/-!
# Tests for the polynomial-time clocked universal function

The polynomial-time statement itself, and the quadratic bound `univTime_le` evaluated on
concrete inputs (the measured step counts of the whole machine are checked against `univTime` in
`ClockedTests`).
-/

set_option autoImplicit false

namespace CSLibExtTest.Computability.Machines.Turing.Universal.PolyTime

open Cslib.Turing.Universal Cslib.Turing.Universal.Clocked

/-- The clocked universal function has a polynomial-time `FinTM2`. -/
example : Nonempty (Turing.TM2ComputableInPolyTime
    (fun a : Code × List Bool × ℕ ↦ encIn a.1 a.2.1 a.2.2) encOut
    (fun a ↦ a.1.evalSteps a.2.1 a.2.2)) :=
  nonempty_univPolyTime

/-! The step bound and the quadratic polynomial, evaluated. -/

#guard univTime ⟨[]⟩ [true] 3 ≤ 18 * ((encIn ⟨[]⟩ [true] 3).length + 1) ^ 2

#guard univTime ⟨[[some (1, 2), some (1, 2), some (1, 2)]]⟩ [true, true] 5 ≤
  18 * ((encIn ⟨[[some (1, 2), some (1, 2), some (1, 2)]]⟩ [true, true] 5).length + 1) ^ 2

end CSLibExtTest.Computability.Machines.Turing.Universal.PolyTime
