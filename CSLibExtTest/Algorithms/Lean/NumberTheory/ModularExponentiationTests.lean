/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.NumberTheory.ModularExponentiation
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Init.Data.Nat.Basic

/-!
# Recursive modular exponentiation execution tests

These execute the source parity recursion and compare both its raw result and
actual multiplication count. The modulus-one zero-exponent result remains `1`.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.ModularExponentiationTests

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.ModularExponentiation

private meta def resultMatches (actual : TimeM Nat Nat) (expectedRet expectedTime : Nat) : Bool :=
  actual.ret == expectedRet && actual.time == expectedTime

private meta def assertResult (label : String) (actual : TimeM Nat Nat)
    (expectedRet expectedTime : Nat) : IO Unit :=
  if resultMatches actual expectedRet expectedTime then
    IO.println s!"{label}: ret={actual.ret} time={actual.time}"
  else
    throw (IO.userError
      s!"{label}: actual {actual.ret}/{actual.time}, expected {expectedRet}/{expectedTime}")

-- Source example and small exponents.
#eval assertResult "CLRS Figure 31.4" (modularExponentiation 7 560 561) 1 12
#eval assertResult "exponent zero" (modularExponentiation 7 0 5) 1 0
#eval assertResult "exponent one" (modularExponentiation 7 1 5) 2 1
#eval assertResult "exponent two" (modularExponentiation 7 2 5) 4 2

-- Odd and even source branches.
#eval assertResult "7^3 mod 5" (modularExponentiation 7 3 5) 3 3
#eval assertResult "7^4 mod 5" (modularExponentiation 7 4 5) 1 3
#eval assertResult "7^7 mod 5" (modularExponentiation 7 7 5) 3 5

-- The literal base result is not normalized when the modulus is one.
#eval assertResult "modulus-one zero exponent" (modularExponentiation 7 0 1) 1 0
#eval assertResult "modulus-one positive exponent" (modularExponentiation 7 7 1) 0 5

-- Base zero, a power-of-two exponent, and an all-one-bit exponent.
#eval assertResult "zero base" (modularExponentiation 0 5 7) 0 4
#eval assertResult "power-of-two exponent" (modularExponentiation 3 8 5) 1 4
#eval assertResult "all-one-bit exponent" (modularExponentiation 2 15 17) 9 7

#eval IO.println "ACTUAL_U111_CASES 12"

end Cslib.Algorithms.Lean.ModularExponentiationTests
