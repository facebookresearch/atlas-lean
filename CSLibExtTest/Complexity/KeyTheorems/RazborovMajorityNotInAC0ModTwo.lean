/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Complexity.KeyTheorems.RazborovMajorityNotInAC0ModTwo

/-!
# Tests for Razborov's majority lower bound

The modulus-two gate accepts even counts, including empty fan-in and a repeated true input.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.Smolensky.Razborov.Tests

open Cslib.Complexity.Classes

example : majorityDec ∉ AC0Mod 2 := razborov_majority_not_in_ac0_mod_two

private def modTwoCircuit : List (ACGate 1) :=
  [.var 0, .modGate 2 [0], .modGate 2 [0, 0], .modGate 2 []]

example (b : Bool) : circuitEval modTwoCircuit (fun _ => b) = [b, !b, true, true] := by
  cases b <;> rfl

end MetaMathlibExt.Complexity.KeyTheorems.Smolensky.Razborov.Tests
