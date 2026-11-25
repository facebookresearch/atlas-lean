/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Smolensky

/-!
# Tests for Smolensky's parity lower bound

At length two, a depth-two circuit computes parity with a modulus-three gate.
The lower bound concerns a family computing parity at every length.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.Smolensky.Tests

open Cslib.Complexity.Classes

example : parityDec ∉ AC0Mod 3 := smolensky

/-- The modular gate tests equality of the input bits by taking their weighted sum modulo three. -/
private def twoBitParity : List (ACGate 2) :=
  [.var 0, .var 1, .modGate 3 [0, 1, 1], .notGate 2]

example : WellFormedCircuit twoBitParity := by
  unfold WellFormedCircuit
  decide

example : ModOnly 3 twoBitParity := by
  unfold ModOnly twoBitParity
  simp

example : circuitDepth twoBitParity = 2 := rfl

example : ∀ x : Fin 2 → Bool,
    (circuitEval twoBitParity x).getLast? = some (parityDec (List.ofFn x)) := by
  decide

end MetaMathlibExt.Complexity.KeyTheorems.Smolensky.Tests
