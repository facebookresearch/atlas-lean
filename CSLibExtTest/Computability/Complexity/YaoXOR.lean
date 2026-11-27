/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.YaoXOR

/-!
# Tests for Yao's XOR lemma

These examples check block order, parity, circuit reference defaults and agreement on a
two-element input space.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.YaoXOR.Tests

private def blocks : Fin 2 → Fin 3 → Bool :=
  ![![true, false, true], ![true, true, false]]

example : List.ofFn (xorFlat (by decide) blocks) = [true, false, true, true, true, false] := by
  decide

example : xorOf (fun x => x 0) blocks = false := by decide

example : xorOf (fun x => x 1) blocks = true := by decide

example (f : (Fin 3 → Bool) → Bool) : xorOf (k := 0) f Fin.elim0 = false := by
  simp [xorOf, xorFold]

-- A forward reference reads false even when the referenced gate later evaluates to true.
example : xorCircuitEval [(2, [1]), (0, [0]), (0, [1])] [true] = [true, true, false] := by
  decide

example (f : Bool → Bool) : agreement [] f (fun x => [x]) = 0 := by
  simp [agreement, xorCircuitEval, Cslib.Complexity.Classes.circuitEval]

example : agreement [(0, [0])] (fun _ : Bool => false) (fun x => [x]) = 1 / 2 := by
  have h : {x : Bool | (xorCircuitEval [(0, [0])] [x]).getLast? = some false} = {false} := by
    ext x
    cases x <;> decide
  simp [agreement, h]

end MetaMathlibExt.Complexity.KeyTheorems.YaoXOR.Tests
