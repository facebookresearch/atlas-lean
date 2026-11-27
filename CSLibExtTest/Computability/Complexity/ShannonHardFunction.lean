/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.ShannonHardFunction
import Mathlib.Data.Set.Card

/-!
# Tests for Shannon's wire-count lower bound

These examples check zero-cost gates, repeated references, and the lower bound at ten inputs.
-/

open Cslib.Complexity.Classes
open MetaMathlibExt.Complexity.KeyTheorems.ShannonHardFunction

example (k : ℕ) :
    wireCount (List.replicate k (.const true : ACGate 0) ++ [.andGate [], .orGate []]) = 0 := by
  simp [wireCount, gateInputs]

example : wireCount ([.var 0, .notGate 0, .andGate [0, 1, 0], .modGate 7 [2]] :
    List (ACGate 1)) = 5 := rfl

example : ∃ f : (Fin 10 → Bool) → Bool, ∀ C : List (ACGate 10),
    WellFormedCircuit C → IsModFree C → wireCount C ≤ 10 →
      ∃ x, (circuitEval C x).getLast? ≠ some (f x) := by
  have h := shannon_hard_function 10 le_rfl
  have ht : 2 ^ 1 ≤ 2 ^ (2 ^ 10) := Nat.pow_le_pow_right (by decide) (by decide)
  have hpos : 0 < 2 ^ (2 ^ 10) / 2 := Nat.div_pos (by simpa only [pow_one] using ht) (by decide)
  exact (Set.ncard_pos (Set.toFinite _)).mp (hpos.trans_le h)
