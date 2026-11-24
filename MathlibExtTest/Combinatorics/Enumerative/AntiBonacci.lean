/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AntiBonacci

open MetaMathlibExt

-- The second block skips the first anti-Tribonacci number in its interior.
example : (antiRecurrenceState [1, 1, 1] 2).1 = [4, 5, 7] := by decide +kernel

-- Both admissible residues occur already in the first two anti-Fibonacci numbers.
example : antiRecurrence [1, 1] 1 % 5 = 3 ∧ antiRecurrence [1, 1] 2 % 5 = 4 := by
  decide +kernel

-- Both endpoints of the odd residue range occur for k = 3.
example : antiRecurrence [1, 1, 1] 8 % 10 = 5 ∧ antiRecurrence [1, 1, 1] 3 % 10 = 7 := by
  decide +kernel

-- Specializing the theorem also gives the two possible residues at an arbitrary positive index.
example {n : ℕ} (hn : 1 ≤ n) :
    antiRecurrence [1, 1] n % 5 ∈ Finset.Icc 3 4 := by
  obtain ⟨_, c, hc, hmod⟩ := antiBonacci_mem_Icc_and_modEq 2 (by decide) hn
  rw [ite_eq_left (by decide : Even 2)] at hc
  change antiRecurrence [1, 1] n % 5 = (2 + c) % 5 at hmod
  rw [Finset.mem_Icc, hmod, Nat.mod_eq_of_lt (by omega)]
  omega
