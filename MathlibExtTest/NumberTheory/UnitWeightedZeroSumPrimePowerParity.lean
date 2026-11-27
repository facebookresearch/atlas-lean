/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases
import MathlibExt.NumberTheory.UnitWeightedZeroSumPrimePowerParity

open MetaMathlibExt

-- Two pairs at different valuations, interleaved with each other and with a zero term.
example :
    let x : Fin 5 → ZMod (3 ^ 2) := ![1, 3, 2, 0, 6]
    ∃ a : Fin 5 → ZMod (3 ^ 2), (∀ j, IsUnit (a j)) ∧ ∑ j, a j * x j = 0 := by
  dsimp only
  apply unitWeightedZeroSum_of_even_nonDivisible Nat.prime_three
  intro i hi
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
  interval_cases i <;> decide

-- For a power of two, the valuation-zero fiber can be empty.
example :
    let x : Fin 2 → ZMod (2 ^ 3) := ![2, 6]
    ∃ a : Fin 2 → ZMod (2 ^ 3), (∀ j, IsUnit (a j)) ∧ ∑ j, a j * x j = 0 := by
  dsimp only
  apply unitWeightedZeroSum_of_even_nonDivisible Nat.prime_two
  intro i hi
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
  interval_cases i <;> decide

-- For exponent zero no parity assumptions are needed.
example (x : Fin 1 → ZMod (3 ^ 0)) :
    ∃ a : Fin 1 → ZMod (3 ^ 0), (∀ j, IsUnit (a j)) ∧ ∑ j, a j * x j = 0 :=
  unitWeightedZeroSum_of_even_nonDivisible Nat.prime_three x fun _ hi => by
    have := Finset.mem_Icc.mp hi
    omega
