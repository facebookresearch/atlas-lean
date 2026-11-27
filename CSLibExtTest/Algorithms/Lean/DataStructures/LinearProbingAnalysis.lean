/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAnalysis
import Mathlib.Tactic.NormNum

/-!
# Tests for the analysis of linear probing

Exact values of Knuth's `M(N, k)` from the 1963 note (the table for `N = 5` in its Section 5)
checked against the definitions, and Knuth's formula `M(N, k) = (1 + E_1(N, k)) / 2` checked on
these instances.
-/

namespace Cslib.Algorithms.Lean.LinearProbing.Test

open Cslib.Algorithms.Lean.LinearProbing

/-- One linear-probing insertion: cells `{0, 1}` occupied in a table of 3 cells, hash address 0. -/
example : probes ({0, 1} : Finset (Fin 3)) 0 = 3 := by decide
example : insertCell ({0, 1} : Finset (Fin 3)) 0 = 2 := by decide
/-- The scan wraps around the end of the table. -/
example : insertCell ({2} : Finset (Fin 3)) 2 = 0 := by decide
example : occupancy [2, 2, 2] = (Finset.univ : Finset (Fin 3)) := by decide

/-- Total probe count behind `M(3, 2) = 4 / 3`: `12` probes over the `3 ^ 2` hash sequences. -/
theorem probes_sum_three_one :
    (∑ a : Fin 1 → Fin 3, ∑ h : Fin 3, probes (occupancy (List.ofFn a)) h) = 12 := by
  decide

/-- Total probe count behind `M(4, 3) = 27 / 16`. -/
theorem probes_sum_four_two :
    (∑ a : Fin 2 → Fin 4, ∑ h : Fin 4, probes (occupancy (List.ofFn a)) h) = 108 := by
  decide

/-- Total probe count behind `M(5, 4) = 257 / 125`, an entry of Knuth's table for `N = 5`. -/
theorem probes_sum_five_three :
    (∑ a : Fin 3 → Fin 5, ∑ h : Fin 5, probes (occupancy (List.ofFn a)) h) = 1285 := by
  decide +kernel

example : insertionCost 3 1 = 4 / 3 := by
  have h := congrArg (Nat.cast : ℕ → ℚ) probes_sum_three_one
  push_cast at h
  rw [insertionCost, h]
  norm_num

example : insertionCost 4 2 = 27 / 16 := by
  have h := congrArg (Nat.cast : ℕ → ℚ) probes_sum_four_two
  push_cast at h
  rw [insertionCost, h]
  norm_num

/-- Knuth's `M(5, 4) = 257 / 125` (the table in Section 5 of the 1963 note). -/
example : insertionCost 5 3 = 257 / 125 := by
  have h := congrArg (Nat.cast : ℕ → ℚ) probes_sum_five_three
  push_cast at h
  rw [insertionCost, h]
  norm_num

/-- Knuth's formula `M(N, k) = (1 + E_1(N, k)) / 2` on the instance `N = 5`, `k = 4`. -/
example : insertionCost 5 3 = (1 + knuthE 1 5 4) / 2 := by
  have h := congrArg (Nat.cast : ℕ → ℚ) probes_sum_five_three
  push_cast at h
  rw [insertionCost, h]
  simp [knuthE, Finset.sum_range_succ, Nat.descFactorial]
  norm_num

example : (1 + knuthE 0 3 2) / 2 = successfulSearchCost 3 2 := by
  have h := congrArg (Nat.cast : ℕ → ℚ) probes_sum_three_one
  push_cast at h
  simp [successfulSearchCost, Finset.sum_range_succ, insertionCost_zero, knuthE,
    Nat.descFactorial]
  rw [insertionCost, h]
  norm_num

/-- The circle argument on a table of 3 cells with 2 items: `(3 - 2) · 3 = 3` of the `9` hash
sequences leave cell `0` empty, by the theorem and by enumeration. -/
example : (Finset.univ.filter fun a : Fin 2 → Fin 3 => (0 : Fin 3) ∉ occupancy (List.ofFn a)).card =
    3 := by
  decide

example : (Finset.univ.filter fun a : Fin 2 → Fin 3 => (0 : Fin 3) ∉ occupancy (List.ofFn a)).card =
    (3 - 2) * 3 ^ (2 - 1) :=
  card_not_mem_occupancy (by norm_num) (by norm_num) 0

/-- Three items fill a table of three cells. -/
example (l : List (Fin 3)) (hl : l.length = 3) : (occupancy l).card = 3 := by
  rw [card_occupancy (by omega), hl]

/-- Lemma 1 for `k = n = 3`: there are `4 ^ 2 = 16` parking functions of length 3. -/
example : Nat.card {f : Fin 3 → Fin 3 // MetaMathlibExt.PollakPartialParking.LinSuccess 3 3 f} =
    16 :=
  card_linSuccess 3 3 (by norm_num) le_rfl

end Cslib.Algorithms.Lean.LinearProbing.Test
