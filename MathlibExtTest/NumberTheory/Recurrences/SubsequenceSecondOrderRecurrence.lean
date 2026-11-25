/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SubsequenceSecondOrderRecurrence
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

open MetaMathlibExt

-- Every other odd-indexed Fibonacci number: with `(P, Q) = (1, -1)`, `t = 2` and `r = 1`, the
-- coefficients are the Lucas number `L₂ = 3` and `(-1) ^ 2 = 1`.
example (n : ℕ) :
    (Nat.fib (2 * (n + 2) + 1) : ℤ) = 3 * Nat.fib (2 * (n + 1) + 1) - Nat.fib (2 * n + 1) := by
  have hw : ∀ n : ℕ, (Nat.fib (n + 2) : ℤ) =
      fibonacciLucasParams.p * Nat.fib (n + 1) - fibonacciLucasParams.q * Nat.fib n := by
    intro n
    simp only [fibonacciLucasParams, Nat.fib_add_two, Nat.cast_add]
    ring
  have h := (subsequence_secondOrderRecurrence fibonacciLucasParams (fun n => (Nat.fib n : ℤ))
    hw 2 1 (by decide)).1 n
  have hV : lucasV fibonacciLucasParams 2 = 3 := by decide
  have hq : fibonacciLucasParams.q ^ 2 = 1 := by decide
  rw [hV, hq] at h
  linear_combination h

-- Applied to `U` itself with `r = 0` and `n = 0`, the recurrence gives the doubling formula
-- `U (2 t) = V t * U t`.
example (params : LucasSequenceParams) (t : ℕ) (ht : 0 < t) :
    lucasU params (2 * t) = lucasV params t * lucasU params t := by
  have h := (subsequence_secondOrderRecurrence params (lucasU params) (lucasU_add_two params)
    t 0 ht).1 0
  rw [show t * (0 + 2) + 0 = 2 * t by ring, show t * (0 + 1) + 0 = t by ring,
    show t * 0 + 0 = 0 by ring] at h
  simpa [lucasU] using h

-- `w n = 2 ^ n` solves `w (n + 2) = 3 w (n + 1) - 2 w n`; for `t = 3` the coefficients of the
-- subsequence recurrence are `V₃ = 2 ^ 3 + 1 = 9` and `Q ^ 3 = 8`, for every offset `r`.
example (n r : ℕ) :
    (2 : ℤ) ^ (3 * (n + 2) + r) = 9 * 2 ^ (3 * (n + 1) + r) - 8 * 2 ^ (3 * n + r) := by
  have h := (subsequence_secondOrderRecurrence ⟨3, 2, by decide⟩ (fun n => (2 : ℤ) ^ n)
    (fun n => by dsimp only; ring) 3 r (by decide)).1 n
  have hV : lucasV ⟨3, 2, by decide⟩ 3 = 9 := by decide
  rw [hV] at h
  dsimp only at h
  linear_combination h

-- For `(P, Q) = (3, 2)` the discriminant `P ^ 2 - 4 Q` is `1`, so `V t ^ 2 - 4 * 2 ^ t` is the
-- square `U t ^ 2`.
example (t : ℕ) (ht : 0 < t) :
    lucasV ⟨3, 2, by decide⟩ t ^ 2 - 4 * 2 ^ t = lucasU ⟨3, 2, by decide⟩ t ^ 2 := by
  have h := (subsequence_secondOrderRecurrence ⟨3, 2, by decide⟩ (lucasU ⟨3, 2, by decide⟩)
    (lucasU_add_two _) t 0 ht).2
  dsimp only at h
  linear_combination h

-- A numerical check of that case at `t = 3`: `9 ^ 2 - 4 * 2 ^ 3 = 49 = 7 ^ 2`.
example : lucasV ⟨3, 2, by decide⟩ 3 ^ 2 - 4 * 2 ^ 3 = lucasU ⟨3, 2, by decide⟩ 3 ^ 2 ∧
    lucasU ⟨3, 2, by decide⟩ 3 = 7 := by
  decide
