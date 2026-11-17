/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ShiftedPrimeTotient
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for the average of `(p - 1) / φ(p - 1)`
-/

@[expose] public section

open Finset Nat

-- `p ≡ 1 [MOD m] ↔ m ∣ p - 1` for `p ≥ 1` is Mathlib's `Nat.modEq_iff_dvd'`.
example (p m : ℕ) (hp : 1 ≤ p) : p ≡ 1 [MOD m] ↔ m ∣ p - 1 :=
  ⟨fun h => (Nat.modEq_iff_dvd' hp).mp h.symm, fun h => ((Nat.modEq_iff_dvd' hp).mpr h).symm⟩
example : primeCountingMod 10 3 1 = 1 := by decide
example : primeCountingMod 10 3 1 ≤ 10 / 3 := primeCountingMod_one_le_div 10 3
-- Boundary `δ = 0`: the bound reads `π(N; 0, 1) ≤ 0`.
example (N : ℕ) : primeCountingMod N 0 1 = 0 := by
  have := primeCountingMod_one_le_div N 0
  simpa using this

-- Interchange of summation at `N = 5` with `f = 1`: both sides equal `6`.
example : ∑ p ∈ primesLE 5, ∑ _δ ∈ (p - 1).divisors, (1 : ℕ) =
    ∑ δ ∈ Icc 1 5, (primeCountingMod 5 δ 1 : ℕ) * 1 :=
  sum_primesLE_sum_divisors_sub_one_eq 5 fun _ => 1
example : ∑ p ∈ primesLE 5, ∑ _δ ∈ (p - 1).divisors, (1 : ℕ) = 6 := by decide
example : ∑ δ ∈ Icc 1 5, primeCountingMod 5 δ 1 = 6 := by decide

example : (fun x : ℝ => ∑ p ∈ primesLE ⌊x⌋₊, ((p - 1 : ℕ) : ℝ) / ((p - 1).totient : ℝ))
    =O[Filter.atTop] (fun x : ℝ => x / Real.log x) :=
  sum_primesLE_sub_one_div_totient_isBigO
