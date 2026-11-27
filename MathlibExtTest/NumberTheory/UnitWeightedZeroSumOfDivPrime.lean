/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import MathlibExt.NumberTheory.UnitWeightedZeroSumOfDivPrime

namespace MetaMathlibExt

/-- For `n' = 1` the hypothesis holds in the trivial ring `ℤ_1`, so the multiples of `p` of any
sequence in `ℤ_{p · 1}` form a unit-weighted zero-sum sequence. -/
example {p k : ℕ} (hp : p.Prime) (z : Fin k → ZMod (p * 1)) :
    ∃ b : Fin k → ZMod (p * 1), (∀ i, IsUnit (b i)) ∧
      ∑ i, b i * ((p : ZMod (p * 1)) * z i) = 0 :=
  unitWeightedZeroSum_of_div_prime hp z ⟨fun _ => 1, fun _ => isUnit_one, Subsingleton.elim _ _⟩

/-- In `ℤ_6 = ℤ_{2 · 3}`, the reductions `1, 2` of `z = (1, 2)` modulo `3` have the zero sum
`1 · 1 + 1 · 2 = 0` in `ℤ_3`, so `(2 · 1, 2 · 2)` has a unit-weighted zero sum in `ℤ_6`. -/
example : ∃ b : Fin 2 → ZMod 6, (∀ i, IsUnit (b i)) ∧
    ∑ i, b i * (((2 : ℕ) : ZMod 6) * ![1, 2] i) = 0 :=
  unitWeightedZeroSum_of_div_prime (p := 2) (n' := 3) Nat.prime_two ![1, 2]
    ⟨fun _ => 1, fun _ => isUnit_one, by decide⟩

/-- For `n' = 0` both `ℤ_{2 · 0}` and `ℤ_0` are `ℤ`: the zero sum `1 · 1 + (-1) · 1 = 0` of
`z = (1, 1)` gives a unit-weighted zero sum of `(2 · 1, 2 · 1)`. -/
example : ∃ b : Fin 2 → ZMod (2 * 0), (∀ i, IsUnit (b i)) ∧
    ∑ i, b i * (((2 : ℕ) : ZMod (2 * 0)) * ![1, 1] i) = 0 :=
  unitWeightedZeroSum_of_div_prime Nat.prime_two ![1, 1]
    ⟨![1, -1], fun i => by fin_cases i <;> simp, by decide⟩

end MetaMathlibExt
