/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.AACarmichaelAuxiliaryProduct

open Finset Filter MetaMathlibExt Real

-- Recover Wright's two disjoint products. Either set may be empty.
example (A : ℝ) :
    ∀ᶠ z : ℕ in atTop, ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ log z ^ (2 * A) →
      ∀ S T : Finset ℕ, Disjoint S T → (∀ q ∈ S ∪ T, q.Prime ∧ ∃ g : ℕ,
        g ∣ ∏ r ∈ (Iic z).filter (fun r : ℕ => r.Prime ∧ (z : ℝ) / 2 ≤ r), r ∧
        g.primeFactors.card = ⌊log z⌋₊ ∧ q = g * j + 1) →
      (ArithmeticFunction.carmichael (S.prod id * T.prod id) : ℝ) ≤ exp (4 * z / 5) := by
  filter_upwards [carmichael_prod_primes_eq_mul_add_one_le_exp A] with z hz
  intro j hj hjz S T hST h
  simpa [Finset.prod_union hST] using hz j hj hjz (S ∪ T) h

-- For z = j = 6, both interval primes 3 and 5 give auxiliary primes (19 and 31).
-- The Carmichael function attains the common multiple J * j here.
example :
    ArithmeticFunction.carmichael (19 * 31) =
      (∏ r ∈ (Iic 6).filter (fun r : ℕ => r.Prime ∧ (6 : ℝ) / 2 ≤ r), r) * 6 := by
  have hhalf (r : ℕ) : (6 : ℝ) / 2 ≤ r ↔ 3 ≤ r := by norm_num
  simp_rw [hhalf]
  rw [ArithmeticFunction.carmichael_mul (by decide : Nat.Coprime 19 31),
    ArithmeticFunction.carmichael_of_prime (by decide : Nat.Prime 19),
    ArithmeticFunction.carmichael_of_prime (by decide : Nat.Prime 31)]
  decide
