/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.IdentityProductNecklacePiCyclic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for identity-product necklaces over a product of cyclic groups -/

open MetaMathlibExt

-- In the cyclic group of order 6, two elements have fourth power one.
example : Fintype.card {x : Multiplicative (ZMod 6) // x ^ (4 : ℕ) = 1} = 2 := by
  rw [card_pow_eq_one_zmod 6 4]
  decide

-- The zero exponent counts every element, even when the order is not prime.
example : Fintype.card {x : Multiplicative (ZMod 6) // x ^ (0 : ℕ) = 1} = 6 := by
  rw [card_pow_eq_one_zmod 6 0]
  decide

-- With no factors (`m = 0`) the group is trivial and there is exactly one necklace: the formula
-- gives `(1 / n) ∑_{d ∣ n} φ(n / d) = 1` by Gauss's identity `∑_{d ∣ n} φ(d) = n`.
example (n : ℕ) (hn : 0 < n) :
    (Set.ncard {O : Set (Fin n → ∀ i : Fin 0, Multiplicative (ZMod ((![] : Fin 0 → ℕ) i))) |
        ∃ x, (List.ofFn x).prod = 1 ∧ O = tupleRotationOrbit x} : ℚ) = 1 := by
  have : ∀ i : Fin 0, NeZero ((![] : Fin 0 → ℕ) i) := fun i => i.elim0
  rw [identityProductNecklace_count_pi_cyclic 0 ![] n hn]
  simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  rw [← Nat.cast_sum, Nat.sum_div_divisors n Nat.totient, Nat.sum_totient]
  field_simp

-- For `n = 1` the only identity-product tuple is `(1)`, whatever the factors are.
example (m : ℕ) (k : Fin m → ℕ) [∀ i, NeZero (k i)] :
    (Set.ncard {O : Set (Fin 1 → ∀ i, Multiplicative (ZMod (k i))) |
        ∃ x, (List.ofFn x).prod = 1 ∧ O = tupleRotationOrbit x} : ℚ) = 1 := by
  rw [identityProductNecklace_count_pi_cyclic m k 1 one_pos]
  simp

-- `G = C₂ × C₂` and `n = 3`. By Burnside's lemma, by hand: the identity fixes all `4 ^ 2 = 16`
-- identity-product triples, and each of the two other rotations fixes only the constant triples
-- `(a, a, a)` with `a ^ 3 = 1`, that is `a = 1`; so there are `(16 + 1 + 1) / 3 = 6` necklaces.
example : (Set.ncard {O : Set (Fin 3 → ∀ i : Fin 2, Multiplicative (ZMod (![2, 2] i))) |
        ∃ x, (List.ofFn x).prod = 1 ∧ O = tupleRotationOrbit x} : ℚ) = 6 := by
  have : ∀ i : Fin 2, NeZero ((![2, 2] : Fin 2 → ℕ) i) := fun i => by
    fin_cases i <;> exact ⟨by decide⟩
  rw [identityProductNecklace_count_pi_cyclic 2 ![2, 2] 3 (by norm_num),
    show Nat.divisors 3 = {1, 3} from rfl]
  simp [Fin.prod_univ_two, Nat.totient_prime Nat.prime_three]
  norm_num

-- `G = C₆` and `n = 4`. By hand: the identity fixes all `6 ^ 3 = 216` identity-product tuples,
-- the rotations by one and by three steps fix the constant tuples `(a, a, a, a)` with `a ^ 4 = 1`
-- (two of them), and the rotation by two steps fixes the tuples `(a, b, a, b)` with
-- `(a b) ^ 2 = 1` (twelve of them); so there are `(216 + 2 + 12 + 2) / 4 = 58` necklaces.
example : (Set.ncard {O : Set (Fin 4 → ∀ i : Fin 1, Multiplicative (ZMod (![6] i))) |
        ∃ x, (List.ofFn x).prod = 1 ∧ O = tupleRotationOrbit x} : ℚ) = 58 := by
  have : ∀ i : Fin 1, NeZero ((![6] : Fin 1 → ℕ) i) := fun i => by
    fin_cases i; exact ⟨by decide⟩
  rw [identityProductNecklace_count_pi_cyclic 1 ![6] 4 (by norm_num),
    show Nat.divisors 4 = {1, 2, 4} from rfl]
  simp [Finset.sum_insert, show Nat.totient 4 = 2 from rfl, show Nat.totient 2 = 1 from rfl]
  norm_num
