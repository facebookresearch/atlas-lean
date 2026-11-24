/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.PeriodicTupleProductCount
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum

/-! # Tests for counting periodic tuples with product in a conjugation-closed set -/

open MetaMathlibExt

-- `k = 1`: the tuples invariant under rotation by one position are the constant tuples
-- `(a, …, a)`, whose product is `a ^ n`, so there are `#{a | a ^ n ∈ K}` of them.
example (G : Type*) [Group G] [Fintype G] (K : Set G) (hK : ∀ g c, c ∈ K → g * c * g⁻¹ ∈ K)
    (n : ℕ) (hn : 0 < n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod ∈ K ∧ x ∘ ⇑(finRotate n) = x} =
      Set.ncard {a : G | a ^ n ∈ K} := by
  simpa using card_productIn_period G K hK n 1 hn (one_dvd n)

-- `k = n`: rotating by `n` positions is the identity, so every tuple counts, and the tuples with
-- product in `K` number `|K| · |G| ^ (n - 1)`; here `n = 3`.
example (G : Type*) [Group G] [Fintype G] (K : Set G) (hK : ∀ g c, c ∈ K → g * c * g⁻¹ ∈ K) :
    Set.ncard {x : Fin 3 → G | (List.ofFn x).prod ∈ K} = K.ncard * Fintype.card G ^ 2 := by
  have h := card_productIn_period G K hK 3 3 (by norm_num) dvd_rfl
  rw [show (finRotate 3) ^ 3 = 1 by decide] at h
  simpa using h

-- `K = {1}`, which is closed under conjugation: the identity-product tuples.
example (G : Type*) [Group G] [Fintype G] (n k : ℕ) (hn : 0 < n) (hk : k ∣ n) :
    Set.ncard {x : Fin n → G | (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate n) ^ k) = x} =
      Set.ncard {a : G | a ^ (n / k) = 1} * Fintype.card G ^ (k - 1) := by
  simpa using card_productIn_period G {1} (fun g c hc => by simp_all) n k hn hk

-- `G = C₄`, `K = {1}`, `n = 4`, `k = 2`. By hand: the tuples are `(a, b, a, b)` with
-- `2 (a + b) = 0` in `ZMod 4`, that is `a + b ∈ {0, 2}`: `4 · 2 = 8` of them. The formula gives
-- `#{a | 2 a = 0} · 4 ^ 1 = 2 · 4`.
example : Set.ncard {x : Fin 4 → Multiplicative (ZMod 4) |
    (List.ofFn x).prod ∈ ({1} : Set (Multiplicative (ZMod 4))) ∧
      x ∘ ⇑((finRotate 4) ^ 2) = x} = 8 := by
  rw [card_productIn_period _ _ (fun g c hc => by simp_all) 4 2 (by norm_num) (by norm_num)]
  simp only [Set.mem_singleton_iff]
  rw [Set.ncard_eq_toFinset_card']
  decide

-- `G = C₄`, `K = {g}` for a generator `g`, `n = 4`, `k = 2`: the product `(a b) ^ 2` of such a
-- tuple is a square, and no square of `C₄` is a generator, so there are none.
example : Set.ncard {x : Fin 4 → Multiplicative (ZMod 4) |
    (List.ofFn x).prod ∈ ({Multiplicative.ofAdd 1} : Set (Multiplicative (ZMod 4))) ∧
      x ∘ ⇑((finRotate 4) ^ 2) = x} = 0 := by
  rw [card_productIn_period _ _ (fun g c hc => by simp_all [mul_comm g]) 4 2 (by norm_num)
    (by norm_num)]
  simp only [Set.mem_singleton_iff]
  rw [Set.ncard_eq_toFinset_card']
  decide

-- Brute force, without the theorem: over `C₂`, all four tuples `(a, b, a, b)` have product
-- `1`, which is the theorem's right-hand side `#{a | a ^ 2 = 1} · 2 ^ 1` for `n = 4`, `k = 2`.
example : Set.ncard {x : Fin 4 → Multiplicative (ZMod 2) |
    (List.ofFn x).prod ∈ ({1} : Set (Multiplicative (ZMod 2))) ∧
      x ∘ ⇑((finRotate 4) ^ 2) = x} =
    Set.ncard {a : Multiplicative (ZMod 2) | a ^ (4 / 2) ∈ ({1} : Set (Multiplicative (ZMod 2)))} *
      Fintype.card (Multiplicative (ZMod 2)) ^ (2 - 1) := by
  simp only [Set.mem_singleton_iff]
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  decide

-- The identity-product specialization counts eight period-two tuples over `C₄`.
example : Set.ncard {x : Fin 4 → Multiplicative (ZMod 4) |
    (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate 4) ^ 2) = x} = 8 := by
  rw [card_identityProduct_period _ 4 2 (by decide) (by decide)]
  decide

-- For three entries over `C₂`, the identity is the only constant tuple with product one.
example : Set.ncard {x : Fin 3 → Multiplicative (ZMod 2) |
    (List.ofFn x).prod = 1 ∧ x ∘ ⇑((finRotate 3) ^ 1) = x} = 1 := by
  rw [card_identityProduct_period _ 3 1 (by decide) (by decide)]
  decide
