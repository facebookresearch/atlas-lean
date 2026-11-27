/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.HashTable.ExpectedChainLength
import Mathlib.Tactic.NormNum

/-!
# Tests for the expected chain length under universal hashing

Generic clients use each part of `expected_chain_length_le`. Two families of functions from
`Bool` to `Fin 2` then probe the bounds. The family of all four functions is universal and
attains both universal bounds. The family of one constant function is near-universal but not
universal: it attains both near-universal bounds and exceeds the universal absent-key bound, so
the universality hypothesis cannot be weakened to near-universality there. An empty set of
stored keys gives the absent-key bound `0`, and with one slot every nonempty family is universal
and attains the absent-key bound.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.HashTableExpectedChainLengthTests

open Cslib.Algorithms.Lean.UniversalHashing
open Finset
open scoped BigOperators

/-! ### Generic clients -/

example {α : Type} {m : ℕ} {H : Finset (α → Fin m)} (hH : IsUniversal H) (S : Finset α)
    {x : α} (hx : x ∉ S) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ #S / m :=
  ((expected_chain_length_le H S x).1 hH).1 hx

example {α : Type} {m : ℕ} {H : Finset (α → Fin m)} (hH : IsUniversal H) (S : Finset α)
    {x : α} (hx : x ∈ S) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 1 + (#S - 1) / m ∧
      𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) < 1 + #S / m :=
  ((expected_chain_length_le H S x).1 hH).2 hx

example {α : Type} {m : ℕ} {H : Finset (α → Fin m)} (hH : IsNearUniversal H) (S : Finset α)
    {x : α} (hx : x ∉ S) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 2 * #S / m :=
  ((expected_chain_length_le H S x).2 hH).1 hx

example {α : Type} {m : ℕ} {H : Finset (α → Fin m)} (hH : IsNearUniversal H) (S : Finset α)
    {x : α} (hx : x ∈ S) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 1 + 2 * (#S - 1) / m ∧
      𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) < 1 + 2 * #S / m :=
  ((expected_chain_length_le H S x).2 hH).2 hx

/-- With no stored keys, the absent-key bound `#S / m` is `0`. -/
example {α : Type} {m : ℕ} {H : Finset (α → Fin m)} (hH : IsUniversal H) (x : α) :
    𝔼 h ∈ H, (#{y ∈ (∅ : Finset α) | h y = h x} : ℝ) ≤ 0 := by
  have bound := ((expected_chain_length_le H ∅ x).1 hH).1 (notMem_empty x)
  rwa [card_empty, Nat.cast_zero, zero_div] at bound

/-! ### One slot: every nonempty family is universal, and the absent-key bound is attained -/

theorem isUniversal_of_fin_one {α : Type} {H : Finset (α → Fin 1)} (hH : H.Nonempty) :
    IsUniversal H :=
  ⟨one_pos, hH, fun x y _ => by simpa using collisionCount_le_card H x y⟩

/-- With one slot every stored key is in the chain of `x`, so the average is `#S = #S / 1`. -/
example {α : Type} {H : Finset (α → Fin 1)} (hH : H.Nonempty) (S : Finset α) (x : α) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) = #S / (1 : ℕ) := by
  have hS (h : α → Fin 1) : {y ∈ S | h y = h x} = S :=
    filter_true_of_mem fun y _ => Subsingleton.elim _ _
  simp only [hS, expect_const hH, Nat.cast_one, div_one]

/-! ### All functions from `Bool` to `Fin 2`: universal, and both bounds are attained -/

/-- The family of all four functions from `Bool` to `Fin 2`. -/
abbrev allHashes : Finset (Bool → Fin 2) := univ

theorem allHashes_isUniversal : IsUniversal allHashes := by
  unfold IsUniversal collisionCount
  decide

theorem card_allHashes : #allHashes = 4 := by
  decide

/-- A universal family is near-universal, so the near-universal bounds apply to it too. -/
example : IsNearUniversal allHashes := allHashes_isUniversal.isNearUniversal

/-- An absent key: its chain holds the one stored key exactly when the two keys collide,
which happens for half of the functions, so the average is the load factor `1 / 2`. -/
theorem allHashes_absent :
    𝔼 h ∈ allHashes, (#{y ∈ ({true} : Finset Bool) | h y = h false} : ℝ) = 1 / 2 := by
  have hsum : ∑ h ∈ allHashes, #{y ∈ ({true} : Finset Bool) | h y = h false} = 2 := by
    decide
  rw [expect_eq_sum_div_card, ← Nat.cast_sum, hsum, card_allHashes]
  norm_num

example :
    𝔼 h ∈ allHashes, (#{y ∈ ({true} : Finset Bool) | h y = h false} : ℝ) =
      #({true} : Finset Bool) / 2 := by
  rw [allHashes_absent]
  simp

example :
    𝔼 h ∈ allHashes, (#{y ∈ ({true} : Finset Bool) | h y = h false} : ℝ) ≤
      #({true} : Finset Bool) / 2 :=
  ((expected_chain_length_le allHashes {true} false).1 allHashes_isUniversal).1 (by decide)

/-- A stored key: its chain holds itself, and the other stored key for half of the functions,
so the average is `1 + (2 - 1) / 2`. -/
theorem allHashes_stored :
    𝔼 h ∈ allHashes, (#{y ∈ (univ : Finset Bool) | h y = h true} : ℝ) = 3 / 2 := by
  have hsum : ∑ h ∈ allHashes, #{y ∈ (univ : Finset Bool) | h y = h true} = 6 := by
    decide
  rw [expect_eq_sum_div_card, ← Nat.cast_sum, hsum, card_allHashes]
  norm_num

example :
    𝔼 h ∈ allHashes, (#{y ∈ (univ : Finset Bool) | h y = h true} : ℝ) =
      1 + (#(univ : Finset Bool) - 1) / 2 := by
  rw [allHashes_stored]
  norm_num

/-! ### One constant function: near-universal, not universal -/

/-- The family whose only member sends every key to slot `0`. -/
abbrev constHashes : Finset (Bool → Fin 2) := {fun _ => 0}

theorem constHashes_isNearUniversal : IsNearUniversal constHashes := by
  unfold IsNearUniversal collisionCount
  decide

theorem not_constHashes_isUniversal : ¬ IsUniversal constHashes := by
  unfold IsUniversal collisionCount
  decide

/-- Every stored key shares the absent key's slot. -/
theorem constHashes_absent :
    𝔼 h ∈ constHashes, (#{y ∈ ({true} : Finset Bool) | h y = h false} : ℝ) = 1 := by
  simp [constHashes]

/-- The near-universal absent-key bound `2 * 1 / 2` is attained. -/
example :
    𝔼 h ∈ constHashes, (#{y ∈ ({true} : Finset Bool) | h y = h false} : ℝ) =
      2 * #({true} : Finset Bool) / 2 := by
  rw [constHashes_absent]
  simp

/-- The universal absent-key bound `1 / 2` fails for this near-universal family. -/
example :
    ¬ 𝔼 h ∈ constHashes, (#{y ∈ ({true} : Finset Bool) | h y = h false} : ℝ) ≤
      #({true} : Finset Bool) / 2 := by
  rw [constHashes_absent]
  norm_num

/-- The near-universal stored-key bound `1 + 2 * (2 - 1) / 2` is attained. -/
example :
    𝔼 h ∈ constHashes, (#{y ∈ (univ : Finset Bool) | h y = h true} : ℝ) =
      1 + 2 * (#(univ : Finset Bool) - 1) / 2 := by
  simp [constHashes]

example :
    𝔼 h ∈ constHashes, (#{y ∈ (univ : Finset Bool) | h y = h true} : ℝ) ≤
      1 + 2 * (#(univ : Finset Bool) - 1) / 2 :=
  (((expected_chain_length_le constHashes univ true).2 constHashes_isNearUniversal).2
    (mem_univ true)).1

end Cslib.Algorithms.Lean.HashTableExpectedChainLengthTests
