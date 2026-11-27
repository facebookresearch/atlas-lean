/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.UniversalHashing.NearUniversal
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic

import CSLibExt.Algorithms.Lean.DataStructures.HashTable.UniversalChain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Expected chain length under universal hashing

A hash table with chaining that stores a finite set `S` of keys using a hash function
`h : α → Fin m` keeps, in slot `i`, the chain of the stored keys `y` with `h y = i`. The chain
searched for a key `x` is the one in slot `h x`, of length `#{y ∈ S | h y = h x}`.

Fix `S` and `x`, and draw `h` uniformly from a finite family `H`; the expectation is the
average `𝔼 h ∈ H` over the members of `H` (`Finset.expect`). If `H` is universal
(`IsUniversal`), the expected chain length is at most the load factor `#S / m` when `x ∉ S`, and
at most `1 + (#S - 1) / m`, hence less than `1 + #S / m`, when `x ∈ S`. If `H` is near-universal
(`IsNearUniversal`), the same holds with the load factor doubled: at most `2 * #S / m` for
`x ∉ S`, and at most `1 + 2 * (#S - 1) / m < 1 + 2 * #S / m` for `x ∈ S`.

The proof writes the chain length as the sum, over the stored keys `y`, of the indicator of
`h y = h x`. Summed over the members of `H`, this counting gives the multiplied-out bounds
`sum_card_collide_mul_le_of_not_mem` and `sum_card_collide_mul_le_of_mem` for universal
families, applied here with `H` indexing itself; dividing by `#H` and `m` gives the universal
bounds. For a near-universal family, linearity of expectation writes the average as the sum of
the collision probabilities `collisionCount H y x / #H`, each at most `2 / m` for `y ≠ x` and
equal to `1` for `y = x`.

This file bounds chain lengths only. For indexed universal families (`IsUniversalOn`),
`HashTable.UniversalChain` bounds the scan events of the concrete hash table's lookups and
erasures in multiplied-out form.

## Main statements

* `expected_chain_length_le`: the four bounds above.

## References

* J. Erickson, *Algorithms*, lecture notes, Lecture 5 "Hash Tables" (Spring 2017), Sections 5.3
  and 5.4.
* MIT OpenCourseWare, 6.046J *Design and Analysis of Algorithms* (Spring 2015), Lecture 8 notes
  "Hashing", section "Universal Hashing": the bound `1 + α` for a stored key.
-/

public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.UniversalHashing

open Finset
open scoped BigOperators

universe u

variable {α : Type u} {m : ℕ}

/-- The average chain length is the sum of the collision probabilities with the stored keys. -/
private theorem expect_card_filter_eq_sum (H : Finset (α → Fin m)) (S : Finset α) (x : α) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) = ∑ y ∈ S, (collisionCount H y x : ℝ) / #H := by
  simp_rw [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [expect_sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [expect_eq_sum_div_card, collisionCount, card_filter, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-- A universal family is universal as the indexed family of its own members. -/
private theorem isUniversalOn_id {H : Finset (α → Fin m)} (hH : IsUniversal H) :
    IsUniversalOn H id :=
  hH

/-- The average chain length is the total chain length over the family divided by its size. -/
private theorem expect_card_filter_eq_div (H : Finset (α → Fin m)) (S : Finset α) (x : α) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) =
      ((∑ h ∈ H, #{y ∈ S | h y = h x} : ℕ) : ℝ) / #H := by
  rw [expect_eq_sum_div_card, Nat.cast_sum]

/-- A collision bound `c / m`, in the multiplied-out form, bounds a collision probability. -/
private theorem collision_div_le {H : Finset (α → Fin m)} {c : ℕ} (hm : 0 < m)
    (hH : H.Nonempty) {y x : α} (hyx : collisionCount H y x * m ≤ c * #H) :
    (collisionCount H y x : ℝ) / #H ≤ c / m := by
  have hH' : (0 : ℝ) < #H := by exact_mod_cast hH.card_pos
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_div_iff₀ hH' hm']
  exact_mod_cast hyx

/-- Under a collision bound `c / m`, an absent key has expected chain length at most
`c * #S / m`. -/
private theorem expect_le_of_notMem {H : Finset (α → Fin m)} {c : ℕ} (hm : 0 < m)
    (hH : H.Nonempty) (hc : ∀ y z : α, y ≠ z → collisionCount H y z * m ≤ c * #H)
    {S : Finset α} {x : α} (hx : x ∉ S) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ c * #S / m := by
  rw [expect_card_filter_eq_sum]
  calc ∑ y ∈ S, (collisionCount H y x : ℝ) / #H ≤ ∑ _y ∈ S, (c : ℝ) / m :=
        sum_le_sum fun y hy => collision_div_le hm hH (hc y x fun e => hx (e ▸ hy))
    _ = c * #S / m := by rw [sum_const, nsmul_eq_mul]; ring

/-- Under a collision bound `c / m`, a stored key has expected chain length at most
`1 + c * (#S - 1) / m`. -/
private theorem expect_le_of_mem {H : Finset (α → Fin m)} {c : ℕ} (hm : 0 < m)
    (hH : H.Nonempty) (hc : ∀ y z : α, y ≠ z → collisionCount H y z * m ≤ c * #H)
    {S : Finset α} {x : α} (hx : x ∈ S) :
    𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 1 + c * (#S - 1) / m := by
  classical
  have hH' : (#H : ℝ) ≠ 0 := by exact_mod_cast hH.card_pos.ne'
  have hS : ((#(S.erase x) : ℕ) : ℝ) = #S - 1 := by
    rw [card_erase_of_mem hx, Nat.cast_sub (card_pos.mpr ⟨x, hx⟩), Nat.cast_one]
  rw [expect_card_filter_eq_sum, ← sum_erase_add _ _ hx, collisionCount_self, div_self hH']
  calc ∑ y ∈ S.erase x, (collisionCount H y x : ℝ) / #H + 1
      ≤ ∑ _y ∈ S.erase x, (c : ℝ) / m + 1 :=
        add_le_add_left (sum_le_sum fun y hy =>
          collision_div_le hm hH (hc y x (ne_of_mem_erase hy))) 1
    _ = 1 + c * (#S - 1) / m := by rw [sum_const, nsmul_eq_mul, hS]; ring

/-- The stored-key bound `1 + c * (#S - 1) / m` is below `1 + c * #S / m`. -/
private theorem one_add_mul_sub_one_div_lt {c : ℕ} (hc : 0 < c) (hm : 0 < m) (n : ℕ) :
    1 + (c : ℝ) * (n - 1) / m < 1 + c * n / m := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  gcongr
  linarith

/--
**Expected chain length under universal hashing.** Let $H$ be a finite family of functions
from a set $\alpha$ to $\{0, 1, \dots, m - 1\}$, let $S \subseteq \alpha$ be a finite set of
$n = |S|$ stored keys, and let $x \in \alpha$ be a key. For $h \in H$ let
$\ell_h(x) = |\{y \in S : h(y) = h(x)\}|$, the length of the chain in slot $h(x)$ when $S$ is
stored with chaining using $h$, and write $\mathbb{E}_h[\ell_h(x)]$ for the average of
$\ell_h(x)$ over the members $h$ of $H$, the expectation for $h$ drawn uniformly from $H$.

1. If $H$ is universal and $x \notin S$, then $\mathbb{E}_h[\ell_h(x)] \le n/m$.
2. If $H$ is universal and $x \in S$, then $\mathbb{E}_h[\ell_h(x)] \le 1 + (n - 1)/m$ and
   $\mathbb{E}_h[\ell_h(x)] < 1 + n/m$.
3. If $H$ is near-universal and $x \notin S$, then $\mathbb{E}_h[\ell_h(x)] \le 2n/m$.
4. If $H$ is near-universal and $x \in S$, then $\mathbb{E}_h[\ell_h(x)] \le 1 + 2(n - 1)/m$ and
   $\mathbb{E}_h[\ell_h(x)] < 1 + 2n/m$.

Here $S$ and $x$ are fixed before $h$ is drawn, and $n/m$ is the load factor.
-/
public theorem expected_chain_length_le (H : Finset (α → Fin m)) (S : Finset α) (x : α) :
    (IsUniversal H →
      (x ∉ S → 𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ #S / m) ∧
      (x ∈ S → 𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 1 + (#S - 1) / m ∧
        𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) < 1 + #S / m)) ∧
    (IsNearUniversal H →
      (x ∉ S → 𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 2 * #S / m) ∧
      (x ∈ S → 𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 1 + 2 * (#S - 1) / m ∧
        𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) < 1 + 2 * #S / m)) := by
  refine ⟨fun hH => ?_, fun ⟨hm, hH, hc⟩ => ?_⟩
  · have hm' : (0 : ℝ) < m := by exact_mod_cast hH.1
    have hH' : (0 : ℝ) < #H := by exact_mod_cast hH.2.1.card_pos
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have hsum := sum_card_collide_mul_le_of_not_mem (isUniversalOn_id hH) S x hx
      simp only [id] at hsum
      rw [expect_card_filter_eq_div, div_le_div_iff₀ hH' hm']
      exact_mod_cast hsum.trans_eq (Nat.mul_comm _ _)
    · have hsum := sum_card_collide_mul_le_of_mem (isUniversalOn_id hH) S x hx
      simp only [id] at hsum
      have hsum' : (∑ h ∈ H, (#{y ∈ S | h y = h x} : ℝ)) * m ≤
          #H * (m + ((#S : ℝ) - 1)) := by
        have hcast := (Nat.cast_le (α := ℝ)).mpr hsum
        push_cast [Nat.cast_sub (card_pos.mpr ⟨x, hx⟩)] at hcast
        exact hcast
      have hle : 𝔼 h ∈ H, (#{y ∈ S | h y = h x} : ℝ) ≤ 1 + (#S - 1) / m := by
        rw [expect_eq_sum_div_card, div_le_iff₀ hH']
        calc ∑ h ∈ H, (#{y ∈ S | h y = h x} : ℝ)
            ≤ #H * (m + ((#S : ℝ) - 1)) / m := (le_div_iff₀ hm').mpr hsum'
          _ = (1 + (#S - 1) / m) * #H := by field_simp
      have hlt := one_add_mul_sub_one_div_lt one_pos hH.1 #S
      simp only [Nat.cast_one, one_mul] at hlt
      exact ⟨hle, hle.trans_lt hlt⟩
  · refine ⟨fun hx => ?_, fun hx => ?_⟩
    · exact_mod_cast expect_le_of_notMem hm hH hc hx
    · have hle := expect_le_of_mem hm hH hc hx
      have hlt := one_add_mul_sub_one_div_lt two_pos hm #S
      push_cast at hle hlt
      exact ⟨hle, hle.trans_lt hlt⟩

end Cslib.Algorithms.Lean.UniversalHashing
