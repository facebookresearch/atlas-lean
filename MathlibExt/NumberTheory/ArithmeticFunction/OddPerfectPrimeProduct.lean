/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith

/-! # A bound on a prime that raises the odd prime product above two -/

namespace MetaMathlibExt

/-- **Bound on a prime that pushes $\prod p/(p-1)$ past $2$.** Let $s$ be a finite set of odd
primes with $\prod_{p \in s} p/(p-1) \le 2$, and let $q$ be an odd prime with
$\left(\prod_{p \in s} p/(p-1)\right) \cdot q/(q-1) > 2$. Then
$q \le 2 \prod_{p \in s} (p - 1) - 1$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Lemma 12 (`integers-2025-A59-lem-12`). -/
public theorem le_two_mul_prod_sub_one_sub_one_of_two_lt
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ Odd p)
    (hle : ∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1) ≤ 2)
    (q : ℕ) (hq : q.Prime) (hqodd : Odd q)
    (hgt : 2 < (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) * ((q : ℚ) / ((q : ℚ) - 1))) :
    q ≤ 2 * ∏ p ∈ s, (p - 1) - 1 := by
  let n := ∏ p ∈ s, p
  let d := ∏ p ∈ s, (p - 1)
  have hd : (0 : ℚ) < d := by
    exact_mod_cast Finset.prod_pos fun p hp => Nat.sub_pos_of_lt (hs p hp).1.one_lt
  have hratio : (∏ p ∈ s, (p : ℚ) / ((p : ℚ) - 1)) = (n : ℚ) / d := by
    simp only [n, d, Finset.prod_div_distrib, Nat.cast_prod]
    congr 1
    exact Finset.prod_congr rfl fun p hp => by rw [Nat.cast_sub (hs p hp).1.one_le, Nat.cast_one]
  rw [hratio] at hle hgt
  -- The odd numerator is at least one unit below the even number 2d.
  obtain ⟨k, hk⟩ : Odd n :=
    s.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun p hp => (hs p hp).2
  have hle' : n ≤ 2 * d := by exact_mod_cast (div_le_iff₀ hd).mp hle
  have hgap : n + 1 ≤ 2 * d := by omega
  have hgap' : (n : ℚ) + 1 ≤ 2 * d := by exact_mod_cast hgap
  have hqpos : (0 : ℚ) < (q : ℚ) - 1 := sub_pos.mpr (by exact_mod_cast hq.one_lt)
  rw [div_mul_div_comm, lt_div_iff₀ (mul_pos hd hqpos)] at hgt
  have hq₀ : (0 : ℚ) ≤ q := by exact_mod_cast hqodd.pos.le
  have hbound : (q : ℚ) < 2 * d := by
    linarith [mul_le_mul_of_nonneg_right hgap' hq₀]
  exact Nat.le_pred_of_lt (show q < 2 * d by exact_mod_cast hbound)

end MetaMathlibExt
