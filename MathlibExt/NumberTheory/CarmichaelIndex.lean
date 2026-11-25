/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
# Carmichael indices

The Carmichael index counts the fixed points of the power map `x ↦ x ^ n` modulo `n`.
For positive `n`, this map cannot have exactly one residue that it fails to fix.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Carmichael index.** For a natural number $n$, the Carmichael index $N(n)$ is the number of
integers $a$ with $0 \le a \le n - 1$ and $a^n \equiv a \pmod{n}$.

Source: Atsushi Yamagami and Youichi Inaba, *On a Formula and Some Properties of Carmichael
Indices*, INTEGERS 24 (2024), Article A40, Definition 1. -/
public def carmichaelIndex (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun a => a ^ n ≡ a [MOD n]).card

/-- **The Carmichael index of 1.** The Carmichael index of $1$ is $N(1) = 1$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Section 1. -/
public theorem carmichaelIndex_one : carmichaelIndex 1 = 1 := by decide

/-- **The Carmichael indices of 4 and 66.** The Carmichael index satisfies $N(4) = 2$ and
$N(66) = 24$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Example 1 (Table 1) and Example 3. -/
public theorem carmichaelIndex_four_and_sixtySix :
    carmichaelIndex 4 = 2 ∧ carmichaelIndex 66 = 24 := by
  constructor <;> decide +kernel

private theorem carmichaelIndex_ne_sub_one.unique_exception {n : ℕ} [NeZero n]
    (h : carmichaelIndex n = n - 1) : ∃! x : ZMod n, x ^ n ≠ x := by
  let bad := (Finset.range n).filter fun a => ¬ a ^ n ≡ a [MOD n]
  have hsum : carmichaelIndex n + bad.card = n := by
    simpa only [carmichaelIndex, bad, Finset.card_range] using
      (Finset.card_filter_add_card_filter_not (s := Finset.range n) (fun a => a ^ n ≡ a [MOD n]))
  have hn := NeZero.pos n
  obtain ⟨a, ha, hu⟩ := Finset.card_eq_one_iff_existsUnique.mp (show bad.card = 1 by omega)
  simp only [bad, Finset.mem_filter, Finset.mem_range, ← ZMod.natCast_eq_natCast_iff,
    Nat.cast_pow] at ha hu
  refine ⟨a, ha.2, fun x hx => ?_⟩
  have hval : x.val = a := hu _ ⟨x.val_lt, by simpa using hx⟩
  rw [← ZMod.natCast_zmod_val x, hval]

/-- **The Carmichael index of $n$ is never $n - 1$.** For every positive integer $n$, the
Carmichael index $N(n)$, the number of integers $a$ with $0 \le a \le n - 1$ and
$a^n \equiv a \pmod{n}$, is not equal to $n - 1$.

Source: Yamagami and Inaba, *On a Formula and Some Properties of Carmichael Indices*,
INTEGERS 24 (2024), Article A40, Theorem 2 (`integers-2024-A40-thm-2`). -/
public theorem carmichaelIndex_ne_sub_one (n : ℕ) (hn : 0 < n) :
    carmichaelIndex n ≠ n - 1 := by
  by_cases hsmall : n ≤ 4
  · interval_cases n <;> decide
  have : NeZero n := ⟨hn.ne'⟩
  intro h
  obtain ⟨x, hx, huniq⟩ := carmichaelIndex_ne_sub_one.unique_exception h
  rcases Nat.even_or_odd n with heven | hodd
  · -- The sole exception would be -1, so both 2 and -2 would be fixed.
    have small_ne_zero (k : ℕ) (hk : 0 < k ∧ k ≤ 4) : (k : ZMod n) ≠ 0 := by
      intro hk0
      have := Nat.le_of_dvd hk.1 ((ZMod.natCast_eq_zero_iff k n).mp hk0)
      omega
    have hneg : (-1 : ZMod n) ^ n ≠ -1 := by
      rw [heven.neg_one_pow]
      exact fun e => small_ne_zero 2 (by decide) (by linear_combination e)
    have fixed {y : ZMod n} (hy : y ≠ -1) : y ^ n = y := by
      by_contra hbad
      exact hy ((huniq y hbad).trans (huniq _ hneg).symm)
    have hpos := fixed (y := 2) (fun e =>
      small_ne_zero 3 (by decide) (by linear_combination e))
    have hneg₂ := fixed (y := -2) (fun e =>
      small_ne_zero 1 (by decide) (by linear_combination -e))
    rw [heven.neg_pow] at hneg₂
    exact small_ne_zero 4 (by decide) (by linear_combination hneg₂ - hpos)
  · -- Negation preserves failures for odd n, and its only fixed point is zero.
    have hneg : (-x) ^ n ≠ -x := by simpa [hodd.neg_pow] using hx
    rcases (ZMod.neg_eq_self_iff x).mp (huniq _ hneg) with rfl | hdouble
    · exact hx (zero_pow hn.ne')
    · obtain ⟨k, hk⟩ := hodd
      omega

end

end MetaMathlibExt
