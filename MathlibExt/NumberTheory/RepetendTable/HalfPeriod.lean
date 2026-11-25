/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Half-period symmetry of repetends

In a cyclic unit group, an even-order base reaches `-1` halfway through its period.
The complementary remainders then give a constant sum of the paired digits.
-/

namespace MetaMathlibExt

/-- **Half-period symmetry of the repetend of $1/n$.** Let $n$ be a natural number whose unit
group $(\mathbb{Z}/n\mathbb{Z})^\times$ is cyclic, let $L > 0$ be even, and let $b < n$ be a
natural number whose multiplicative order modulo $n$ is $L$. For natural numbers $m$ write
$b_m = b^m \bmod n$ and $r_m = \lfloor b^{m+1}/n \rfloor \bmod b$, the $m$-th base-$b$ digit of
$1/n$. Then for every natural number $j$ we have $b_{j+L/2} = n - b_j$ and
$r_j + r_{j+L/2} = r_{L/2}$.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 29 (`integers-2025-A26-lem-29`). -/
public theorem pow_add_half_mod_eq_and_digit_add (n L b j : ℕ) [IsCyclic (ZMod n)ˣ]
    (hL : Even L) (hL0 : 0 < L) (hbn : b < n) (hb : orderOf (b : ZMod n) = L) :
    b ^ (j + L / 2) % n = n - b ^ j % n ∧
      b ^ (j + 1) / n % b + b ^ (j + L / 2 + 1) / n % b = b ^ (L / 2 + 1) / n % b := by
  have hn : 0 < n := by omega
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨u, hu⟩ := (orderOf_pos_iff.mp (hb.symm ▸ hL0)).isUnit
  have hu_order : orderOf u = L := by rw [← orderOf_units, hu, hb]
  have hdiv : L ∣ n.totient := by
    rw [← hu_order, ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have hn₂ : 2 < n := by
    by_contra! h
    have ht : n.totient = 1 := by interval_cases n <;> decide
    have h1 := Nat.dvd_one.mp (ht ▸ hdiv)
    exact Nat.not_even_one (h1 ▸ hL)
  let : Fact (1 < n) := ⟨by omega⟩
  have hhalf_order : orderOf (u ^ (L / 2)) = 2 := by
    rw [← hu_order]
    exact orderOf_pow_orderOf_div (hu_order.symm ▸ hL0.ne') (hu_order.symm ▸ even_iff_two_dvd.mp hL)
  have hneg_order : orderOf (-1 : (ZMod n)ˣ) = 2 := by
    have : Fact (2 < n) := ⟨hn₂⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by simp [pow_two]) ?_
    intro h
    exact ZMod.neg_one_ne_one (by simpa using congrArg Units.val h)
  have hhalf : (b : ZMod n) ^ (L / 2) = -1 := by
    classical
    have hcard : (Finset.univ.filter fun v : (ZMod n)ˣ => orderOf v = 2).card ≤ 1 := by
      rw [IsCyclic.card_orderOf_eq_totient (hhalf_order ▸ orderOf_dvd_card), Nat.totient_two]
    have heq := Finset.card_le_one.mp hcard
      _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhalf_order⟩)
      _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneg_order⟩)
    simpa [hu] using congrArg Units.val heq
  let r (i : ℕ) := b ^ i % n
  let d (i : ℕ) := b ^ (i + 1) / n % b
  have hval (i : ℕ) : ((b : ZMod n) ^ i).val = r i := by
    rw [← Nat.cast_pow, ZMod.val_natCast]
  have half (i : ℕ) : r (i + L / 2) = n - r i := by
    have hunit : IsUnit (b : ZMod n) := ⟨u, hu⟩
    have : NeZero ((b : ZMod n) ^ i) := ⟨(hunit.pow i).ne_zero⟩
    rw [← hval, pow_add, hhalf, mul_neg_one, ZMod.val_neg_of_ne_zero, hval]
  have pair (i : ℕ) : r (i + L / 2) + r i = n :=
    (half i).symm ▸ Nat.sub_add_cancel (Nat.mod_lt (b ^ i) hn).le
  -- A long-division step: multiplying the current remainder produces the digit and next remainder.
  have step (i : ℕ) : n * d i + r (i + 1) = b * r i := by
    have hd : d i = b * r i / n := by
      dsimp only [d, r]
      rw [← Nat.mod_mul_left_div_self, pow_succ', Nat.mul_mod_mul_left]
    have hr : r (i + 1) = b * r i % n := by
      dsimp only [r]
      rw [Nat.mul_mod_mod, pow_succ']
    rw [hd, hr, Nat.div_add_mod]
  have digitSum (i : ℕ) : d i + d (i + L / 2) = b - 1 := by
    have hp := pair (i + 1)
    have hs : i + 1 + L / 2 = i + L / 2 + 1 := by omega
    have hm : n * (d i + d (i + L / 2) + 1) = n * b := calc
      _ = (n * d i + r (i + 1)) + (n * d (i + L / 2) + r (i + L / 2 + 1)) := by
        rw [hs] at hp
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_add]
        omega
      _ = b * r i + b * r (i + L / 2) := by rw [step, step]
      _ = n * b := by rw [← Nat.mul_add, add_comm (r i), pair, mul_comm]
    have he := Nat.eq_of_mul_eq_mul_left hn hm
    omega
  have hd₀ : d 0 = 0 := by simp [d, Nat.div_eq_of_lt hbn]
  have hbase : d (L / 2) = b - 1 := by simpa [hd₀] using digitSum 0
  exact ⟨half j, (digitSum j).trans hbase.symm⟩

end MetaMathlibExt
