/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Distinct columns in order-six repetend tables

`MetaMathlibExt.repetend_columns_ne_of_three_pow_of_six` proves that the six columns of
the order-six repetend table for `3 ^ k * t` are pairwise distinct when `2 ≤ k` and
`t = 1 ∨ t = 2`.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*,
INTEGERS 25 (2025), Article A26, Lemma 34.
-/

namespace MetaMathlibExt

private def rowRemainder (r a j : ℕ) : ℕ :=
  match j with
  | 0 => 1
  | 1 => 3 * r * a - 1
  | 2 => 3 * r * a + 1
  | 3 => 9 * r - 1
  | 4 => 3 * r * (3 - a) + 1
  | 5 => 3 * r * (3 - a) - 1
  | _ => 1

private def rowDigit (r a j : ℕ) : ℕ :=
  match j with
  | 0 => 0
  | 1 => r * a ^ 2 - a
  | 2 => r * a ^ 2 - 1
  | 3 => 3 * r * a - 2
  | 4 => 2 * r + a - 2
  | _ => 2 * r - 1

private theorem row_remainder_lt (r a j : ℕ) (hr : 0 < r) (ha : a = 1 ∨ a = 2) :
    rowRemainder r a j < 9 * r := by
  rcases ha with rfl | rfl <;> rcases j with _ | _ | _ | _ | _ | _ | j <;>
    norm_num [rowRemainder] <;> omega

private theorem row_step (r a j : ℕ) (hr : 0 < r) (ha : a = 1 ∨ a = 2) (hj : j < 6) :
    (3 * r * a - 1) * rowRemainder r a j =
      9 * r * rowDigit r a j + rowRemainder r a (j + 1) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rcases ha with rfl | rfl <;> interval_cases j <;>
    simp [rowRemainder, rowDigit, Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul,
      Nat.add_sub_assoc] <;> ring

private theorem row_pow_mod (r a j : ℕ) (hr : 0 < r) (ha : a = 1 ∨ a = 2) (hj : j ≤ 6) :
    (3 * r * a - 1) ^ j % (9 * r) = rowRemainder r a j := by
  induction j with
  | zero => simp only [pow_zero, rowRemainder]; exact Nat.mod_eq_of_lt (by omega)
  | succ j ih =>
    rw [pow_succ', ← Nat.mul_mod_mod, ih (by omega), row_step r a j hr ha (by omega)]
    simp only [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (row_remainder_lt r a (j + 1) hr ha)

private theorem row_digit_eq (r a j : ℕ) (hr : 0 < r) (ha : a = 1 ∨ a = 2) (hj : j < 6) :
    (3 * r * a - 1) ^ (j + 1) / (9 * r) % (3 * r * a - 1) = rowDigit r a j := by
  rw [← Nat.mod_mul_left_div_self, pow_succ', Nat.mul_mod_mul_left,
    row_pow_mod r a j hr ha (by omega), row_step r a j hr ha hj,
    Nat.mul_add_div (by omega), Nat.div_eq_of_lt (row_remainder_lt r a (j + 1) hr ha), add_zero]

private theorem row_order (r a : ℕ) (hr : 0 < r) (ha : a = 1 ∨ a = 2) :
    orderOf ((3 * r * a - 1 : ℕ) : ZMod (9 * r)) = 6 := by
  have : Fact (1 < 9 * r) := ⟨by omega⟩
  have hp (j : ℕ) (hj : j ≤ 6) :
      (((3 * r * a - 1 : ℕ) : ZMod (9 * r)) ^ j).val = rowRemainder r a j := by
    rw [← Nat.cast_pow, ZMod.val_natCast, row_pow_mod r a j hr ha hj]
  apply orderOf_eq_of_pow_and_pow_div_prime
  · apply ZMod.val_injective
    rw [hp 6 (by omega), ZMod.val_one]
    rfl
  · intro p hprime hdvd
    have hcases : p = 2 ∨ p = 3 := by
      have h : p ∣ 2 * 3 := hdvd
      rcases hprime.dvd_mul.mp h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hprime (by decide)).mp h)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hprime (by decide)).mp h)
    intro heq
    have hv := congrArg ZMod.val heq
    rcases hcases with rfl | rfl <;> rw [hp _ (by norm_num), ZMod.val_one] at hv
    · norm_num [rowRemainder] at hv
      omega
    · rcases ha with rfl | rfl <;> norm_num [rowRemainder] at hv <;> omega

private theorem rows_eq (r : ℕ) (hr : 0 < r) [IsCyclic (ZMod (9 * r))ˣ] :
    ((Finset.Ico 1 (9 * r)).filter fun b =>
      Nat.Coprime b (9 * r) ∧ orderOf (b : ZMod (9 * r)) = 6) = {3 * r - 1, 6 * r - 1} := by
  classical
  have : NeZero (9 * r) := ⟨by omega⟩
  let B := (Finset.Ico 1 (9 * r)).filter fun b =>
    Nat.Coprime b (9 * r) ∧ orderOf (b : ZMod (9 * r)) = 6
  have mem (a : ℕ) (ha : a = 1 ∨ a = 2) : 3 * r * a - 1 ∈ B := by
    have hord := row_order r a hr ha
    have hpow : ((3 * r * a - 1 : ℕ) : ZMod (9 * r)) ^ 6 = 1 := by
      simpa only [hord] using pow_orderOf_eq_one ((3 * r * a - 1 : ℕ) : ZMod (9 * r))
    have hu : IsUnit ((3 * r * a - 1 : ℕ) : ZMod (9 * r)) :=
      IsUnit.of_pow_eq_one hpow (by decide)
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ?_⟩,
      (ZMod.isUnit_iff_coprime _ _).mp hu, hord⟩
    · rcases ha with rfl | rfl <;> omega
    · rcases ha with rfl | rfl <;> omega
  have hlow : 3 * r - 1 ∈ B := by simpa only [mul_one] using mem 1 (Or.inl rfl)
  have hhigh : 6 * r - 1 ∈ B := by
    convert mem 2 (Or.inr rfl) using 1
    congr 1
    ring
  let f (b : {b // b ∈ B}) : (ZMod (9 * r))ˣ :=
    ZMod.unitOfCoprime b.val (Finset.mem_filter.mp b.property).2.1
  have hf (b : {b // b ∈ B}) : orderOf (f b) = 6 := by
    rw [← orderOf_units, ZMod.coe_unitOfCoprime]
    exact (Finset.mem_filter.mp b.property).2.2
  have hcard : (Finset.univ.filter fun u : (ZMod (9 * r))ˣ => orderOf u = 6).card = 2 := by
    have hdiv : 6 ∣ Fintype.card (ZMod (9 * r))ˣ := by
      rw [← hf ⟨3 * r - 1, hlow⟩]
      exact orderOf_dvd_card
    have ht6 : Nat.totient 6 = 2 := by decide
    simpa only [ht6] using IsCyclic.card_orderOf_eq_totient (α := (ZMod (9 * r))ˣ) hdiv
  have hle : B.card ≤ 2 := by
    rw [← hcard, ← Finset.card_attach]
    apply Finset.card_le_card_of_injOn f
    · intro b _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf b⟩
    · intro b _ c _ heq
      apply Subtype.ext
      have hv := congrArg (fun u : (ZMod (9 * r))ˣ => (u : ZMod (9 * r)).val) heq
      simpa only [f, ZMod.coe_unitOfCoprime,
        ZMod.val_cast_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp b.property).1).2,
        ZMod.val_cast_of_lt (Finset.mem_Ico.mp (Finset.mem_filter.mp c.property).1).2] using hv
  exact (Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hlow (Finset.singleton_subset_iff.mpr hhigh))
    (by rw [Finset.card_pair (by omega : 3 * r - 1 ≠ 6 * r - 1)]; exact hle)).symm

private theorem digits_ne (r i j : ℕ) (hr : 0 < r) (hi : i < 6) (hj : j < 6) (hne : i ≠ j) :
    ({rowDigit r 1 i, rowDigit r 2 i} : Multiset ℕ) ≠ {rowDigit r 1 j, rowDigit r 2 j} := by
  intro h
  have hm : rowDigit r 1 i ∈ ({rowDigit r 1 j, rowDigit r 2 j} : Multiset ℕ) := h ▸ by simp
  have hs := congrArg Multiset.sum h
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton] at hs
  interval_cases i <;> interval_cases j <;> norm_num [rowDigit] at hm hs <;> omega

@[expose] public section

/-- **Order-$6$ repetend tables of $3^k t$ have no matched columns.** Let $k \ge 2$ and
$t \in \{1, 2\}$, and put $n = 3^k t$. Let the rows be the integers $b$ with $1 \le b < n$,
$\gcd(b, n) = 1$ and multiplicative order $6$ modulo $n$, and let column $j$ be the multiset of
the digits $\lfloor b^{j+1}/n \rfloor \bmod b$ over these rows. Then for all distinct $i, j < 6$
columns $i$ and $j$ are different.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 34 (`integers-2025-A26-lem-34`). -/
public theorem repetend_columns_ne_of_three_pow_of_six (k t : ℕ) (hk : 2 ≤ k)
    (ht : t = 1 ∨ t = 2) :
    let n := 3 ^ k * t
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = 6
    ∀ i < 6, ∀ j < 6, i ≠ j →
      (B.val.map fun b => b ^ (i + 1) / n % b) ≠ B.val.map fun b => b ^ (j + 1) / n % b
    := by
  classical
  let r := 3 ^ (k - 2) * t
  have hr : 0 < r := Nat.mul_pos (pow_pos (by decide) _) (by omega)
  have hn : 3 ^ k * t = 9 * r := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_add]
    dsimp only [r]
    norm_num
    ring
  have hcyclic : IsCyclic (ZMod (3 ^ k * t))ˣ := by
    rcases ht with rfl | rfl
    · rw [Nat.mul_one]
      exact ZMod.isCyclic_units_of_prime_pow 3 (by decide) (by decide) k
    · rw [mul_comm]
      exact (ZMod.isCyclic_units_two_mul_iff_of_odd _ ((by decide : Odd 3).pow)).mpr
        (ZMod.isCyclic_units_of_prime_pow 3 (by decide) (by decide) k)
  have : IsCyclic (ZMod (9 * r))ˣ := hn ▸ hcyclic
  dsimp only
  rw [hn, rows_eq r hr]
  intro i hi j hj hij
  have hd (a j : ℕ) (ha : a = 1 ∨ a = 2) (hj : j < 6) := row_digit_eq r a j hr ha hj
  have hc (j : ℕ) (hj : j < 6) :
      ({3 * r - 1, 6 * r - 1} : Finset ℕ).val.map (fun b => b ^ (j + 1) / (9 * r) % b) =
        {rowDigit r 1 j, rowDigit r 2 j} := by
    have hlow := hd 1 j (Or.inl rfl) hj
    have hhigh := hd 2 j (Or.inr rfl) hj
    have hmul : 3 * r * 2 = 6 * r := by ring
    simp only [mul_one] at hlow
    rw [hmul] at hhigh
    simp [Finset.insert_val_of_notMem (Finset.notMem_singleton.mpr (by omega :
      3 * r - 1 ≠ 6 * r - 1)), hlow, hhigh]
  rw [hc i hi, hc j hj]
  exact digits_ne r i j hr hi hj hij

end

end MetaMathlibExt
