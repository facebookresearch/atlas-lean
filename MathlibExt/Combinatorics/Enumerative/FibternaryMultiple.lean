/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.ModEq

/-!
# Fibternary multiples

A collision among base-nine repunits modulo `n` gives a positive difference made
of base-nine ones followed by zeros. In base three each such digit occupies two places.
-/

namespace MetaMathlibExt

private def repunit9 (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, 9 ^ i

private theorem repunit9_strictMono : StrictMono repunit9 := by
  apply strictMono_nat_of_lt_succ
  intro k
  unfold repunit9
  rw [Finset.sum_range_succ]
  exact lt_add_of_pos_right _ (Nat.pow_pos (by decide))

private theorem repunit9_add (i k : ℕ) :
    repunit9 (i + k) = repunit9 i + 9 ^ i * repunit9 k := by
  simp only [repunit9, Finset.sum_range_add, pow_add, Finset.mul_sum]

/-- Prepending a bit and a separating zero to a nonempty ternary expansion. -/
private theorem fibternary_block {x d : ℕ} (hx : 0 < x) (hd : d ≤ 1)
    (h : (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 x) :
    (∀ e ∈ Nat.digits 3 (d + 9 * x), e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 (d + 9 * x) := by
  have hdigits : Nat.digits 3 (d + 9 * x) = d :: 0 :: Nat.digits 3 x := by
    rw [show d + 9 * x = d + 3 * (0 + 3 * x) by simp [← Nat.mul_assoc],
      Nat.digits_add 3 (by decide) d _ (by omega)
        (Or.inr (by simpa using Nat.mul_ne_zero (by decide : 3 ≠ 0) hx.ne')),
      Nat.digits_add 3 (by decide) 0 x (by decide) (Or.inr hx.ne')]
  rw [hdigits]
  exact ⟨by simpa [hd] using h.1, by simpa [List.infix_cons_iff, List.prefix_cons_iff] using h.2⟩

private theorem fibternary_shifted_repunit (i k : ℕ) :
    let x := 9 ^ i * repunit9 (k + 1)
    (∀ e ∈ Nat.digits 3 x, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 x := by
  have hpos (j : ℕ) : 0 < repunit9 (j + 1) := by
    simpa [repunit9] using repunit9_strictMono (Nat.zero_lt_succ j)
  induction i with
  | zero =>
    simp only [pow_zero, one_mul]
    induction k with
    | zero =>
      have h : repunit9 1 = 1 := by simp [repunit9]
      rw [h]
      decide
    | succ k ih =>
      have h : repunit9 (k + 1 + 1) = 1 + 9 * repunit9 (k + 1) := by
        rw [show k + 1 + 1 = 1 + (k + 1) by ac_rfl, repunit9_add]
        simp [repunit9]
      rw [h]
      exact fibternary_block (hpos k) le_rfl ih
  | succ i ih =>
    simpa only [pow_succ', mul_assoc, zero_add] using
      fibternary_block (Nat.mul_pos (Nat.pow_pos (by decide)) (hpos k)) (d := 0) (by decide) ih

/-- **Fibternary multiples.** Every positive integer $n$ has a positive multiple $m$ that is
Fibternary: the base-$3$ digits of $m$ are all $0$ or $1$, and no two consecutive digits
of $m$ are both $1$.

Source: E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to
Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4,
Proposition 22 (`jis-2025-25.5.4-prop-22`). -/
public theorem exists_fibternary_multiple (n : ℕ) (hn : 0 < n) :
    ∃ m, 0 < m ∧ n ∣ m ∧ (∀ e ∈ Nat.digits 3 m, e ≤ 1) ∧ ¬ [1, 1] <:+: Nat.digits 3 m := by
  let f (i : Fin (n + 1)) : Fin n := ⟨repunit9 i % n, Nat.mod_lt _ hn⟩
  obtain ⟨a, b, hab, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have hmod : repunit9 a ≡ repunit9 b [MOD n] := congrArg Fin.val hf
  obtain ⟨i, j, hij, hmod⟩ : ∃ i j : ℕ, i < j ∧ repunit9 i ≡ repunit9 j [MOD n] := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, hmod⟩
    · exact ⟨b, a, h, hmod.symm⟩
  have hlt := repunit9_strictMono hij
  refine ⟨repunit9 j - repunit9 i, Nat.sub_pos_of_lt hlt, (Nat.modEq_iff_dvd' hlt.le).mp hmod, ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hij)
  have heq : repunit9 (i + 1 + k) - repunit9 i = 9 ^ i * repunit9 (k + 1) := by
    rw [show i + 1 + k = i + (k + 1) by omega, repunit9_add, Nat.add_sub_cancel_left]
  rw [heq]
  exact fibternary_shifted_repunit i k

end MetaMathlibExt
