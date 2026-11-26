/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Ring

/-!
# Columns `j` and `j⁻¹` of a repetend table match

For a modulus `n` and a length `L`, the rows of a repetend table are the bases `b` with
`1 ≤ b < n`, `gcd(b, n) = 1` and multiplicative order `L` modulo `n`, and column `j` holds the
digits `⌊b^(j+1)/n⌋ mod b`. If `j j' ≡ 1 (mod L)`, then columns `j` and `j'` are equal as
multisets (`MetaMathlibExt.repetend_column_eq_column_of_mul_modEq_one`; its docstring gives the
source).

## Proof outline

The digit `⌊c^(k+1)/n⌋ mod c` is the long-division digit `⌊c (c^k mod n)/n⌋`. Send a row `b` to
`c = b^j mod n`. Since `j` is prime to `L`, `c` is again a row, and `c^(j') ≡ b^(j j') ≡ b`
(mod `n`), so `c^(j') mod n = b`. Hence the digit of `c` in column `j'` is
`⌊c b/n⌋ = ⌊b (b^j mod n)/n⌋`, the digit of `b` in column `j`. The map `b ↦ b^j mod n` permutes
the rows, with inverse `c ↦ c^(j') mod n`, so the two columns are equal as multisets.
-/

public section

namespace MetaMathlibExt

/-- The `k`-th base-`c` digit of `1/n` is the long-division digit `⌊c (c^k mod n)/n⌋`. -/
private theorem repetend_column_digit_eq (c k n : ℕ) (hn : 0 < n) :
    c ^ (k + 1) / n % c = c * (c ^ k % n) / n := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  have h : c ^ (k + 1) = c * (c ^ k % n) + n * (c * (c ^ k / n)) := by
    conv_lhs => rw [pow_succ', ← Nat.mod_add_div (c ^ k) n]
    ring
  rw [h, Nat.add_mul_div_left _ _ hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  refine Nat.div_lt_of_lt_mul ?_
  rw [Nat.mul_comm n c]
  exact Nat.mul_lt_mul_of_pos_left (Nat.mod_lt _ hn) hc

/-- If `k k' ≡ 1 (mod L)`, then `b ↦ b^k mod n` sends a row of the repetend table to a row, and
`c ↦ c^(k') mod n` undoes it. -/
private theorem repetend_column_row_pow_mod {n L k k' b : ℕ} (hkk : k * k' ≡ 1 [MOD L])
    (hb : b ∈ (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L) :
    b ^ k % n ∈ ((Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L) ∧
      (b ^ k % n) ^ k' % n = b := by
  obtain ⟨hb, hcop, hord⟩ := Finset.mem_filter.mp hb
  obtain ⟨hb1, hbn⟩ := Finset.mem_Ico.mp hb
  have hn : 0 < n := by omega
  have hcast : ((b ^ k % n : ℕ) : ZMod n) = (b : ZMod n) ^ k := by
    rw [ZMod.natCast_mod, Nat.cast_pow]
  have hcop' : Nat.Coprime (b ^ k % n) n := by
    have : Nat.Coprime (b ^ k) n := hcop.pow_left k
    unfold Nat.Coprime at this ⊢
    rw [← Nat.gcd_rec, Nat.gcd_comm, this]
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, Nat.mod_lt _ hn⟩, hcop', ?_⟩, ?_⟩
  · -- A residue prime to `n ≥ 2` is not `0`.
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
    rw [h0, Nat.coprime_zero_left] at hcop'
    omega
  · -- The power `b^k` has the same order as `b`, since `k` is prime to `L`.
    rw [hcast, Nat.Coprime.orderOf_pow]
    · exact hord
    · rw [hord]
      exact (Nat.coprime_of_mul_modEq_one k' hkk).symm
  · -- `(b^k)^(k') = b^(k k') = b` modulo `n`, and both sides lie in `[0, n)`.
    have hpow : (((b ^ k % n) ^ k' : ℕ) : ZMod n) = (b : ZMod n) := by
      rw [Nat.cast_pow, hcast, ← pow_mul, ← pow_mod_orderOf, hord, hkk, ← hord, pow_mod_orderOf,
        pow_one]
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hbn] at hpow
    exact hpow

-- The proof uses only `j * j' ≡ 1 [MOD L]`: it gives `Nat.Coprime j L` and, when `L = 0`, forces
-- `j = j' = 1`. The hypothesis `j ^ 2 ≢ 1` only makes the two columns distinct in the source.
set_option linter.unusedVariables false in
/-- **Columns $j$ and $j^{-1}$ of a repetend table match.** Let $n$ and $L \ge 1$ be natural
numbers, and consider the repetend table of $1/n$ whose rows are the natural numbers $1 \le b < n$
coprime to $n$ of multiplicative order $L$ modulo $n$, and whose column $j$ holds the digits
$\lfloor b^{j+1}/n \rfloor \bmod b$. If $j$ and $j'$ are natural numbers with $j$ coprime to $L$,
$j^2 \not\equiv 1 \pmod L$ and $jj' \equiv 1 \pmod L$, then columns $j$ and $j'$ are equal as
multisets.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Theorem 2 (`integers-2025-A26-thm-2`). -/
theorem repetend_column_eq_column_of_mul_modEq_one (n L j j' : ℕ) (hL : 0 < L)
    (hj : Nat.Coprime j L) (hjsq : ¬ j ^ 2 ≡ 1 [MOD L]) (hjj : j * j' ≡ 1 [MOD L]) :
    let B := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
    (B.val.map fun b => b ^ (j + 1) / n % b) = B.val.map fun b => b ^ (j' + 1) / n % b := by
  intro B
  have hjj' : j' * j ≡ 1 [MOD L] := by rwa [Nat.mul_comm]
  -- `b ↦ b^j mod n` permutes the rows, with inverse `c ↦ c^(j') mod n`.
  have hinj : Set.InjOn (fun b => b ^ j % n) B := fun b hb b' hb' h => by
    rw [← (repetend_column_row_pow_mod hjj hb).2, ← (repetend_column_row_pow_mod hjj hb').2]
    exact congrArg (· ^ j' % n) h
  have himage : B.image (fun b => b ^ j % n) = B := by
    refine Finset.Subset.antisymm (fun c hc => ?_) (fun c hc => ?_)
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      exact (repetend_column_row_pow_mod hjj hb).1
    · exact Finset.mem_image.mpr ⟨_, (repetend_column_row_pow_mod hjj' hc).1,
        (repetend_column_row_pow_mod hjj' hc).2⟩
  conv_rhs => rw [← himage, Finset.image_val_of_injOn hinj, Multiset.map_map]
  refine Multiset.map_congr rfl fun b hb => ?_
  replace hb : b ∈ B := Finset.mem_val.mp hb
  -- The digit of `b^j mod n` in column `j'` is the digit of `b` in column `j`.
  have hn : 0 < n := by
    have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).2
    omega
  simp only [Function.comp_apply]
  rw [repetend_column_digit_eq _ _ _ hn, repetend_column_digit_eq _ _ _ hn,
    (repetend_column_row_pow_mod hjj hb).2, Nat.mul_comm]

end MetaMathlibExt
