/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Small bases of order greater than two come in pairs

For a modulus `n` and a length `L`, the rows of a repetend table are the bases `b` with
`1 ≤ b < n`, `gcd(b, n) = 1` and multiplicative order `L` modulo `n`. When `L > 2` there is an
even number of them (`MetaMathlibExt.even_card_small_bases_orderOf`; its docstring gives the
source).

## Proof outline

For `n ≤ 1` there are no such bases. For `n ≥ 2`, send a base `b` to the representative in
`[0, n)` of its inverse modulo `n`. This map sends the rows to rows, since a unit and its inverse
have the same order, and it is an involution. It has no fixed point: a base equal to its own
inverse satisfies `b^2 ≡ 1 (mod n)`, so its order divides `2`, which `L > 2` excludes. So the
rows split into pairs `{b, b⁻¹}`, and their number is even (`Finset.sum_involution` in
`ZMod 2`).
-/

public section

namespace MetaMathlibExt

/-- **Small bases of order greater than two come in pairs.** For every natural number $n$ and
every $L > 2$, the number of integers $b$ with $1 \le b < n$ and $\gcd(b, n) = 1$ whose
multiplicative order modulo $n$ is $L$ is even.

Source: R. J. Booth and D. J. Horton, *Matched Column Sets in Repetend Tables*, INTEGERS 25 (2025),
Article A26, Lemma 3 (`integers-2025-A26-lem-2`). -/
theorem even_card_small_bases_orderOf (n L : ℕ) (hL : 2 < L) :
    Even ((Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L).card := by
  set s := (Finset.Ico 1 n).filter fun b => Nat.Coprime b n ∧ orderOf (b : ZMod n) = L
  -- For `n ≤ 1` the interval `[1, n)` is empty.
  rcases Nat.lt_or_ge n 2 with hn | hn
  · rw [show s = ∅ from Finset.filter_eq_empty_iff.mpr fun b hb => by
      simp only [Finset.mem_Ico] at hb; omega]
    exact ⟨0, rfl⟩
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨hn⟩
  -- The involution sends a base to the representative in `[0, n)` of its inverse modulo `n`.
  let g : ℕ → ℕ := fun b => ((b : ZMod n)⁻¹).val
  have key : ∀ b ∈ s, g b ∈ s ∧ g (g b) = b ∧ g b ≠ b := by
    intro b hb
    obtain ⟨hb, hcop, hord⟩ := Finset.mem_filter.mp hb
    have hbn : b < n := (Finset.mem_Ico.mp hb).2
    -- Write `u` for the unit `b` of `ZMod n`; `g b` represents `u⁻¹`.
    set u : (ZMod n)ˣ := ZMod.unitOfCoprime b hcop
    have hu : (u : ZMod n) = b := ZMod.coe_unitOfCoprime b hcop
    have hg : ((g b : ℕ) : ZMod n) = ((u⁻¹ : (ZMod n)ˣ) : ZMod n) := by
      simp only [g, ZMod.natCast_zmod_val, ← hu, ZMod.inv_coe_unit]
    have hordu : orderOf u = L := by rw [← orderOf_units, hu, hord]
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨?_, ZMod.val_lt _⟩, ?_, ?_⟩, ?_, ?_⟩
    · -- `g b ≠ 0`, since `u⁻¹` is a unit of the nontrivial ring `ZMod n`.
      refine Nat.one_le_iff_ne_zero.mpr fun h0 => (u⁻¹).ne_zero ?_
      rw [← hg, h0, Nat.cast_zero]
    · -- `g b` is coprime to `n`, being the value of a unit.
      simp only [g, ← hu, ZMod.inv_coe_unit]
      exact ZMod.val_coe_unit_coprime _
    · -- `u⁻¹` has the same order as `u`.
      rw [hg, orderOf_units, orderOf_inv, hordu]
    · -- Inverting twice gives back `u`, which `b < n` represents.
      change (((g b : ℕ) : ZMod n)⁻¹).val = b
      rw [hg, ZMod.inv_coe_unit, inv_inv, hu, ZMod.val_cast_of_lt hbn]
    · -- A base equal to its inverse has order dividing `2`.
      intro hfix
      have huu : u⁻¹ = u := Units.ext (by rw [← hg, hfix, hu])
      have h2 : orderOf u ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [sq, ← inv_mul_cancel u, huu])
      have := Nat.le_of_dvd two_pos h2
      omega
  -- Counting in `ZMod 2`, the pairs `{b, g b}` contribute `1 + 1 = 0`.
  have hsum : ∑ _b ∈ s, (1 : ZMod 2) = 0 :=
    Finset.sum_involution (fun b _ => g b) (fun _ _ => by decide)
      (fun b hb _ => (key b hb).2.2) (fun b hb => (key b hb).1) (fun b hb => (key b hb).2.1)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hsum

end MetaMathlibExt
