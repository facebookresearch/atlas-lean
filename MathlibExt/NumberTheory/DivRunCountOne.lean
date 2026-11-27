/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.DivisibilityRuns
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring

/-!
# Exact formula for the length-one divisibility run count

The first Gibonacci term must be a nonzero divisor of the first Tribonacci term.
We count the nonzero multiples separately from the zero term, where the other two
Tribonacci terms cannot both be zero.
-/

open Finset

namespace MetaMathlibExt

private def intBox (B : ℕ) : Finset ℤ := Icc (-(B : ℤ)) B

private theorem mem_intBox {B : ℕ} {x : ℤ} : x ∈ intBox B ↔ x.natAbs ≤ B := by
  simp only [intBox, mem_Icc]
  omega

private theorem card_intBox (B : ℕ) : (intBox B).card = 2 * B + 1 := by
  rw [intBox, Int.card_Icc]
  omega

private theorem sum_intBox_erase_zero (B : ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ (intBox B).erase 0, f x.natAbs = 2 * ∑ m ∈ Icc 1 B, f m := by
  let pos : ℕ ↪ ℤ := ⟨fun m => (m : ℤ), fun _ _ h => Int.ofNat_inj.mp h⟩
  let neg : ℕ ↪ ℤ := ⟨fun m => -(m : ℤ), fun _ _ h => Int.ofNat_inj.mp (neg_injective h)⟩
  have hpos (m : ℕ) : pos m = (m : ℤ) := rfl
  have hneg (m : ℕ) : neg m = -(m : ℤ) := rfl
  let s := Icc (1 : ℕ) B
  have hset : (intBox B).erase 0 = s.map pos ∪ s.map neg := by
    ext x
    simp only [mem_erase, mem_intBox, mem_union, mem_map, mem_Icc, s, hpos, hneg]
    constructor
    · intro ⟨hx, hb⟩
      have hm : 1 ≤ x.natAbs := by omega
      by_cases h : 0 ≤ x
      · exact Or.inl ⟨x.natAbs, ⟨hm, hb⟩, by omega⟩
      · exact Or.inr ⟨x.natAbs, ⟨hm, hb⟩, by omega⟩
    · rintro (⟨m, ⟨hm, hb⟩, rfl⟩ | ⟨m, ⟨hm, hb⟩, rfl⟩) <;>
        simp [hb, show m ≠ 0 by omega]
  have hd : Disjoint (s.map pos) (s.map neg) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hx
    obtain ⟨n, hn, h⟩ := mem_map.mp hy
    have hm' := (mem_Icc.mp hm).1
    have hn' := (mem_Icc.mp hn).1
    change -(n : ℤ) = m at h
    omega
  rw [hset, sum_union hd, sum_map, sum_map, two_mul]
  simp [hpos, hneg, s]

private theorem card_intBox_erase_zero (B : ℕ) : ((intBox B).erase 0).card = 2 * B := by
  simpa using sum_intBox_erase_zero B (fun _ => 1)

private theorem card_nonzero_multiples (B : ℕ) {x : ℤ} (hx : x ≠ 0) :
    ((intBox B).filter fun a => a ≠ 0 ∧ x ∣ a).card = 2 * (B / x.natAbs) := by
  let scale : ℤ ↪ ℤ := ⟨fun q => x * q, fun _ _ h => mul_left_cancel₀ hx h⟩
  have hscale (q : ℤ) : scale q = x * q := rfl
  have hset : (intBox B).filter (fun a => a ≠ 0 ∧ x ∣ a) =
      ((intBox (B / x.natAbs)).erase 0).map scale := by
    ext a
    simp only [mem_filter, mem_intBox, mem_map, mem_erase, hscale]
    have hd : 0 < x.natAbs := by omega
    constructor
    · rintro ⟨ha, hane, q, rfl⟩
      rw [Int.natAbs_mul, mul_comm] at ha
      exact ⟨q, ⟨fun hq => hane (by simp [hq]), (Nat.le_div_iff_mul_le hd).mpr ha⟩, rfl⟩
    · rintro ⟨q, ⟨hq, hb⟩, rfl⟩
      refine ⟨?_, mul_ne_zero hx hq, dvd_mul_right x q⟩
      rw [Int.natAbs_mul, mul_comm]
      exact (Nat.le_div_iff_mul_le hd).mp hb
  rw [hset, card_map, card_intBox_erase_zero]

private def runOneTail (B : ℕ) (x y : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (intBox B ×ˢ intBox B ×ˢ intBox B).filter fun t =>
    (x, y) ≠ (0, 0) ∧ t ≠ (0, 0, 0) ∧ IsDivRunUpTo x y t.1 t.2.1 t.2.2 1

private theorem card_runOneTail (B : ℕ) {x y : ℤ} (hx : x ≠ 0) :
    (runOneTail B x y).card =
      2 * (B / x.natAbs) * (2 * B + 1) ^ 2 + ((2 * B + 1) ^ 2 - 1) := by
  let box := intBox B
  let pairs := box ×ˢ box
  let multiples := box.filter fun a => a ≠ 0 ∧ x ∣ a
  have hzero : (0 : ℤ) ∈ box := mem_intBox.mpr (by simp)
  have hp : (0, 0) ∈ pairs := mem_product.mpr ⟨hzero, hzero⟩
  have hxy : (x, y) ≠ (0, 0) := fun h => hx (congrArg Prod.fst h)
  have hset : runOneTail B x y = multiples ×ˢ pairs ∪ ({0} ×ˢ pairs.erase (0, 0)) := by
    ext ⟨a, b, c⟩
    by_cases ha : a = 0
    · subst a
      simp [runOneTail, (isDivRunUpTo_small x y 0 b c).1, hx, hxy, ← show box = intBox B from rfl,
        hzero, pairs, multiples, and_assoc, and_comm]
    · simp [runOneTail, (isDivRunUpTo_small x y a b c).1, hx, hxy, ← show box = intBox B from rfl,
        ha, Ne.symm ha, pairs, multiples, and_assoc, and_comm]
  have hd : Disjoint (multiples ×ˢ pairs) ({0} ×ˢ pairs.erase (0, 0)) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    have ht0 := (mem_filter.mp (mem_product.mp ht).1).2.1
    exact ht0 (mem_singleton.mp (mem_product.mp ht').1)
  rw [hset, card_union_of_disjoint hd]
  simp only [card_product, card_singleton, one_mul, card_erase_of_mem hp]
  simp [multiples, pairs, box, card_nonzero_multiples B hx, card_product, card_intBox, pow_two]

/-- **Exact formula for the length-one run count.** For every natural number $B$, let
$D(B) = \sum_{m=1}^{B} \lfloor B/m \rfloor$ and let $A_B(1)$ be the number of integer tuples
$(x, y, a, b, c) \in [-B, B]^5$ with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have
a divisibility run of length at least $1$. Then
$$A_B(1) = 4(2B+1)^3 D(B) + 2B(2B+1)\left((2B+1)^2 - 1\right).$$

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
public theorem divRunCount_one (B : ℕ) :
    divRunCount B 1 = 4 * (2 * B + 1) ^ 3 * ∑ m ∈ Finset.Icc 1 B, B / m
      + 2 * B * (2 * B + 1) * ((2 * B + 1) ^ 2 - 1) := by
  classical
  calc
    divRunCount B 1 = ∑ x ∈ intBox B, ∑ y ∈ intBox B, (runOneTail B x y).card := by
      simp only [divRunCount, runOneTail, intBox, card_filter, sum_product]
    _ = ∑ x ∈ (intBox B).erase 0, ∑ y ∈ intBox B, (runOneTail B x y).card := by
      symm
      apply sum_subset (erase_subset _ _)
      intro x hx hnot
      have h : x = 0 := by by_contra h; exact hnot (mem_erase.mpr ⟨h, hx⟩)
      subst x
      simp [runOneTail, (isDivRunUpTo_small _ _ _ _ _).1]
    _ = ∑ x ∈ (intBox B).erase 0,
        (2 * (2 * B + 1) ^ 3 * (B / x.natAbs) + (2 * B + 1) * ((2 * B + 1) ^ 2 - 1)) := by
      apply sum_congr rfl
      intro x hx
      simp only [card_runOneTail B (mem_erase.mp hx).1, sum_const, Nat.nsmul_eq_mul, card_intBox]
      ring
    _ = _ := by
      rw [sum_add_distrib, ← mul_sum, sum_intBox_erase_zero, sum_const, Nat.nsmul_eq_mul,
        card_intBox_erase_zero]
      ring

end MetaMathlibExt
