/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.DivisibilityRuns
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact formula and asymptotics for the length-one divisibility run count

For a natural bound $B$, the count ranges over integer initial quintuples in $[-B, B]^5$
with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$. A run of length at least one requires
the first Gibonacci term to be nonzero and divide the first Tribonacci term. The exact formula
counts nonzero multiples separately from a zero first Tribonacci term, where the other two
Tribonacci initial values cannot both be zero. For $B \ge 2$, the count is
$32 B^4 \log B + O(B^4)$. For the error bound, the elementary harmonic-number
bounds suffice in place of the sharper Dirichlet estimate used in the paper.

## References

- Nicholas Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
  Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, pp. 1–13, Proposition 4 (p. 7).
- Mathlib's `Mathlib.NumberTheory.Harmonic.Bounds` for the harmonic-number bounds.
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

/-- **Asymptotics of the length-one run count.** There is a real constant $K$ such that for every
natural number $B \ge 2$ the number $A_B(1)$ of integer tuples $(x, y, a, b, c) \in [-B, B]^5$
with $(x, y) \ne (0, 0)$ and $(a, b, c) \ne (0, 0, 0)$ that have a divisibility run of length at
least $1$ satisfies $|A_B(1) - 32 B^4 \log B| \le K B^4$; that is,
$A_B(1) = 32 B^4 \log B + O(B^4)$.

Source: Smirnov, *Finite Divisibility Runs Between Generalized Fibonacci and
Tribonacci Sequences*, INTEGERS 26 (2026), Article A122, Proposition 4
(`integers-2026-A122-prop-4`). -/
public theorem divRunCount_one_asymptotic :
    ∃ K : ℝ, ∀ B : ℕ, 2 ≤ B →
      |(divRunCount B 1 : ℝ) - 32 * (B : ℝ) ^ 4 * Real.log B| ≤ K * (B : ℝ) ^ 4 := by
  refine ⟨238, fun B hB => ?_⟩
  let b : ℝ := B
  let D : ℝ := ∑ m ∈ Icc 1 B, ((B / m : ℕ) : ℝ)
  have hb : 1 ≤ b := by
    change (1 : ℝ) ≤ (B : ℝ)
    exact_mod_cast (show 1 ≤ B by omega)
  have hb₀ : 0 ≤ b := zero_le_one.trans hb
  -- Rounding down costs at most one per term in the harmonic sum.
  have hsum : (∑ m ∈ Icc 1 B, b / (m : ℝ)) = b * (harmonic B : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, mul_sum,
      div_eq_mul_inv]
  have hlow : b * (harmonic B : ℝ) ≤ D + b := calc
    _ = ∑ m ∈ Icc 1 B, b / (m : ℝ) := hsum.symm
    _ ≤ ∑ m ∈ Icc 1 B, (((B / m : ℕ) : ℝ) + 1) := by
      refine sum_le_sum fun m _ => ?_
      simpa only [Nat.floor_div_eq_div] using (Nat.lt_floor_add_one ((B : ℝ) / m)).le
    _ = D + b := by simp [D, b, sum_add_distrib, Nat.card_Icc]
  have hupp : D ≤ b * (harmonic B : ℝ) := by
    rw [← hsum]
    exact sum_le_sum fun _ _ => Nat.cast_div_le
  have hlogH : Real.log b ≤ (harmonic B : ℝ) := by
    simpa only [Nat.floor_natCast] using log_le_harmonic_floor (B : ℝ) hb₀
  have hD : |D - b * Real.log b| ≤ b := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith only [mul_le_mul_of_nonneg_left hlogH hb₀, hlow]
    · linarith only [mul_le_mul_of_nonneg_left (harmonic_le_one_add_log B) hb₀, hupp]
  -- Isolate the errors from the divisor sum, the cubic coefficient, and the exact remainder.
  let w : ℝ := 2 * b + 1
  let A : ℝ := 4 * w ^ 3
  let R : ℝ := 2 * b * w * (w ^ 2 - 1)
  have hw : w ≤ 3 * b := by dsimp [w]; linarith only [hb]
  have hw₁ : 1 ≤ w := by dsimp [w]; linarith only [hb₀]
  have hA : A ≤ 108 * b ^ 3 := calc
    A ≤ 4 * (3 * b) ^ 3 := by
      dsimp [A]
      gcongr
    _ = _ := by ring
  have hcoeff₀ : 0 ≤ A - 32 * b ^ 3 := by
    dsimp [A, w]
    nlinarith only [hb₀, sq_nonneg b]
  have hcoeff : A - 32 * b ^ 3 ≤ 76 * b ^ 2 := by
    dsimp [A, w]
    nlinarith only [hb, mul_nonneg hb₀ (sub_nonneg.mpr hb)]
  have hw₂ : 0 ≤ w ^ 2 - 1 := sub_nonneg.mpr (one_le_pow₀ hw₁)
  have hw₂le : w ^ 2 - 1 ≤ (3 * b) ^ 2 := calc
    w ^ 2 - 1 ≤ w ^ 2 := sub_le_self _ zero_le_one
    _ ≤ (3 * b) ^ 2 := by gcongr
  have hR₀ : 0 ≤ R := mul_nonneg (by positivity) hw₂
  have hR : R ≤ 54 * b ^ 4 := calc
    R ≤ 2 * b * (3 * b) * (3 * b) ^ 2 := by
      dsimp [R]
      gcongr
    _ = _ := by ring
  have hlog₀ : 0 ≤ Real.log b := Real.log_nonneg hb
  have hlog : Real.log b ≤ b := (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hb)).trans
    (sub_le_self _ zero_le_one)
  have hsub : 1 ≤ (2 * B + 1) ^ 2 := by
    exact Nat.succ_le_iff.mpr (Nat.pow_pos (by omega))
  rw [divRunCount_one]
  push_cast [Nat.cast_sub hsub]
  change |A * D + R - 32 * b ^ 4 * Real.log b| ≤ 238 * b ^ 4
  have hsplit : A * D + R - 32 * b ^ 4 * Real.log b =
      A * (D - b * Real.log b) + (A - 32 * b ^ 3) * (b * Real.log b) + R := by ring
  rw [hsplit]
  calc
    _ ≤ |A * (D - b * Real.log b)| + |(A - 32 * b ^ 3) * (b * Real.log b)| + |R| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (108 * b ^ 3) * b + (76 * b ^ 2) * (b * b) + 54 * b ^ 4 := by
      rw [abs_mul A, abs_mul (A - 32 * b ^ 3), abs_of_nonneg (show 0 ≤ A by positivity),
        abs_of_nonneg hcoeff₀, abs_of_nonneg (mul_nonneg hb₀ hlog₀), abs_of_nonneg hR₀]
      gcongr
    _ = _ := by ring

end MetaMathlibExt
