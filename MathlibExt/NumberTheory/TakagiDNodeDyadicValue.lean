/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.TakagiFunction
public import MathlibExt.NumberTheory.TakagiDyadicIdentities
import Mathlib.Tactic.FieldSimp

/-!
# Takagi values and divide-and-conquer D-node counts

For natural numbers `k` and `r` with `r ≤ 2 ^ k`, the Takagi value at `r / 2 ^ k` is the
D-node count of the divide-and-conquer tree on `2 ^ k + r` leaves divided by `2 ^ k`.
Prepending a binary digit to the fractional expansion gives a recurrence for the Takagi
series; the even and odd recurrences for D-node counts give the same recurrence after scaling.

## References

* Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences
  27 (2024), Article 24.2.7, pp. 1–14, Definition 3 and Theorems 8 and 9.
* Tomás M. Coronado, Mareike Fischer, Lina Herbst, Francesc Rosselló, and Kristina Wicke,
  *On the minimum value of the Colless index and the bifurcating trees that achieve it*,
  Journal of Mathematical Biology 80 (2020), pp. 1993–2054, §3.1 and Corollary 4.
-/

namespace MetaMathlibExt

open Finset

private theorem bit_le_one (n : ℕ) (j : ℤ) : takagiBit n j ≤ 1 := by
  rw [takagiBit_eq]
  split_ifs <;> decide

private theorem bit_prepend_head (k r b : ℕ) (hr : r < 2 ^ k) (hb : b < 2) :
    takagiBit (2 ^ k * b + r) k = b := by
  rw [takagiBit_eq, ite_eq_left (Int.natCast_nonneg k), Int.toNat_natCast,
    Nat.testBit_two_pow_mul_add b hr, ite_eq_right (lt_irrefl k), Nat.sub_self]
  rcases show b = 0 ∨ b = 1 by omega with rfl | rfl <;> decide

private theorem bit_prepend_low (k r b : ℕ) (hr : r < 2 ^ k) {j : ℤ} (hj : j < k) :
    takagiBit (2 ^ k * b + r) j = takagiBit r j := by
  by_cases h : 0 ≤ j
  · have hj' : j.toNat < k := by omega
    simp only [takagiBit_eq, ite_eq_left h, Nat.testBit_two_pow_mul_add b hr, ite_eq_left hj']
  · rw [takagiBit_neg _ _ (lt_of_not_ge h), takagiBit_neg _ _ (lt_of_not_ge h)]

-- The binary fraction is recovered by shifting off its leading digit.
private theorem hasSum_binary_fraction (k r : ℕ) (hr : r < 2 ^ k) :
    HasSum (fun i : ℕ ↦ (takagiBit r ((k : ℤ) - 1 - (i : ℤ)) : ℝ) / 2 ^ (i + 1))
      ((r : ℝ) / 2 ^ k) := by
  induction k generalizing r with
  | zero =>
    have hzero : r = 0 := by simpa using hr
    subst r
    have hbit (i : ℕ) : takagiBit 0 (-1 - (i : ℤ)) = 0 := takagiBit_neg _ _ (by omega)
    simp [hbit]
  | succ k ih =>
    let b := r / 2 ^ k
    let s := r % 2 ^ k
    have hs : s < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have hb : b < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).2 (by simpa [pow_succ'] using hr)
    have hr' : 2 ^ k * b + s = r := Nat.div_add_mod r _
    rw [← hr', show ((k + 1 : ℕ) : ℤ) - 1 = k by omega, ← hasSum_nat_add_iff' 1]
    have hweight (i : ℕ) :
        takagiBit (2 ^ k * b + s) ((k : ℤ) - (↑(i + 1) : ℤ)) =
          takagiBit s ((k : ℤ) - 1 - (i : ℤ)) := by
      rw [bit_prepend_low k s b hs (by omega)]
      congr 1
      omega
    simp only [hweight, sum_range_one, Nat.cast_zero, sub_zero,
      bit_prepend_head k s b hs hb, zero_add, pow_one]
    convert (ih s hs).div_const 2 using 1
    · funext i
      rw [div_div, pow_succ]
    · push_cast
      rw [pow_succ]
      field_simp
      ring

-- Adding a first digit contributes one discrepancy precisely where it differs from the current
-- digit. The old discrepancies are unchanged, including those after the last nonzero position.
private theorem ell_prepend (k r b i : ℕ) (hr : r < 2 ^ k) (hb : b < 2) :
    (takagiEll (2 ^ k * b + r) k (i + 1 + 1) : ℝ) =
      (takagiEll r ((k : ℤ) - 1) (i + 1) : ℝ) +
        (if b = 0 then (takagiBit r ((k : ℤ) - 1 - (i : ℤ)) : ℝ)
          else 1 - (takagiBit r ((k : ℤ) - 1 - (i : ℤ)) : ℝ)) := by
  have hbit (j : ℕ) :
      takagiBit (2 ^ k * b + r) ((k : ℤ) - (↑(j + 1) : ℤ)) =
        takagiBit r ((k : ℤ) - 1 - (j : ℤ)) := by
    rw [bit_prepend_low k r b hr (by omega)]
    congr 1
    omega
  have hd := bit_le_one r ((k : ℤ) - 1 - (i : ℤ))
  have hell : takagiEll (2 ^ k * b + r) k (i + 1 + 1) =
      takagiEll r ((k : ℤ) - 1) (i + 1) +
        (if b = 0 then takagiBit r ((k : ℤ) - 1 - (i : ℤ))
          else 1 - takagiBit r ((k : ℤ) - 1 - (i : ℤ))) := by
    rw [takagiEll_succ, takagiEll_succ, sum_range_succ', hbit]
    simp only [hbit, Nat.cast_zero, sub_zero, bit_prepend_head k r b hr hb]
    let S := ∑ j ∈ range i, takagiBit r ((k : ℤ) - 1 - (j : ℤ))
    let d := takagiBit r ((k : ℤ) - 1 - (i : ℤ))
    change (if d = 0 then S + b else i + 1 - (S + b)) =
      (if d = 0 then S else i - S) + (if b = 0 then d else 1 - d)
    have hS : S ≤ i := calc
      _ ≤ ∑ _j ∈ range i, 1 := sum_le_sum fun _ _ ↦ bit_le_one r _
      _ = i := by simp
    have hd' : d ≤ 1 := hd
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hb) with hb0 | hb1 <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd' with hd0 | hd1
    all_goals
      first | rw [hb0] | rw [hb1]
      first | rw [hd0] | rw [hd1]
      simp
    omega
  rw [hell, Nat.cast_add]
  split_ifs
  · rfl
  · rw [Nat.cast_sub hd, Nat.cast_one]

private theorem hasSum_takagi_prepend (k r b : ℕ) (hr : r < 2 ^ k) (hb : b < 2) {x : ℝ}
    (hx : HasSum (fun i : ℕ ↦ (takagiEll r ((k : ℤ) - 1) (i + 1) : ℝ) / 2 ^ (i + 1)) x) :
    HasSum (fun i : ℕ ↦ (takagiEll (2 ^ k * b + r) k (i + 1) : ℝ) / 2 ^ (i + 1))
      ((x + if b = 0 then (r : ℝ) / 2 ^ k else 1 - (r : ℝ) / 2 ^ k) / 2) := by
  have hgeom : HasSum (fun i : ℕ ↦ (1 : ℝ) / 2 ^ (i + 1)) 1 := by
    simpa only [pow_succ', div_div] using hasSum_geometric_two' 1
  have hbin := hasSum_binary_fraction k r hr
  have hcorr : HasSum (fun i : ℕ ↦
      (if b = 0 then (takagiBit r ((k : ℤ) - 1 - (i : ℤ)) : ℝ)
        else 1 - (takagiBit r ((k : ℤ) - 1 - (i : ℤ)) : ℝ)) / 2 ^ (i + 1))
      (if b = 0 then (r : ℝ) / 2 ^ k else 1 - (r : ℝ) / 2 ^ k) := by
    by_cases h : b = 0
    · simpa only [ite_eq_left h] using hbin
    · simpa only [ite_eq_right h, sub_div] using hgeom.sub hbin
  rw [← hasSum_nat_add_iff' 1]
  simpa only [sum_range_one, zero_add, takagiEll_one, Nat.cast_zero, zero_div, sub_zero,
    ell_prepend k r b _ hr hb, pow_succ _ (_ + 1), ← div_div, add_div] using
    (hx.add hcorr).div_const 2

-- Keeping the right endpoint in the induction lets the odd step use both neighboring offsets.
private theorem dcDNodes_leading_digit (k r : ℕ) (hr : r ≤ 2 ^ k) :
    dcDNodes (2 * 2 ^ k + r) = dcDNodes (2 ^ k + r) + r ∧
      dcDNodes (3 * 2 ^ k + r) = dcDNodes (2 ^ k + r) + (2 ^ k - r) := by
  induction k generalizing r with
  | zero =>
    have hr' : r ≤ 1 := by simpa using hr
    rcases show r = 0 ∨ r = 1 by omega with rfl | rfl <;>
      norm_num [dcDNodes_one, dcDNodes_small.1, dcDNodes_small.2.1, dcDNodes_small.2.2.1]
  | succ k ih =>
    have hpow := Nat.two_pow_pos k
    have heven (a t : ℕ) (ha : 0 < a) :
        dcDNodes (a * 2 ^ (k + 1) + 2 * t) = 2 * dcDNodes (a * 2 ^ k + t) := by
      rw [show a * 2 ^ (k + 1) + 2 * t = 2 * (a * 2 ^ k + t) by rw [pow_succ]; ring]
      exact dcDNodes_two_mul (Nat.add_pos_left (Nat.mul_pos ha hpow) _)
    have hodd (a t : ℕ) (ha : 0 < a) :
        dcDNodes (a * 2 ^ (k + 1) + (2 * t + 1)) =
          dcDNodes (a * 2 ^ k + t) + dcDNodes (a * 2 ^ k + (t + 1)) + 1 := by
      rw [show a * 2 ^ (k + 1) + (2 * t + 1) = 2 * (a * 2 ^ k + t) + 1 by rw [pow_succ]; ring,
        dcDNodes_two_mul_add_one (Nat.add_pos_left (Nat.mul_pos ha hpow) _), add_assoc (a * 2 ^ k)]
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · obtain ⟨t, rfl⟩ : ∃ t, r = 2 * t := ⟨r / 2, by omega⟩
      have ht : t ≤ 2 ^ k := by rw [pow_succ] at hr; omega
      obtain ⟨hl, hu⟩ := ih t ht
      have hbase := by simpa only [one_mul] using heven 1 t one_pos
      rw [heven 2 t (by decide), heven 3 t (by decide), hbase, hl, hu, pow_succ']
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, r = 2 * t + 1 := ⟨r / 2, by omega⟩
      have ht : t + 1 ≤ 2 ^ k := by rw [pow_succ] at hr; omega
      obtain ⟨hl, hu⟩ := ih t (by omega)
      obtain ⟨hl', hu'⟩ := ih (t + 1) ht
      have hbase := by simpa only [one_mul] using hodd 1 t one_pos
      rw [hodd 2 t (by decide), hodd 3 t (by decide), hbase, hl, hu, hl', hu', pow_succ']
      omega

private theorem dcDNodes_two_pow (k : ℕ) : dcDNodes (2 ^ k) = 0 := by
  induction k with
  | zero => simpa using dcDNodes_one
  | succ k ih => rw [pow_succ', dcDNodes_two_mul (Nat.two_pow_pos k), ih, mul_zero]

private theorem hasSum_takagi_of_lt (k r : ℕ) (hr : r < 2 ^ k) :
    HasSum (fun i : ℕ ↦ (takagiEll r ((k : ℤ) - 1) (i + 1) : ℝ) / 2 ^ (i + 1))
      ((dcDNodes (2 ^ k + r) : ℝ) / 2 ^ k) := by
  induction k generalizing r with
  | zero =>
    have hr' : r = 0 := by simpa using hr
    subst r
    have hbit (i : ℕ) : takagiBit 0 (-1 - (i : ℤ)) = 0 := takagiBit_neg _ _ (by omega)
    simp [takagiEll_succ, hbit, dcDNodes_one]
  | succ k ih =>
    let b := r / 2 ^ k
    let s := r % 2 ^ k
    have hs : s < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have hb : b < 2 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)).2 (by simpa [pow_succ'] using hr)
    have hr' : 2 ^ k * b + s = r := Nat.div_add_mod r _
    have h := hasSum_takagi_prepend k s b hs hb (ih s hs)
    rw [← hr', show ((k + 1 : ℕ) : ℤ) - 1 = k by omega]
    convert h using 1
    obtain ⟨hl, hu⟩ := dcDNodes_leading_digit k s hs.le
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hb) with h | h
    · rw [h, ite_eq_left rfl, mul_zero, zero_add, pow_succ', pow_succ', hl, Nat.cast_add, ← add_div]
      rw [div_div, mul_comm (2 : ℝ)]
    · rw [h, ite_eq_right one_ne_zero, mul_one, pow_succ', pow_succ',
        show 2 * 2 ^ k + (2 ^ k + s) = 3 * 2 ^ k + s by omega, hu,
        Nat.cast_add, Nat.cast_sub hs.le, Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- **The Takagi function at dyadic rationals counts D-nodes (Coronado et al.).** Let $k$ and $r$
be natural numbers with $r \le 2^k$. Write $\tau(r / 2^k)$ for the Takagi value of the dyadic
presentation $r / 2^k$, and $\delta(n)$ for the number of $D$-nodes of the divide-and-conquer
tree on $n$ leaves, given by $\delta(1) = 0$, $\delta(2m) = 2 \delta(m)$ and
$\delta(2m + 1) = \delta(m) + \delta(m + 1) + 1$ for $m \ge 1$. Then
$\tau(r / 2^k) = \delta(2^k + r) / 2^k$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 8 (`jis-2024-24.2.7-thm-8`). -/
public theorem takagi_dyadic_eq_dcDNodes_div (k r : ℕ) (hr : r ≤ 2 ^ k) :
    takagiNewdef r ((k : ℤ) - 1) = (dcDNodes (2 ^ k + r) : ℝ) / 2 ^ k := by
  rw [takagiNewdef_eq]
  rcases hr.eq_or_lt with rfl | hr
  · have hbit (i : ℕ) : takagiBit (2 ^ k) ((k : ℤ) - 1 - (i : ℤ)) = 0 := by
      by_cases h : 0 ≤ (k : ℤ) - 1 - (i : ℤ)
      · rw [takagiBit_eq, ite_eq_left h, Nat.testBit_two_pow_of_ne (by omega)]
        rfl
      · exact takagiBit_neg _ _ (lt_of_not_ge h)
    rw [← two_mul (2 ^ k), ← pow_succ']
    simp [takagiEll_succ, hbit, dcDNodes_two_pow]
  · exact (hasSum_takagi_of_lt k r hr).tsum_eq

end MetaMathlibExt
