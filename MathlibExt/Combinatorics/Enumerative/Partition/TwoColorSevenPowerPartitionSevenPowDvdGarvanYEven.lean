/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.TwoColorSevenPowerPartition
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# 7-adic bounds for the vectors $y^{(2k)}_beta$

This module proves the lower bounds on the powers of seven dividing the entries of the
coefficient vectors for even powers of seven, built from Garvan's vectors and matrix.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 5 (`integers-2026-A94-lem-5`).
-/

namespace MetaMathlibExt

@[expose] public section

namespace seven_pow_dvd_garvanYEven

private theorem recurrence (k b j : ℕ) :
    garvanYEven k (b + 2) j = ∑ i ∈ Finset.Icc 1 (7 ^ (2 * k + b - 1)),
      garvanYEven k (b + 1) i *
      (if (b + 1) % 2 = 1 then garvanM (4 * i) (i + j) else garvanM (4 * i + 2) (i + j)) := by
  rw [garvanYEven]

private theorem pow_dvd_mul {a b e x y : ℕ} (hx : 7 ^ a ∣ x) (hy : 7 ^ b ∣ y)
    (he : e ≤ a + b) : 7 ^ e ∣ x * y := by
  apply dvd_trans (pow_dvd_pow 7 he)
  rw [pow_add]
  exact mul_dvd_mul hx hy

private theorem base_one (j : ℕ) :
    7 ^ (1 + (7 * j - 7) / 4) ∣ garvanYEven 1 1 j := by
  rw [garvanYEven_one, show 2 * 1 - 1 = 1 by decide, garvanX]
  rcases eq_or_ne j 1 with rfl | h₁
  · decide
  rcases eq_or_ne j 2 with rfl | h₂
  · decide
  simp [h₁, h₂]

private theorem base (k : ℕ) (hk : 1 ≤ k) (j : ℕ) (hj : 1 ≤ j) :
    7 ^ (k + (7 * j - 7) / 4) ∣ garvanYEven k 1 j := by
  rw [garvanYEven_one]
  rcases eq_or_ne k 1 with rfl | hk1
  · exact base_one j
  have hk2 : 1 ≤ k - 1 := by omega
  have heq : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  rw [heq]
  apply dvd_trans (pow_dvd_pow 7 (by omega : k + (7 * j - 7) / 4 ≤ (k - 1) + 1 + (7 * j - 4) / 4))
  exact (seven_pow_dvd_garvanX (k - 1) j hk2 hj).2.2.1

private theorem stepB (k β : ℕ)
    (hA : ∀ i, 1 ≤ i → 7 ^ (k + β + (7 * i - 7) / 4) ∣ garvanYEven k (2 * β + 1) i)
    (j : ℕ) (hj : 1 ≤ j) :
    7 ^ (k + β + 1 + (7 * j - 7) / 4) ∣ garvanYEven k (2 * β + 2) j := by
  rw [show 2 * β + 2 = (2 * β) + 2 by omega, recurrence]
  apply Finset.dvd_sum
  intro i hi
  rw [ite_eq_left (by omega : (2 * β + 1) % 2 = 1)]
  have hi₁ := (Finset.mem_Icc.mp hi).1
  apply pow_dvd_mul (hA i hi₁) (seven_pow_dvd_garvanM i j hi₁ hj).2.1
  rcases eq_or_lt_of_le hi₁ with rfl | hi₂ <;> omega

private theorem stepA (k β : ℕ)
    (hB : ∀ i, 1 ≤ i → 7 ^ (k + β + 1 + (7 * i - 7) / 4) ∣ garvanYEven k (2 * β + 2) i)
    (j : ℕ) (hj : 1 ≤ j) :
    7 ^ (k + (β + 1) + (7 * j - 7) / 4) ∣ garvanYEven k (2 * (β + 1) + 1) j := by
  rw [show 2 * (β + 1) + 1 = (2 * β + 1) + 2 by omega, recurrence]
  apply Finset.dvd_sum
  intro i hi
  rw [ite_eq_right (by omega : (2 * β + 2) % 2 ≠ 1)]
  have hi₁ := (Finset.mem_Icc.mp hi).1
  apply pow_dvd_mul (hB i hi₁) (seven_pow_dvd_garvanM i j hi₁ hj).2.2.2
  rcases eq_or_lt_of_le hi₁ with rfl | hi₂ <;> omega

private theorem both (k : ℕ) (hk : 1 ≤ k) : ∀ β,
    (∀ j, 1 ≤ j → 7 ^ (k + β + (7 * j - 7) / 4) ∣ garvanYEven k (2 * β + 1) j) ∧
    (∀ j, 1 ≤ j → 7 ^ (k + β + 1 + (7 * j - 7) / 4) ∣ garvanYEven k (2 * β + 2) j) := by
  intro β
  induction β with
  | zero =>
    constructor
    · intro j hj
      exact base k hk j hj
    · intro j hj
      exact stepB k 0 (base k hk) j hj
  | succ β ih =>
    obtain ⟨ihA, ihB⟩ := ih
    have nextA : ∀ j, 1 ≤ j →
        7 ^ (k + (β + 1) + (7 * j - 7) / 4) ∣ garvanYEven k (2 * (β + 1) + 1) j :=
      fun j hj => stepA k β ihB j hj
    have nextB : ∀ j, 1 ≤ j →
        7 ^ (k + (β + 1) + 1 + (7 * j - 7) / 4) ∣ garvanYEven k (2 * (β + 1) + 2) j :=
      fun j hj => stepB k (β + 1) nextA j hj
    exact ⟨nextA, nextB⟩

end seven_pow_dvd_garvanYEven

/-- **7-adic bounds for the vectors $y^{(2k)}_\beta$.** Let $y^{(2k)}_\beta$ be the coefficient
vectors for even powers of $7$, built from Garvan's vectors and matrix. For all $k, j \ge 1$ and
$\beta \ge 0$, $7^{k + \beta + \lfloor (7j-7)/4 \rfloor}$ divides $y^{(2k)}_{2\beta+1,j}$ and
$7^{k + \beta + 1 + \lfloor (7j-7)/4 \rfloor}$ divides $y^{(2k)}_{2\beta+2,j}$.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 5 (`integers-2026-A94-lem-5`). -/
public theorem seven_pow_dvd_garvanYEven (k β j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    7 ^ (k + β + (7 * j - 7) / 4) ∣ garvanYEven k (2 * β + 1) j ∧
      7 ^ (k + β + 1 + (7 * j - 7) / 4) ∣ garvanYEven k (2 * β + 2) j := by
  obtain ⟨hA, hB⟩ := seven_pow_dvd_garvanYEven.both k hk β
  exact ⟨hA j hj, hB j hj⟩

end

end MetaMathlibExt
