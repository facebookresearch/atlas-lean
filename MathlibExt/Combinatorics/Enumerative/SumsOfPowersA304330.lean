/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted binomial sums and the A304330 array

The sums in Cereceda's Lemmas 4 and 7 telescope by Pascal's identity and the
absorption identity for binomial coefficients. A recurrence for the A304330 array
and a vanishing finite difference give Cereceda's alternating sum in Proposition 15.
-/

public section

namespace MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted

/-- **Sum of $2i \binom{2i+k-1}{2k-1}$.** For all natural numbers $k \ge 1$ and $n \ge 1$,
$$\sum_{i=1}^{n} 2i \binom{2i + k - 1}{2k - 1} = k \binom{2n + k + 1}{2k + 1}.$$

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 4. -/
theorem sum_two_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (2 * i) * Nat.choose (2 * i + k - 1) (2 * k - 1)) =
      k * Nat.choose (2 * n + k + 1) (2 * k + 1) := by
  let F (i : ℕ) := k * (2 * i + k + 1).choose (2 * k + 1)
  have step (i : ℕ) :
      F i + 2 * (i + 1) * (2 * (i + 1) + k - 1).choose (2 * k - 1) = F (i + 1) := by
    dsimp only [F]
    set a := 2 * i + k + 1 with ha
    have htop : 2 * (i + 1) + k = a + 1 := by omega
    have hbot : 2 * k - 1 + 1 = 2 * k := by omega
    have pascal := Nat.choose_succ_succ' a (2 * k - 1)
    have absorb := Nat.add_one_mul_choose_eq a (2 * k - 1)
    rw [hbot] at pascal absorb
    -- Expand the binomial two rows above row a, then use absorption on row a.
    rw [htop, Nat.add_sub_cancel, Nat.choose_succ_succ' (a + 1) (2 * k),
      Nat.choose_succ_succ' a (2 * k), pascal]
    rw [pascal, ← htop] at absorb
    grind only
  induction n, hn using Nat.le_induction with
  | base =>
    simpa [F, Nat.choose_eq_zero_of_lt (show k + 1 < 2 * k + 1 by omega)] using step 0
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    exact step n

/-- **Sum of $i \binom{i+k-1}{2k-1}$.** For all natural numbers $k \ge 1$ and $n \ge 1$,
$$\sum_{i=1}^{n} i \binom{i + k - 1}{2k - 1} = \frac{k(2n + 1)}{2k + 1} \binom{n + k}{2k}.$$

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 7. -/
theorem sum_mul_choose_eq (k n : ℕ) (hk : 1 ≤ k)
    (hn : 1 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n,
      (i : ℚ) * (Nat.choose (i + k - 1) (2 * k - 1) : ℚ)) =
      ((k : ℚ) * (2 * (n : ℚ) + 1) / (2 * (k : ℚ) + 1)) *
        (Nat.choose (n + k) (2 * k) : ℚ) := by
  let F (i : ℕ) : ℚ := (k : ℚ) * (2 * i - 1) / (2 * k + 1) *
    ((i + k - 1).choose (2 * k) : ℚ)
  have hbot : 2 * k - 1 + 1 = 2 * k := by omega
  have step (i : ℕ) :
      (i : ℚ) * ((i + k - 1).choose (2 * k - 1) : ℚ) = F (i + 1) - F i := by
    have htop : i + k - 1 + 1 = i + k := by omega
    have pascal := Nat.choose_succ_succ' (i + k - 1) (2 * k - 1)
    have absorb := Nat.add_one_mul_choose_eq (i + k - 1) (2 * k - 1)
    rw [htop, hbot] at pascal absorb
    apply_fun (Nat.cast : ℕ → ℚ) at pascal absorb
    push_cast at pascal absorb
    dsimp only [F]
    rw [show i + 1 + k - 1 = i + k by omega]
    push_cast
    field_simp
    linear_combination absorb - k * (2 * (i : ℚ) - 1) * pascal
  rw [Finset.sum_congr rfl (fun i _ ↦ step i), Finset.sum_Icc_sub hn]
  simp [F, show 2 * ((n : ℚ) + 1) - 1 = 2 * n + 1 by ring,
    Nat.choose_eq_zero_of_lt (show k < 2 * k by omega),
    show n + 1 + k - 1 = n + k by omega]

/-- **The array $R(k, m)$.** For natural numbers $k$ and $m$, $R(k, m)$ is the integer
$\sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. -/
@[expose] def arrayR (k m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℤ) ^ j * (Nat.choose (2 * m) j : ℤ) * ((m : ℤ) - j) ^ (2 * k)

-- Absorb two factors into the binomial coefficient to lower its top index by two.
private theorem choose_absorb_two (m j : ℕ) (hj : j ≤ 2 * m + 1) :
    ((2 * m + 2).choose (j + 1) : ℤ) * (j + 1) * (2 * m + 1 - j) =
      (2 * (m : ℤ) + 2) * (2 * m + 1) * (2 * m).choose j := by
  have ha := Nat.add_one_mul_choose_eq (2 * m + 1) j
  have hb := Nat.choose_mul_succ_eq (2 * m) j
  apply_fun (Nat.cast : ℕ → ℤ) at ha hb
  push_cast [Nat.cast_sub hj] at ha hb
  linear_combination -(2 * (m : ℤ) + 1 - j) * ha - (2 * (m : ℤ) + 2) * hb

-- Subtracting the square of the column index leaves a factor j * (2m + 2 - j).
private theorem arrayR_succ_sub (k m : ℕ) :
    arrayR (k + 1) (m + 1) - ((m : ℤ) + 1) ^ 2 * arrayR k (m + 1) =
      (2 * (m : ℤ) + 2) * (2 * m + 1) * arrayR k m := by
  simp only [arrayR, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, sub_zero, Nat.choose_zero_right, Nat.cast_one, pow_zero,
    one_mul, Nat.cast_add, show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
  rw [show ((m : ℤ) + 1) ^ (2 * k) * (m + 1) ^ 2 -
    (m + 1) ^ 2 * (m + 1) ^ (2 * k) = 0 by ring, add_zero]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' := Finset.mem_range.mp hj
  simp only [add_sub_add_right_eq_sub, pow_succ (-1 : ℤ),
    show 2 * (m + 1) = 2 * m + 2 by omega]
  linear_combination (-1 : ℤ) ^ j * ((m : ℤ) - j) ^ (2 * k) * choose_absorb_two m j (by omega)

-- When the order exceeds the degree, the centered difference vanishes. The two
-- halves agree by reflection, and the central term vanishes for positive degree.
private theorem arrayR_eq_zero_of_lt {k m : ℕ} (hk : 0 < k) (hkm : k < m) :
    arrayR k m = 0 := by
  let f (j : ℕ) := (-1 : ℤ) ^ j * (Nat.choose (2 * m) j : ℤ) * ((m : ℤ) - j) ^ (2 * k)
  have sign (j : ℕ) (hj : j ≤ 2 * m) : (-1 : ℤ) ^ (2 * m - j) = (-1) ^ j := by
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  have reflect (j : ℕ) (hj : j ≤ 2 * m) : f (2 * m - j) = f j := by
    dsimp only [f]
    rw [sign j hj, Nat.choose_symm hj, Nat.cast_sub hj]
    push_cast
    rw [show (m : ℤ) - (2 * m - j) = -((m : ℤ) - j) by ring, (even_two_mul k).neg_pow]
  have full : ∑ j ∈ Finset.range (2 * m + 1), f j = 0 := by
    have hd := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ)
      (show 2 * k < 2 * m by omega)) (-(m : ℤ))
    rw [fwdDiff_iter_eq_sum_shift] at hd
    refine (Finset.sum_congr rfl fun j hj ↦ ?_).trans hd
    dsimp only [f]
    rw [sign j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), nsmul_one, zsmul_eq_mul,
      show -(m : ℤ) + j = -((m : ℤ) - j) by ring, (even_two_mul k).neg_pow, Int.cast_id]
  rw [show 2 * m + 1 = (m + 1) + m by omega, Finset.sum_range_add] at full
  have tail : ∑ j ∈ Finset.range m, f (m + 1 + j) = ∑ j ∈ Finset.range m, f j := by
    rw [← Finset.sum_range_reflect f m]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    simpa only [show 2 * m - (m + 1 + j) = m - 1 - j by omega] using
      (reflect (m + 1 + j) (by omega)).symm
  have center : f m = 0 := by simp [f, zero_pow (by omega : 2 * k ≠ 0)]
  change ∑ j ∈ Finset.range (m + 1), f j = 0
  rw [tail, Finset.sum_range_succ, center, add_zero] at full
  rw [Finset.sum_range_succ, center, add_zero]
  omega

/-- **Vanishing alternating sum of the A304330 array.** For every natural number $k \ge 2$,
$$\sum_{m=1}^{k} (-1)^m \frac{((m-1)!)^2}{(2m)!} R(k, m) = 0,$$
where $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$ is the array of OEIS A304330.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 15. -/
theorem sum_neg_factorial_sq_div_arrayR_eq_zero (k : ℕ)
    (hk : 2 ≤ k) :
    (∑ m ∈ Finset.Icc 1 k,
      (-1 : ℚ) ^ m *
        ((Nat.factorial (m - 1) : ℚ) ^ 2 /
          (Nat.factorial (2 * m) : ℚ)) * (arrayR k m : ℚ)) = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  -- The weighted sum in row r + 1 telescopes to two boundary entries of row r.
  let F (m : ℕ) : ℚ := (-1 : ℚ) ^ m * (m.factorial : ℚ) ^ 2 /
    ((2 * m).factorial : ℚ) * (arrayR r m : ℚ)
  have step (m : ℕ) :
      (-1 : ℚ) ^ (m + 1) * ((m.factorial : ℚ) ^ 2 / ((2 * (m + 1)).factorial : ℚ)) *
        (arrayR (r + 1) (m + 1) : ℚ) = F (m + 1) - F m := by
    have h := arrayR_succ_sub r m
    apply_fun (Int.cast : ℤ → ℚ) at h
    push_cast at h
    simp only [F, show 2 * (m + 1) = 2 * m + 1 + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ (-1 : ℚ)]
    field_simp
    linear_combination -h
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  simp_rw [step]
  rw [Finset.sum_range_sub]
  dsimp only [F]
  rw [arrayR_eq_zero_of_lt (by omega : 0 < r) (by omega : r < r + 1)]
  simp [arrayR, zero_pow (by omega : 2 * r ≠ 0)]

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
