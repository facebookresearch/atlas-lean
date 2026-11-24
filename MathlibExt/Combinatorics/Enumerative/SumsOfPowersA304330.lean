/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted binomial sums and the A304330 array

The sums in Cereceda's Lemmas 4 and 7 telescope by Pascal's identity and the
absorption identity for binomial coefficients. A recurrence for the A304330 array
and a vanishing finite difference give Cereceda's alternating sum in Proposition 15.

Cereceda's closed form for the array in Corollary 6 comes from exponential generating
functions: the coefficient of `X ^ (2k)` in `(exp X + exp (-X) - 2) ^ m` is
`2 R(k, m) / (2k)!`, and the multinomial theorem expands the same power of the truncation
`∑_{r=1}^{k} X ^ (2r) / (2r)!` of `cosh X - 1`.
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

-- The centered difference over `0 ≤ j ≤ 2m` is twice `R(k, m)`. The two halves agree by
-- reflection, and the central term vanishes for positive degree.
private theorem sum_range_two_mul_add_one_eq_two_mul_arrayR {k : ℕ} (hk : 0 < k) (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m + 1),
        (-1 : ℤ) ^ j * (Nat.choose (2 * m) j : ℤ) * ((m : ℤ) - j) ^ (2 * k) =
      2 * arrayR k m := by
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
  have tail : ∑ j ∈ Finset.range m, f (m + 1 + j) = ∑ j ∈ Finset.range m, f j := by
    rw [← Finset.sum_range_reflect f m]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hj' := Finset.mem_range.mp hj
    simpa only [show 2 * m - (m + 1 + j) = m - 1 - j by omega] using
      (reflect (m + 1 + j) (by omega)).symm
  have center : f m = 0 := by simp [f, zero_pow (by omega : 2 * k ≠ 0)]
  change ∑ j ∈ Finset.range (2 * m + 1), f j = 2 * ∑ j ∈ Finset.range (m + 1), f j
  rw [show 2 * m + 1 = (m + 1) + m by omega, Finset.sum_range_add, tail,
    Finset.sum_range_succ f m, center]
  ring

-- When the order exceeds the degree, the centered difference vanishes, and so does its half.
private theorem arrayR_eq_zero_of_lt {k m : ℕ} (hk : 0 < k) (hkm : k < m) :
    arrayR k m = 0 := by
  have sign (j : ℕ) (hj : j ≤ 2 * m) : (-1 : ℤ) ^ (2 * m - j) = (-1) ^ j := by
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  have hd := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ)
    (show 2 * k < 2 * m by omega)) (-(m : ℤ))
  rw [fwdDiff_iter_eq_sum_shift] at hd
  have full : 2 * arrayR k m = 0 := by
    rw [← sum_range_two_mul_add_one_eq_two_mul_arrayR hk m]
    refine (Finset.sum_congr rfl fun j hj ↦ ?_).trans hd
    rw [sign j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)), nsmul_one, zsmul_eq_mul,
      show -(m : ℤ) + j = -((m : ℤ) - j) by ring, (even_two_mul k).neg_pow, Int.cast_id]
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

section ClosedForm

open PowerSeries

-- `exp X + exp (-X) - 2 = exp (-X) (exp X - 1) ^ 2`, expanded by the binomial theorem.
private theorem pow_exp_add_rescale_neg_one_sub_two (m : ℕ) :
    (exp ℚ + rescale (-1) (exp ℚ) - 2) ^ m =
      ∑ j ∈ Finset.range (2 * m + 1),
        C ((-1 : ℚ) ^ j * ((2 * m).choose j : ℚ)) * rescale ((j : ℚ) - m) (exp ℚ) := by
  have h1 : rescale (-1 : ℚ) (exp ℚ) * exp ℚ = 1 := by
    simpa using exp_mul_exp_eq_exp_add (A := ℚ) (-1) 1
  have hD : exp ℚ + rescale (-1) (exp ℚ) - 2 = rescale (-1 : ℚ) (exp ℚ) * (exp ℚ - 1) ^ 2 := by
    linear_combination (2 - exp ℚ) * h1
  rw [hD, mul_pow, ← pow_mul, sub_pow, ← map_pow, exp_pow_eq_rescale_exp, rescale_rescale,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [exp_pow_eq_rescale_exp, one_pow, mul_one]
  have hsign : (-1 : ℚ⟦X⟧) ^ (j + 2 * m) = C ((-1 : ℚ) ^ j) := by
    rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one, map_pow, map_neg, map_one]
  have hexp : rescale ((m : ℚ) * -1) (exp ℚ) * rescale (j : ℚ) (exp ℚ) =
      rescale ((j : ℚ) - m) (exp ℚ) := by
    rw [exp_mul_exp_eq_exp_add, show (m : ℚ) * -1 + j = j - m by ring]
  rw [hsign, ← map_natCast (C (R := ℚ)) ((2 * m).choose j), map_mul, ← hexp]
  ring

-- The coefficient of `X ^ (2k)` in `(exp X + exp (-X) - 2) ^ m` is `2 R(k, m) / (2k)!`.
private theorem coeff_pow_exp_add_rescale_neg_one_sub_two {k : ℕ} (hk : 0 < k) (m : ℕ) :
    coeff (2 * k) ((exp ℚ + rescale (-1) (exp ℚ) - 2) ^ m) =
      2 * (arrayR k m : ℚ) / ((2 * k).factorial : ℚ) := by
  have h := congrArg (Int.cast : ℤ → ℚ) (sum_range_two_mul_add_one_eq_two_mul_arrayR hk m)
  push_cast at h
  rw [pow_exp_add_rescale_neg_one_sub_two, map_sum, ← h, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [coeff_C_mul, coeff_rescale, coeff_exp, ← neg_sub, (even_two_mul k).neg_pow]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

-- The truncation `∑_{r=1}^{k} X ^ (2r) / (2r)!` of `cosh X - 1`.
private noncomputable def coshSubOneTrunc (k : ℕ) : ℚ⟦X⟧ :=
  ∑ r : Fin k, C (1 / ((2 * (r.val + 1)).factorial : ℚ)) * X ^ (2 * (r.val + 1))

-- `exp X + exp (-X) - 2 = 2 (cosh X - 1)` agrees with twice the truncation below `X ^ (2k+2)`.
private theorem X_pow_dvd_sub_coshSubOneTrunc (k : ℕ) :
    (X : ℚ⟦X⟧) ^ (2 * k + 2) ∣
      (exp ℚ + rescale (-1) (exp ℚ) - 2) - C 2 * coshSubOneTrunc k := by
  rw [X_pow_dvd_iff]
  intro n hn
  rw [coshSubOneTrunc, Finset.mul_sum, ← map_ofNat (C (R := ℚ)) 2]
  simp only [← mul_assoc, ← map_mul, map_sub, map_add, map_sum, coeff_C_mul_X_pow, coeff_C,
    coeff_rescale, coeff_exp, Algebra.algebraMap_self, RingHom.id_apply]
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · rcases t with _ | s
    · rw [Finset.sum_eq_zero fun r _ ↦ ite_eq_right (by omega)]
      norm_num
    · have hs : s < k := by omega
      rw [Finset.sum_eq_single ⟨s, hs⟩
          (fun r _ hr ↦ ite_eq_right fun h ↦ hr (Fin.ext (by dsimp only; omega)))
          (fun h ↦ absurd (Finset.mem_univ _) h),
        ite_eq_left rfl, ite_eq_right (by omega), pow_mul, Fin.val_mk]
      ring
  · rw [Finset.sum_eq_zero fun r _ ↦ ite_eq_right (by omega), ite_eq_right (by omega), pow_succ,
      pow_mul]
    ring

private theorem coeff_pow_eq_two_pow_mul_coeff_coshSubOneTrunc_pow (k m : ℕ) :
    coeff (2 * k) ((exp ℚ + rescale (-1) (exp ℚ) - 2) ^ m) =
      2 ^ m * coeff (2 * k) (coshSubOneTrunc k ^ m) := by
  have h := (X_pow_dvd_sub_coshSubOneTrunc k).trans (sub_dvd_pow_sub_pow _ _ m)
  rw [X_pow_dvd_iff] at h
  have h2 := h (2 * k) (by omega)
  rwa [map_sub, sub_eq_zero, mul_pow, ← map_pow, coeff_C_mul] at h2

-- The multinomial theorem extracts the coefficient of `X ^ (2k)`.
private theorem coeff_coshSubOneTrunc_pow (k m : ℕ) :
    coeff (2 * k) (coshSubOneTrunc k ^ m) =
      ∑ b ∈ (Finset.univ.piAntidiag m).filter
          (fun b : Fin k → ℕ ↦ ∑ r, (r.val + 1) * b r = k),
        (Nat.multinomial Finset.univ b : ℚ) *
          ∏ r, (1 / ((2 * (r.val + 1)).factorial : ℚ)) ^ b r := by
  rw [coshSubOneTrunc, Finset.sum_pow_eq_sum_piAntidiag, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  simp_rw [mul_pow, ← map_pow, ← pow_mul, Finset.prod_mul_distrib, ← map_prod,
    Finset.prod_pow_eq_pow_sum, coeff_natCast_mul, coeff_C_mul_X_pow]
  have hsum : (∑ r : Fin k, 2 * (r.val + 1) * b r) = 2 * ∑ r : Fin k, (r.val + 1) * b r := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ ↦ by ring
  rw [hsum]
  by_cases hb : ∑ r : Fin k, (r.val + 1) * b r = k
  · rw [ite_eq_left hb, ite_eq_left (by omega)]
  · rw [ite_eq_right hb, ite_eq_right (by omega), mul_zero]

end ClosedForm

/-- **Closed form for the array $R(k, m)$.** Let $k$ and $m$ be natural numbers with
$1 \le m \le k$, and let $R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then
$$R(k, m) = 2^{2k+m-1}\, m! \sum_{b} \frac{(2k)!}{b_1! \cdots b_k!}
\prod_{r=1}^{k} \left(\frac{1}{4^r (2r)!}\right)^{b_r},$$
where the sum runs over all $k$-tuples $b = (b_1, \dots, b_k)$ of natural numbers with
$b_1 + 2 b_2 + \dots + k b_k = k$ and $b_1 + \dots + b_k = m$ (each such $b_r$ is at most $k$).

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Corollary 6. -/
theorem arrayR_eq_closedForm (k m : ℕ) (hm1 : 1 ≤ m)
    (hmk : m ≤ k) :
    (arrayR k m : ℚ) =
      (2 : ℚ) ^ (2 * k + m - 1) * (Nat.factorial m : ℚ) *
        ∑ b ∈ Finset.univ.filter
            (fun b : Fin k → Fin (k + 1) =>
              (∑ r : Fin k, (r.val + 1) * (b r).val) = k ∧
              (∑ r : Fin k, (b r).val) = m),
          ((Nat.factorial (2 * k) : ℚ) /
            ∏ r : Fin k, (Nat.factorial (b r).val : ℚ)) *
            ∏ r : Fin k,
              (1 / ((4 : ℚ) ^ (r.val + 1) *
                (Nat.factorial (2 * (r.val + 1)) : ℚ))) ^ ((b r).val) := by
  have hR : (arrayR k m : ℚ) =
      ((2 * k).factorial : ℚ) / 2 * 2 ^ m * PowerSeries.coeff (2 * k) (coshSubOneTrunc k ^ m) := by
    have h := coeff_pow_exp_add_rescale_neg_one_sub_two (by omega : 0 < k) m
    rw [coeff_pow_eq_two_pow_mul_coeff_coshSubOneTrunc_pow] at h
    rw [mul_assoc, h]
    field_simp
  have hpow : (2 : ℚ) ^ (2 * k + m - 1) * 2 = 4 ^ k * 2 ^ m := by
    rw [← pow_succ, show 2 * k + m - 1 + 1 = 2 * k + m by omega, pow_add, pow_mul]
    norm_num
  -- Entries of a tuple with sum `m ≤ k` are below `k + 1`.
  have hmod : ∀ a ∈ (Finset.univ : Finset (Fin k)).piAntidiag m, ∀ r, a r % (k + 1) = a r := by
    intro a ha r
    have : a r ≤ m := (Finset.mem_piAntidiag.mp ha).1 ▸
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ r)
    exact Nat.mod_eq_of_lt (by omega)
  rw [hR, coeff_coshSubOneTrunc_pow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_nbij' (fun b r ↦ ⟨b r % (k + 1), Nat.mod_lt _ k.succ_pos⟩)
    (fun b r ↦ (b r).val) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmod a ha1]
    exact ⟨ha2, (Finset.mem_piAntidiag.mp ha1).1⟩
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_piAntidiag.mpr ⟨ha.2, fun r _ ↦ Finset.mem_univ r⟩, ha.1⟩
  · intro a ha
    funext r
    exact hmod a (Finset.mem_filter.mp ha).1 r
  · intro a _
    funext r
    exact Fin.ext (Nat.mod_eq_of_lt (a r).isLt)
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    simp only [hmod a ha1]
    have hmult := Nat.multinomial_spec Finset.univ a
    rw [(Finset.mem_piAntidiag.mp ha1).1] at hmult
    have hmult' : (∏ r, ((a r).factorial : ℚ)) * (Nat.multinomial Finset.univ a : ℚ) =
        (m.factorial : ℚ) := by
      exact_mod_cast hmult
    have hprod : (∏ r : Fin k, (1 / ((4 : ℚ) ^ (r.val + 1) *
        ((2 * (r.val + 1)).factorial : ℚ))) ^ a r) * 4 ^ k =
        ∏ r : Fin k, (1 / ((2 * (r.val + 1)).factorial : ℚ)) ^ a r := by
      rw [show (4 : ℚ) ^ k = 4 ^ (∑ r : Fin k, (r.val + 1) * a r) by rw [ha2],
        ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ ↦ ?_
      rw [pow_mul, ← mul_pow]
      congr 1
      field_simp
    have hQ : (∏ r, ((a r).factorial : ℚ)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun r _ ↦ by positivity
    rw [← hprod, ← hmult', (eq_div_iff two_ne_zero).mpr hpow]
    field_simp

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
