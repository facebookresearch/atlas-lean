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
public import MathlibExt.Combinatorics.Enumerative.JacobiStirlingFirstKind
public import MathlibExt.Combinatorics.Enumerative.LegendreStirlingFirstKind
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Cast.Lemmas
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

The recurrence for the normalized array `arrayU` and the signed Jacobi–Stirling recurrence
give the inverse sequence transformations in Cereceda's Lemma 5.

The odd power-sum formula follows by extracting coefficients from the finite geometric
sum in `exp (2X)`, expanded in powers of `exp X + exp (-X) - 2` after factoring out
`exp (nX)`.

The even power-sum formula in Theorem 1 follows by centering the geometric sum at zero
and taking its coefficient of degree `2k`. Opposite exponents contribute equally.

The proof of Knuth's formula (Proposition 3) takes first differences and expands the
resulting even power in the central factorial basis.

Cereceda's Proposition 12 gives the Faulhaber form of the even power sums for exponents
`2k` with `k ≥ 1` and `n : ℕ`. The even and odd Faulhaber expansions both use the
binomial expansion (20) in the signed Legendre–Stirling basis.

## References

* José L. Cereceda, *Sums of Powers of Integers and the Sequence A304330*,
  Journal of Integer Sequences 28 (2025), Article 25.1.3, pp. 1–21, especially Proposition 3,
  equation (5), Section 2.2, Proposition 12, and Proposition 15.
* G. E. Andrews, W. Gawronski, and L. L. Littlejohn, *The Legendre-Stirling numbers*,
  Discrete Mathematics 311 (2011), 1255–1272, Theorem 5.5.
* Haili Guo and Kelun Wang, *Some Properties of the Legendre-Stirling Numbers*,
  IOP Conference Series: Materials Science and Engineering 466 (2018), 012026,
  Theorem 2, equation (4).
* M. W. Coffey and M. C. Lettington, *On Fibonacci Polynomial Expressions for Sums of mth
  Powers, their implications for Faulhaber's Formula and some Theorems of Fermat*,
  arXiv:1510.05402 (2015), Equation (5.1).
* Donald E. Knuth, *Johann Faulhaber and Sums of Powers*, Mathematics of Computation
  61 (1993), 277–294, pp. 284–286.
* P. L. Butzer, M. Schmidt, E. L. Stark, and L. Vogt,
  *Central factorial numbers; their main properties and some applications*,
  Numerical Functional Analysis and Optimization 10 (1989), 419–488,
  Propositions 2.3 and 2.4(xiii).
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

/-- **The array $U(k, m)$.** For natural numbers $k$ and $m$, $U(k, m)$ is the rational number
$\frac{2}{(2m)!} \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. -/
@[expose] def arrayU (k m : ℕ) : ℚ :=
  (2 / (Nat.factorial (2 * m) : ℚ)) *
    ∑ j ∈ Finset.range (m + 1),
      (-1 : ℚ) ^ j * (Nat.choose (2 * m) j : ℚ) * ((m : ℚ) - j) ^ (2 * k)

section Inversion

open MetaMathlibExt

private theorem arrayU_eq_scaled_arrayR (k m : ℕ) :
    arrayU k m = (2 / ((2 * m).factorial : ℚ)) * (arrayR k m : ℚ) := by
  simp [arrayU, arrayR]

private theorem arrayU_succ (k m : ℕ) :
    arrayU (k + 1) (m + 1) = arrayU k m + ((m : ℚ) + 1) ^ 2 * arrayU k (m + 1) := by
  have h := congrArg (Int.cast : ℤ → ℚ) (arrayR_succ_sub k m)
  push_cast at h
  simp only [arrayU_eq_scaled_arrayR, show 2 * (m + 1) = 2 * m + 1 + 1 by omega,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  linear_combination h

private noncomputable abbrev firstEntry (k m : ℕ) : ℝ := jacobiStirlingFirst k m (0 : ℤ)
private abbrev secondEntry (k m : ℕ) : ℝ := arrayU k m

private noncomputable def transform (c : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 k, c k m * b m

-- A two-term row recurrence shifts the argument of the sequence transform.
private theorem transform_step (c : ℕ → ℕ → ℝ) (b w : ℕ → ℝ) (k : ℕ)
    (hzero : c k 0 = 0) (htop : c k (k + 1) = 0)
    (hrec : ∀ m, c (k + 1) (m + 1) = c k m + w (m + 1) * c k (m + 1)) :
    transform c b (k + 1) = transform c (fun m ↦ b (m + 1) + w m * b m) k := by
  simp only [transform, ← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel, Nat.add_comm 1, hrec, add_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ' (fun m ↦ c k m * b (m + 1)),
    Finset.sum_range_succ (fun m ↦ w (m + 1) * c k (m + 1) * b (m + 1))]
  simp only [hzero, htop, zero_mul, mul_zero, add_zero]
  congr 1
  exact Finset.sum_congr rfl fun m _ ↦ by ring

private theorem firstTransform_succ (b : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    transform firstEntry b (k + 1) =
      transform firstEntry (fun m ↦ b (m + 1)) k - (k : ℝ) ^ 2 * transform firstEntry b k := by
  have hzero : firstEntry k 0 = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    simp [firstEntry, jacobiStirlingFirst, jacobiStirlingFirstPoly, Finset.prod_range_succ',
      Polynomial.mul_coeff_zero]
  rw [transform_step firstEntry b (fun _ ↦ -(k : ℝ) ^ 2) k hzero
    (jacobiStirlingFirst_support k (k + 1) _ (Nat.lt_succ_self k)) (by
    intro m
    simp only [firstEntry, jacobiStirlingFirst_recurrence]
    ring)]
  simp only [transform, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ ↦ by ring

private theorem secondTransform_succ (a : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    transform secondEntry a (k + 1) =
      transform secondEntry (fun m ↦ a (m + 1) + (m : ℝ) ^ 2 * a m) k := by
  apply transform_step
  · simp [secondEntry, arrayU, zero_pow (by omega : 2 * k ≠ 0)]
  · simp [secondEntry, arrayU_eq_scaled_arrayR, arrayR_eq_zero_of_lt hk (Nat.lt_succ_self k)]
  · intro m
    simp [secondEntry, arrayU_succ, sq]

-- Composing the transforms cancels the square weight at each step.
private theorem first_second_cancel (a : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) :
    transform firstEntry (transform secondEntry a) k = a k := by
  induction k, hk using Nat.le_induction generalizing a with
  | base =>
    simp [transform, firstEntry, secondEntry, jacobiStirlingFirst_diagonal,
      show arrayU 1 1 = 1 by norm_num [arrayU, Finset.sum_range_succ, Nat.factorial]]
  | succ k hk ih =>
    rw [firstTransform_succ _ k hk, ih]
    let shifted (m : ℕ) := a (m + 1) + (m : ℝ) ^ 2 * a m
    have hshift : transform firstEntry (fun m ↦ transform secondEntry a (m + 1)) k =
        transform firstEntry (transform secondEntry shifted) k :=
      Finset.sum_congr rfl fun m hm ↦
        congrArg (firstEntry k m * ·) (secondTransform_succ a m (Finset.mem_Icc.mp hm).1)
    rw [hshift, ih]
    dsimp only [shifted]
    ring

/-- **Inversion formula for the arrays $u(k, m)$ and $U(k, m)$ (Butzer et al.).** For natural
numbers $k$ and $m$, let $u(k, m)$ be the first-kind Jacobi–Stirling number $J(k, m; 0)$, the
coefficient of $x^m$ in $\prod_{i=0}^{k-1} (x - i^2)$, and let
$U(k, m) = \frac{2}{(2m)!} \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. For all sequences
$(a_k)_{k \ge 0}$ and $(b_k)_{k \ge 0}$ of real numbers, $a_k = \sum_{m=1}^{k} u(k, m)\, b_m$
holds for every $k \ge 1$ if and only if $b_k = \sum_{m=1}^{k} U(k, m)\, a_m$ holds for every
$k \ge 1$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Lemma 5. -/
theorem inversion_uU (a b : ℕ → ℝ) :
    (∀ k : ℕ, 1 ≤ k → a k =
      ∑ m ∈ Finset.Icc 1 k, (MetaMathlibExt.jacobiStirlingFirst k m (0 : ℤ) : ℝ) * b m) ↔
    (∀ k : ℕ, 1 ≤ k → b k =
      ∑ m ∈ Finset.Icc 1 k, (arrayU k m : ℝ) * a m) := by
  change (∀ k, 1 ≤ k → a k = transform firstEntry b k) ↔
    (∀ k, 1 ≤ k → b k = transform secondEntry a k)
  constructor
  · intro h k hk
    -- The unit diagonal determines each new term from the terms already recovered.
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have eq := (h _ hk).symm.trans (first_second_cancel a _ hk).symm
      have split (c : ℕ → ℝ) : transform firstEntry c (r + 1) =
          (∑ m ∈ Finset.Icc 1 r, firstEntry (r + 1) m * c m) + c (r + 1) := by
        simp [transform, Finset.sum_Icc_succ_top hk, firstEntry, jacobiStirlingFirst_diagonal]
      have lower : (∑ m ∈ Finset.Icc 1 r, firstEntry (r + 1) m * b m) =
          ∑ m ∈ Finset.Icc 1 r, firstEntry (r + 1) m * transform secondEntry a m :=
        Finset.sum_congr rfl fun m hm ↦ by
          obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hm
          rw [ih m (by omega) hm₁]
      rw [split, split, lower] at eq
      exact add_left_cancel eq
  · intro h k hk
    rw [← first_second_cancel a k hk]
    exact Finset.sum_congr rfl fun m hm ↦ by rw [h m (Finset.mem_Icc.mp hm).1]

end Inversion

/-- **Power sums.** For natural numbers $k$ and $n$, the power sum $S_k(n)$ is the rational
number $\sum_{i=1}^{n} i^k = 1^k + 2^k + \cdots + n^k$, which is $0$ when $n = 0$. -/
@[expose] def powerSum (k n : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 n, (i : ℚ) ^ k

-- Multiplying the first difference of the binomial basis by `n + 1` gives the first
-- difference of the same basis with the endpoint weight `2n + 1` and the reciprocal scaling.
private theorem weighted_choose_sub (m n : ℕ) (hm : 1 ≤ m) :
    (2 * ((n + 1 : ℕ) : ℝ) + 1) * ((n + 1 + m).choose (2 * m) : ℝ) -
        (2 * (n : ℝ) + 1) * ((n + m).choose (2 * m) : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (((2 * (m : ℝ) + 1) / m) *
        (((n + 1 + m).choose (2 * m) : ℝ) - ((n + m).choose (2 * m) : ℝ))) := by
  have pascal := Nat.choose_succ_succ' (n + m) (2 * m - 1)
  rw [show 2 * m - 1 + 1 = 2 * m by omega, show n + m + 1 = n + 1 + m by omega] at pascal
  have hdiff : ((n + 1 + m).choose (2 * m) : ℝ) - ((n + m).choose (2 * m) : ℝ) =
      ((n + m).choose (2 * m - 1) : ℝ) := by
    rw [pascal, Nat.cast_add, add_sub_cancel_right]
  have hm₀ : (m : ℝ) ≠ 0 := by positivity
  have weighted (j : ℕ) : (2 * (j : ℝ) + 1) * ((j + m).choose (2 * m) : ℝ) =
      ((2 * (m : ℝ) + 1) / m) *
        ∑ i ∈ Finset.Icc 1 j, (i : ℝ) * ((i + m - 1).choose (2 * m - 1) : ℝ) := by
    cases j with
    | zero => simp [Nat.choose_eq_zero_of_lt (show m < 2 * m by omega)]
    | succ j =>
      have h := congrArg (fun q : ℚ ↦ (q : ℝ)) (sum_mul_choose_eq m (j + 1) hm (by omega))
      push_cast at h
      rw [h]
      field_simp
      push_cast
      ring
  rw [hdiff, weighted (n + 1), weighted n, Finset.sum_Icc_succ_top (Nat.succ_pos n),
    ← mul_sub, add_sub_cancel_left, show n + 1 + m - 1 = n + m by omega]
  ring

/-- **Knuth's correspondence between even and odd power sums.** Let $k \ge 1$ be a natural
number, let $(a_m)_{m \ge 0}$ be a sequence of real numbers, and write
$S_j(n) = 1^j + 2^j + \dots + n^j$. Then
$\frac{S_{2k}(n)}{2n+1} = \sum_{m=1}^{k} a_m \binom{n+m}{2m}$ for every natural number $n$
if and only if $S_{2k-1}(n) = \sum_{m=1}^{k} \frac{2m+1}{m}\, a_m \binom{n+m}{2m}$ for every
natural number $n$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 2. -/
theorem powerSum_even_div_iff_odd (k : ℕ) (hk : 1 ≤ k)
    (a : ℕ → ℝ) :
    (∀ n : ℕ, (powerSum (2 * k) n : ℝ) / (2 * (n : ℝ) + 1) =
      ∑ m ∈ Finset.Icc 1 k,
        a m * (Nat.choose (n + m) (2 * m) : ℝ)) ↔
    (∀ n : ℕ, (powerSum (2 * k - 1) n : ℝ) =
      ∑ m ∈ Finset.Icc 1 k,
        ((2 * (m : ℝ) + 1) / (m : ℝ)) * a m *
          (Nat.choose (n + m) (2 * m) : ℝ)) := by
  let expansion (c : ℕ → ℝ) (n : ℕ) : ℝ :=
    ∑ m ∈ Finset.Icc 1 k, c m * ((n + m).choose (2 * m) : ℝ)
  let b (m : ℕ) : ℝ := ((2 * (m : ℝ) + 1) / m) * a m
  let d (n : ℕ) : ℝ := 2 * (n : ℝ) + 1
  let even (n : ℕ) : ℝ := powerSum (2 * k) n
  let odd (n : ℕ) : ℝ := powerSum (2 * k - 1) n
  change (∀ n, even n / d n = expansion a n) ↔ ∀ n, odd n = expansion b n
  have normalize (n : ℕ) : even n / d n = expansion a n ↔
      even n = d n * expansion a n := by
    rw [div_eq_iff (show d n ≠ 0 by dsimp [d]; positivity), mul_comm (expansion a n)]
  simp_rw [normalize]
  have expansion_zero (c : ℕ → ℝ) : expansion c 0 = 0 := by
    refine Finset.sum_eq_zero fun m hm ↦ ?_
    have hm₁ := (Finset.mem_Icc.mp hm).1
    simp [Nat.choose_eq_zero_of_lt (show m < 2 * m by omega)]
  -- The candidate expansions and the power sums satisfy the same relation on differences.
  have expansion_step (n : ℕ) :
      d (n + 1) * expansion a (n + 1) - d n * expansion a n =
        ((n + 1 : ℕ) : ℝ) * (expansion b (n + 1) - expansion b n) := by
    simp only [expansion, b, d, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    linear_combination a m * weighted_choose_sub m n (Finset.mem_Icc.mp hm).1
  have powerSum_sub (j n : ℕ) :
      (powerSum j (n + 1) : ℝ) - (powerSum j n : ℝ) = ((n + 1 : ℕ) : ℝ) ^ j := by
    simp only [powerSum, Finset.sum_Icc_succ_top (Nat.succ_pos n), Rat.cast_add, Rat.cast_pow,
      Rat.cast_natCast, add_sub_cancel_left]
  have powerSum_step (n : ℕ) : even (n + 1) - even n =
      ((n + 1 : ℕ) : ℝ) * (odd (n + 1) - odd n) := by
    dsimp only [even, odd]
    rw [powerSum_sub, powerSum_sub, ← pow_succ', show 2 * k - 1 + 1 = 2 * k by omega]
  constructor
  · intro h n
    induction n with
    | zero => simp [odd, powerSum, expansion_zero]
    | succ n ih =>
      have hs := powerSum_step n
      rw [h (n + 1), h n] at hs
      have hd := mul_left_cancel₀ (show ((n + 1 : ℕ) : ℝ) ≠ 0 by positivity)
        (hs.symm.trans (expansion_step n))
      linear_combination hd + ih
  · intro h n
    induction n with
    | zero => simp [even, powerSum, expansion_zero]
    | succ n ih =>
      have hs := powerSum_step n
      rw [h (n + 1), h n] at hs
      linear_combination hs - expansion_step n + ih

section Knuth

-- The factorial-scaled binomial is the central-factorial product at a positive integer.
private theorem central_factorial_choose (n m : ℕ) :
    (∏ i ∈ Finset.range (m + 1), (((n : ℝ) + 1) ^ 2 - (i : ℝ) ^ 2)) =
      ((n : ℝ) + 1) * ((2 * m + 1).factorial : ℝ) *
        ((n + m + 1).choose (2 * m + 1) : ℝ) := by
  induction m with
  | zero => simp [Nat.choose_one_right]; ring
  | succ m ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : m < n
    · rw [Nat.cast_choose ℝ (by omega), Nat.cast_choose ℝ (by omega)]
      rw [show n + (m + 1) + 1 = n + m + 1 + 1 by omega,
        Nat.factorial_succ (n + m + 1),
        show n + m + 1 - (2 * m + 1) = n - m by omega,
        show n + m + 1 + 1 - (2 * (m + 1) + 1) = n - m - 1 by omega]
      rw [show n - m = n - m - 1 + 1 by omega, Nat.factorial_succ (n - m - 1)]
      push_cast [Nat.cast_sub (show m ≤ n by omega), Nat.cast_sub (show 1 ≤ n - m by omega)]
      have hnm : (m : ℝ) < n := by exact_mod_cast h
      field_simp [sub_ne_zero.mpr hnm.ne']
      ring
    · rw [Nat.choose_eq_zero_of_lt (show n + (m + 1) + 1 < 2 * (m + 1) + 1 by omega)]
      rcases eq_or_lt_of_le (show n ≤ m by omega) with rfl | hlt
      · simp
      · simp [Nat.choose_eq_zero_of_lt (show n + m + 1 < 2 * m + 1 by omega)]

-- Multiplication by x² shifts the product basis by one column, with a diagonal correction.
private theorem even_pow_eq_central_factorial (x : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    x ^ (2 * k) = transform secondEntry
      (fun m ↦ ∏ i ∈ Finset.range m, (x ^ 2 - (i : ℝ) ^ 2)) k := by
  let b (m : ℕ) := ∏ i ∈ Finset.range m, (x ^ 2 - (i : ℝ) ^ 2)
  change _ = transform secondEntry b k
  induction k, hk using Nat.le_induction with
  | base =>
    simp [transform, secondEntry, b,
      show arrayU 1 1 = 1 by norm_num [arrayU, Finset.sum_range_succ, Nat.factorial]]
  | succ k hk ih =>
    rw [secondTransform_succ _ k hk, show 2 * (k + 1) = 2 * k + 2 by omega, pow_add, ih]
    simp only [transform, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    dsimp only [b]
    rw [Finset.prod_range_succ]
    ring

private theorem even_pow_eq_choose_step (k n : ℕ) (hk : 1 ≤ k) :
    ((n : ℝ) + 1) ^ (2 * k) =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℝ) * (((n : ℝ) + 1) / m) * ((n + m).choose (2 * m - 1) : ℝ) := by
  rw [even_pow_eq_central_factorial _ k hk]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hm₁ := (Finset.mem_Icc.mp hm).1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  change (arrayU k (j + 1) : ℝ) *
    (∏ i ∈ Finset.range (j + 1), (((n : ℝ) + 1) ^ 2 - (i : ℝ) ^ 2)) =
    (arrayR k (j + 1) : ℝ) * (((n : ℝ) + 1) / ↑(j + 1 : ℕ)) *
      ((n + j + 1).choose (2 * (j + 1) - 1) : ℝ)
  rw [arrayU_eq_scaled_arrayR, central_factorial_choose n j,
    show 2 * (j + 1) - 1 = 2 * j + 1 by omega,
    show 2 * (j + 1) = 2 * j + 1 + 1 by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- **Knuth's formula for even power sums.** For natural numbers $k \ge 1$ and $n$, write
$S_{2k}(n) = 1^{2k} + 2^{2k} + \dots + n^{2k}$ and
$R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then
$S_{2k}(n) = \sum_{m=1}^{k} R(k, m)\, \frac{2n+1}{2m+1} \binom{n+m}{2m}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 3. -/
theorem powerSum_even_eq_sum (k : ℕ) (hk : 1 ≤ k) (n : ℕ) :
    powerSum (2 * k) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) * ((2 * (n : ℚ) + 1) / (2 * (m : ℚ) + 1)) *
          (Nat.choose (n + m) (2 * m) : ℚ) := by
  let F (j : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 k,
    (arrayR k m : ℝ) * ((2 * (j : ℝ) + 1) / (2 * (m : ℝ) + 1)) *
      ((j + m).choose (2 * m) : ℝ)
  have step (j : ℕ) : F (j + 1) - F j = ((j : ℝ) + 1) ^ (2 * k) := by
    rw [even_pow_eq_choose_step k j hk]
    simp only [F, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm ↦ ?_
    have hm₁ := (Finset.mem_Icc.mp hm).1
    have h := weighted_choose_sub m j hm₁
    have pascal := Nat.choose_succ_succ' (j + m) (2 * m - 1)
    rw [show 2 * m - 1 + 1 = 2 * m by omega, show j + m + 1 = j + 1 + m by omega] at pascal
    have hd : ((j + 1 + m).choose (2 * m) : ℝ) - ((j + m).choose (2 * m) : ℝ) =
        ((j + m).choose (2 * m - 1) : ℝ) := by rw [pascal, Nat.cast_add, add_sub_cancel_right]
    rw [hd, Nat.cast_succ] at h
    push_cast
    calc
      _ = ((arrayR k m : ℝ) / (2 * (m : ℝ) + 1)) *
          ((2 * ((j : ℝ) + 1) + 1) * ((j + 1 + m).choose (2 * m) : ℝ) -
            (2 * (j : ℝ) + 1) * ((j + m).choose (2 * m) : ℝ)) := by ring
      _ = _ := by
        rw [h]
        field_simp
  have eq (j : ℕ) : (powerSum (2 * k) j : ℝ) = F j := by
    induction j with
    | zero =>
      simp only [powerSum, Finset.Icc_eq_empty_of_lt (show (0 : ℕ) < 1 by omega),
        Finset.sum_empty, Rat.cast_zero, F]
      symm
      refine Finset.sum_eq_zero fun m hm ↦ ?_
      have hm₁ := (Finset.mem_Icc.mp hm).1
      simp [Nat.choose_eq_zero_of_lt (show m < 2 * m by omega)]
    | succ j ih =>
      have hsum : powerSum (2 * k) (j + 1) = powerSum (2 * k) j + ((j + 1 : ℕ) : ℚ) ^ (2 * k) := by
        simp only [powerSum, Finset.sum_Icc_succ_top (Nat.succ_pos j)]
      rw [hsum, Rat.cast_add, Rat.cast_pow, Rat.cast_natCast, Nat.cast_succ, ih]
      linear_combination -(step j)
  apply Rat.cast_injective (α := ℝ)
  push_cast
  exact eq n

end Knuth

/-- **The polynomials $Q_{k,m}$ of Theorem 10.** For natural numbers $k$, $m$ and $n$, write
$R(a, b) = \sum_{i=0}^{b} (-1)^i \binom{2b}{i} (b - i)^{2a}$ for the array of OEIS A304330.
The rational number $Q_{k,m}(n)$ is $n^{2k-1}$ if $m = 1$, and otherwise
$$Q_{k,m}(n) = 2 \sum_{j=m}^{k} \binom{2k-1}{2j-2} R(j-1, m-1) \, n^{2k-2j+1}.$$

Differences of natural numbers such as $2k - 1$ and $m - 1$ are truncated at $0$. -/
@[expose] def thmQ (k m n : ℕ) : ℚ :=
  if m = 1 then (n : ℚ) ^ (2 * k - 1)
  else 2 * ∑ j ∈ Finset.Icc m k,
    (Nat.choose (2 * k - 1) (2 * j - 2) : ℚ) *
      (arrayR (j - 1) (m - 1) : ℚ) * (n : ℚ) ^ (2 * k - 2 * j + 1)

section OddPowerSums

open PowerSeries Finset

private def binomialSum {A : Type*} [CommRing A] (d : A) (n : ℕ) : A :=
  ∑ m ∈ range (n + 1), ((n + m + 1).choose (2 * m + 1) : A) * d ^ m

-- Two applications of Pascal's identity give the recurrence in the endpoint n.
private theorem binomialSum_recurrence {A : Type*} [CommRing A] (d : A) (n : ℕ) :
    binomialSum d (n + 2) + binomialSum d n = (d + 2) * binomialSum d (n + 1) := by
  let c (i m : ℕ) : A := (i + m + 1).choose (2 * m + 1)
  have pad (i b : ℕ) (hi : i < b) :
      ∑ m ∈ range (b + 1), c i m * d ^ m = ∑ m ∈ range b, c i m * d ^ m := by
    rw [sum_range_succ]
    simp [c, Nat.choose_eq_zero_of_lt (show i + b + 1 < 2 * b + 1 by omega)]
  have row (m : ℕ) : c (n + 2) (m + 1) + c n (m + 1) =
      2 * c (n + 1) (m + 1) + c (n + 1) m := by
    dsimp only [c]
    set a := n + m + 2
    set b := 2 * m + 1
    have h := Nat.choose_succ_succ' (a + 1) (b + 1)
    have h' := Nat.choose_succ_succ' a b
    have h'' := Nat.choose_succ_succ' a (b + 1)
    have hr : (a + 2).choose (b + 2) + a.choose (b + 2) =
        2 * (a + 1).choose (b + 2) + a.choose b := by
      grind only
    have hc := congrArg (Nat.cast : ℕ → A) hr
    push_cast at hc
    simpa only [a, b, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm, Nat.reduceAdd] using hc
  change (∑ m ∈ range (n + 3), c (n + 2) m * d ^ m) +
    (∑ m ∈ range (n + 1), c n m * d ^ m) =
    (d + 2) * ∑ m ∈ range (n + 2), c (n + 1) m * d ^ m
  rw [add_mul, mul_sum, ← pad n (n + 1) (by omega), ← pad n (n + 2) (by omega),
    ← pad (n + 1) (n + 2) (by omega)]
  -- Remove the constant terms to align the columns shifted by multiplication by d.
  rw [sum_range_succ' (fun m ↦ c (n + 2) m * d ^ m),
    sum_range_succ' (fun m ↦ c n m * d ^ m),
    sum_range_succ' (fun m ↦ c (n + 1) m * d ^ m), mul_add, mul_sum]
  have hsum := sum_congr (s₁ := range (n + 2)) rfl fun m _ ↦
    congrArg (· * d ^ (m + 1)) (row m)
  simp only [add_mul, sum_add_distrib] at hsum
  simp only [pow_zero, mul_one]
  have hzero (i : ℕ) : c i 0 = (i : A) + 1 := by simp [c]
  simp_rw [hzero]
  push_cast
  simp_rw [pow_succ d] at hsum ⊢
  simp only [mul_comm, mul_left_comm, mul_assoc] at hsum ⊢
  linear_combination hsum

-- The geometric sum at z², centered by zⁿ, is a polynomial in z + z⁻¹ - 2.
private theorem geomSum_eq_binomialSum {A : Type*} [CommRing A] (z w : A) (hw : z * w = 1)
    (n : ℕ) : ∑ i ∈ range (n + 1), (z ^ 2) ^ i =
      z ^ n * binomialSum (z + w - 2) n := by
  let d := z + w - 2
  have hd : z * (d + 2) = 1 + z ^ 2 := by dsimp [d]; linear_combination hw
  change _ = z ^ n * binomialSum d n
  induction n using Nat.twoStepInduction with
  | zero => simp [binomialSum]
  | one =>
    simp [binomialSum, sum_range_succ, Nat.choose] at *
    linear_combination -hd
  | more n ih₀ ih₁ =>
    have hg : (∑ i ∈ range (n + 3), (z ^ 2) ^ i) =
        (1 + z ^ 2) * (∑ i ∈ range (n + 2), (z ^ 2) ^ i) -
          z ^ 2 * ∑ i ∈ range (n + 1), (z ^ 2) ^ i := by
      rw [sum_range_succ _ (n + 2), sum_range_succ _ (n + 1), pow_succ _ (n + 1)]
      ring
    rw [hg, ih₀, ih₁, ← hd]
    simp only [pow_succ z]
    linear_combination -(z ^ n * z ^ 2) * binomialSum_recurrence d n

private noncomputable abbrev centeredExp : ℚ⟦X⟧ := exp ℚ + rescale (-1) (exp ℚ) - 2

-- The nonzero coefficients of the m-th power have even degree at least 2m.
private theorem centeredExp_support (m r : ℕ) (hm : 0 < m)
    (hr : coeff r (centeredExp ^ m) ≠ 0) : ∃ j, r = 2 * j ∧ m ≤ j := by
  rcases Nat.even_or_odd' r with ⟨j, rfl | rfl⟩
  · refine ⟨j, rfl, ?_⟩
    by_contra! hj
    cases j with
    | zero =>
      have hc : constantCoeff centeredExp = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply]
        simp only [centeredExp, map_sub, map_add, coeff_rescale, pow_zero, one_mul, coeff_exp]
        norm_num [map_ofNat]
      exact hr (by simp [coeff_zero_eq_constantCoeff, hc, hm.ne'])
    | succ j =>
      exact hr (by rw [coeff_pow_exp_add_rescale_neg_one_sub_two (by omega) m,
        arrayR_eq_zero_of_lt (by omega) hj]; simp)
  · have hs : rescale (-1 : ℚ) centeredExp = centeredExp := by
      simp [centeredExp, rescale_rescale, map_ofNat, add_comm]
    have h := congrArg (coeff (2 * j + 1)) (congrArg (· ^ m) hs)
    rw [← map_pow, coeff_rescale, pow_succ, pow_mul, neg_one_sq, one_pow] at h
    exact (hr (by linarith)).elim

-- Extract the odd coefficient after translating the centered exponential by n.
private theorem factorial_mul_coeff_centeredExp (k m n : ℕ) (hk : 1 ≤ k) :
    ((2 * k - 1).factorial : ℚ) * coeff (2 * k - 1) (centeredExp ^ m * exp ℚ ^ n) =
      thmQ k (m + 1) n := by
  rw [exp_pow_eq_rescale_exp]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [thmQ, coeff_exp, Algebra.algebraMap_self]
    field_simp
  rw [thmQ, ite_eq_right (by omega), coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [mul_sum, Nat.add_sub_cancel]
  symm
  apply sum_of_injOn (fun j ↦ 2 * j - 2)
  · intro i hi j hj hij
    simp only [SetLike.mem_coe, mem_Icc] at hi hj
    dsimp only at hij
    omega
  · intro j hj
    simp only [SetLike.mem_coe, mem_Icc, mem_range] at hj ⊢
    omega
  · intro r hr hmiss
    suffices coeff r (centeredExp ^ m) = 0 by simp [this]
    by_contra h
    obtain ⟨j, rfl, hj⟩ := centeredExp_support m r hm h
    apply hmiss
    have hr' := mem_range.mp hr
    refine ⟨j + 1, mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩
    dsimp only
    omega
  · intro j hj
    obtain ⟨h₁, h₂⟩ := mem_Icc.mp hj
    have hdeg : 2 * j - 2 = 2 * (j - 1) := by omega
    have hsub : 2 * k - 1 - (2 * j - 2) = 2 * k - 2 * j + 1 := by omega
    rw [Nat.cast_choose ℚ (by omega), hsub, hdeg,
      coeff_pow_exp_add_rescale_neg_one_sub_two (by omega) m, coeff_rescale, coeff_exp]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    ring

-- The binomial factor vanishes after column n, and the polynomial after column k - 1.
private theorem sum_thmQ_change_bound (k n : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ range (n + 1), thmQ k (m + 1) n * ((n + m + 1).choose (2 * m + 1) : ℚ)) =
      ∑ m ∈ range k, thmQ k (m + 1) n * ((n + m + 1).choose (2 * m + 1) : ℚ) := by
  rcases le_total (n + 1) k with h | h
  · apply sum_subset (range_mono h)
    intro m _ hm
    rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hm; omega)]
    simp
  · symm
    apply sum_subset (range_mono h)
    intro m _ hm
    have hmk : k < m + 1 := by simp only [mem_range] at hm; omega
    simp [thmQ, show m ≠ 0 by omega, Icc_eq_empty_of_lt hmk]

/-- **Odd power sums in terms of $\binom{n+m}{2m-1}$.** For natural numbers $k \ge 1$ and $n$,
write $S_{2k-1}(n) = 1^{2k-1} + 2^{2k-1} + \dots + n^{2k-1}$, let
$R(p, q) = \sum_{j=0}^{q} (-1)^j \binom{2q}{j} (q - j)^{2p}$, and let $Q_{k,1}(n) = n^{2k-1}$ and
$Q_{k,m}(n) = 2 \sum_{j=m}^{k} \binom{2k-1}{2j-2} R(j-1, m-1)\, n^{2k-2j+1}$ for $m \ge 2$. Then
$2^{2k-1} S_{2k-1}(n) = \sum_{m=1}^{k} Q_{k,m}(n) \binom{n+m}{2m-1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Theorem 10. -/
theorem pow_mul_powerSum_odd_eq_sum (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    (2 : ℚ) ^ (2 * k - 1) * powerSum (2 * k - 1) n =
      ∑ m ∈ Finset.Icc 1 k,
        thmQ k m n * (Nat.choose (n + m) (2 * m - 1) : ℚ) := by
  let p := 2 * k - 1
  have hp : p ≠ 0 := by dsimp [p]; omega
  have hg := geomSum_eq_binomialSum (exp ℚ) (rescale (-1) (exp ℚ))
    (by simpa using exp_mul_exp_eq_exp_add (1 : ℚ) (-1)) n
  have h := congrArg (fun f ↦ (p.factorial : ℚ) * coeff p f) hg
  have left (i : ℕ) : (p.factorial : ℚ) * coeff p ((exp ℚ ^ 2) ^ i) =
      2 ^ p * (i : ℚ) ^ p := by
    rw [← pow_mul, exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp]
    push_cast
    simp [Algebra.algebraMap_self, mul_pow]
    field_simp
  have right (m : ℕ) : (p.factorial : ℚ) * coeff p
      (exp ℚ ^ n * (((n + m + 1).choose (2 * m + 1) : ℚ⟦X⟧) * centeredExp ^ m)) =
      thmQ k (m + 1) n * ((n + m + 1).choose (2 * m + 1) : ℚ) := by
    rw [mul_left_comm, mul_comm (exp ℚ ^ n), coeff_natCast_mul,
      ← factorial_mul_coeff_centeredExp k m n hk]
    change _ = ((p.factorial : ℚ) * _) * _
    ring
  change _ = (p.factorial : ℚ) * coeff p (exp ℚ ^ n * binomialSum centeredExp n) at h
  simp only [binomialSum, mul_sum, map_sum] at h
  simp_rw [left, right] at h
  rw [← mul_sum, sum_thmQ_change_bound k n hk] at h
  rw [sum_range_succ'] at h
  simp only [Nat.cast_zero, zero_pow hp, add_zero] at h
  simpa only [powerSum, ← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    Nat.add_comm 1, show ∀ m, 2 * (m + 1) - 1 = 2 * m + 1 by omega,
    Nat.add_assoc] using h

end OddPowerSums

section EvenPowerSums

open PowerSeries Finset

-- Shift the geometric sum by -2n so its exponents range from -2n to 2n.
private theorem centered_geomSum (n : ℕ) :
    (∑ i ∈ range (2 * n + 1), rescale (2 * ((i : ℚ) - n)) (exp ℚ)) =
      binomialSum centeredExp (2 * n) := by
  have shift (i : ℕ) : rescale (-(2 * (n : ℚ))) (exp ℚ) * (exp ℚ ^ 2) ^ i =
      rescale (2 * ((i : ℚ) - n)) (exp ℚ) := by
    rw [← pow_mul, exp_pow_eq_rescale_exp, exp_mul_exp_eq_exp_add]
    push_cast
    rw [show -(2 * (n : ℚ)) + 2 * i = 2 * (i - n) by ring]
  have cancel : rescale (-(2 * (n : ℚ))) (exp ℚ) * exp ℚ ^ (2 * n) = 1 := by
    rw [exp_pow_eq_rescale_exp, exp_mul_exp_eq_exp_add]
    simp
  simp_rw [← shift]
  rw [← mul_sum, geomSum_eq_binomialSum (exp ℚ) (rescale (-1) (exp ℚ))
    (by simpa using exp_mul_exp_eq_exp_add (1 : ℚ) (-1)), ← mul_assoc, cancel, one_mul]

-- Each positive integer and its negative contribute the same even power.
private theorem sum_centered_even_pow (k n : ℕ) (hk : 0 < k) :
    (∑ i ∈ range (2 * n + 1), ((i : ℚ) - n) ^ (2 * k)) = 2 * powerSum (2 * k) n := by
  induction n with
  | zero => simp [powerSum, zero_pow (by omega : 2 * k ≠ 0)]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega, sum_range_succ, sum_range_succ']
    simp only [Nat.cast_succ, add_sub_add_right_eq_sub, Nat.cast_zero, zero_sub,
      (even_two_mul k).neg_pow, ih]
    simp only [powerSum, sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]
    push_cast
    rw [show 2 * (n : ℚ) + 1 - n = n + 1 by ring]
    ring

/-- **Even power sums in terms of $\binom{2n+m+1}{2m+1}$.** For natural numbers $k \ge 1$ and
$n$, write $S_{2k}(n) = 1^{2k} + 2^{2k} + \dots + n^{2k}$ and
$R(k, m) = \sum_{j=0}^{m} (-1)^j \binom{2m}{j} (m - j)^{2k}$. Then
$2^{2k} S_{2k}(n) = \sum_{m=1}^{k} R(k, m) \binom{2n+m+1}{2m+1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Theorem 1. -/
theorem pow_mul_powerSum_even_eq_sum (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    (2 : ℚ) ^ (2 * k) * powerSum (2 * k) n =
      ∑ m ∈ Finset.Icc 1 k,
        (arrayR k m : ℚ) *
          (Nat.choose (2 * n + m + 1) (2 * m + 1) : ℚ) := by
  have h := congrArg (fun f ↦ ((2 * k).factorial : ℚ) * coeff (2 * k) f) (centered_geomSum n)
  have left (i : ℕ) : ((2 * k).factorial : ℚ) *
      coeff (2 * k) (rescale (2 * ((i : ℚ) - n)) (exp ℚ)) =
      2 ^ (2 * k) * ((i : ℚ) - n) ^ (2 * k) := by
    rw [coeff_rescale, coeff_exp, mul_pow]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  have right (m : ℕ) : ((2 * k).factorial : ℚ) * coeff (2 * k)
      (((2 * n + m + 1).choose (2 * m + 1) : ℚ⟦X⟧) * centeredExp ^ m) =
      2 * ((arrayR k m : ℚ) * (2 * n + m + 1).choose (2 * m + 1)) := by
    rw [coeff_natCast_mul, coeff_pow_exp_add_rescale_neg_one_sub_two hk]
    field_simp
  simp only [binomialSum, map_sum, mul_sum] at h
  simp_rw [left, right] at h
  rw [← mul_sum, ← mul_sum, sum_centered_even_pow k n hk] at h
  calc
    _ = ∑ m ∈ range (2 * n + 1),
          (arrayR k m : ℚ) * (2 * n + m + 1).choose (2 * m + 1) := by linarith only [h]
    _ = _ := by
      apply sum_congr_of_eq_on_inter _ _ (fun _ _ _ ↦ rfl)
      · intro m _ hm
        rcases Nat.eq_zero_or_pos m with rfl | hpos
        · simp [arrayR, zero_pow (by omega : 2 * k ≠ 0)]
        · have hmk : k < m := by simp only [mem_Icc] at hm; omega
          simp [arrayR_eq_zero_of_lt hk hmk]
      · intro m _ hm
        simp only [mem_range] at hm
        simp [Nat.choose_eq_zero_of_lt (show 2 * n + m + 1 < 2 * m + 1 by omega)]

end EvenPowerSums

section Faulhaber

open Finset MetaMathlibExt Polynomial

-- Pair the two halves of the descending factorial around n and n + 1.
private theorem legendreProduct_eq_factorial_mul_choose (n m : ℕ) :
    (∏ j ∈ range m, ((n : ℚ) * (n + 1) - (j : ℚ) * (j + 1))) =
      ((2 * m).factorial : ℚ) * ((n + m).choose (2 * m) : ℚ) := by
  by_cases hnm : m ≤ n
  · have h := congrArg (Nat.castRingHom ℚ) (Nat.descFactorial_eq_prod_range (n + m) (2 * m))
    rw [Nat.descFactorial_eq_factorial_mul_choose, map_mul, map_prod] at h
    change ((2 * m).factorial : ℚ) * ((n + m).choose (2 * m) : ℚ) =
      ∏ i ∈ range (2 * m), ((n + m - i : ℕ) : ℚ) at h
    rw [h]
    have hcast (i : ℕ) (hi : i ∈ range (2 * m)) :
        ((n + m - i : ℕ) : ℚ) = (n : ℚ) + m - i := by
      simp only [mem_range] at hi
      rw [Nat.cast_sub (show i ≤ n + m by omega), Nat.cast_add]
    rw [prod_congr rfl hcast, two_mul m, prod_range_add,
      ← prod_range_reflect (fun i : ℕ ↦ (n : ℚ) + m - i) m, ← prod_mul_distrib]
    refine prod_congr rfl fun j hj ↦ ?_
    have hj' := mem_range.mp hj
    rw [Nat.cast_add, Nat.cast_sub (show j ≤ m - 1 by omega),
      Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
    ring
  · rw [Nat.choose_eq_zero_of_lt (show n + m < 2 * m by omega), Nat.cast_zero, mul_zero]
    exact prod_eq_zero (mem_range.mpr (show n < m by omega)) (sub_self _)

private theorem legendrePoly_eval (m : ℕ) (x : ℚ) :
    eval₂ (Int.castRingHom ℚ) x (legendreStirlingFirstPoly m) =
      ∏ j ∈ range m, (x - (j : ℚ) * (j + 1)) := by
  change eval₂RingHom (Int.castRingHom ℚ) x (∏ j ∈ range m,
    (X - C ((j : ℤ) * (j + 1)))) = _
  rw [map_prod]
  refine prod_congr rfl fun j _ ↦ ?_
  rw [map_sub]
  change eval₂ (Int.castRingHom ℚ) x X - eval₂ (Int.castRingHom ℚ) x (C _) = _
  rw [eval₂_X, eval₂_C, map_mul, map_add, map_one, map_natCast]

-- For positive m the factor with j = 0 eliminates the constant coefficient.
private theorem legendrePoly_eval_eq_sum (m : ℕ) (hm : 1 ≤ m) (x : ℚ) :
    eval₂ (Int.castRingHom ℚ) x (legendreStirlingFirstPoly m) =
      ∑ r ∈ Icc 1 m, (legendreStirlingFirst m r : ℚ) * x ^ r := by
  rw [eval₂_eq_sum, Polynomial.sum]
  apply sum_congr_of_eq_on_inter
  · intro r hr h
    have hnz : legendreStirlingFirst m r ≠ 0 := mem_support_iff.mp hr
    have hrm : r ≤ m := by
      by_contra! hlt
      exact hnz (legendreStirlingFirst_eq_zero_of_lt m r hlt)
    have : r = 0 := by simp only [mem_Icc] at h; omega
    subst r
    change (legendreStirlingFirst m 0 : ℚ) * x ^ 0 = 0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    rw [legendreStirlingFirst_succ_zero j, Int.cast_zero, zero_mul]
  · intro r _ hr
    have hz : (legendreStirlingFirstPoly m).coeff r = 0 := by
      simpa only [mem_support_iff, not_ne_iff] using hr
    change ((legendreStirlingFirstPoly m).coeff r : ℚ) * x ^ r = 0
    simp [hz]
  · intro r _ _
    rfl

private theorem two_mul_powerSum_one (n : ℕ) :
    (n : ℚ) * (n + 1) = 2 * powerSum 1 n := by
  induction n with
  | zero => simp [powerSum]
  | succ n ih =>
    simp only [powerSum, sum_Icc_succ_top (Nat.succ_pos n), pow_one, Nat.cast_succ] at ih ⊢
    linear_combination ih

/-- **Binomial coefficients in the signed Legendre–Stirling basis.** For natural numbers $n$
and $m \ge 1$, let $S_1(n) = n(n+1)/2$ and let $\mathrm{Ps}_m^{(r)}$ denote the coefficient of
$X^r$ in $\prod_{j=0}^{m-1}(X-j(j+1))$. Then

$$\binom{n+m}{2m} = \frac{1}{(2m)!}\sum_{r=1}^{m}\mathrm{Ps}_m^{(r)}\,(2S_1(n))^r.$$

Source: José L. Cereceda, *Sums of Powers of Integers and the Sequence A304330*, equation (20). -/
theorem choose_eq_legendreStirlingFirst_sum (n m : ℕ) (hm : 1 ≤ m) :
    ((n + m).choose (2 * m) : ℚ) =
      (∑ r ∈ Icc 1 m, (legendreStirlingFirst m r : ℚ) * (2 * powerSum 1 n) ^ r) /
        ((2 * m).factorial : ℚ) := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm, ← legendreProduct_eq_factorial_mul_choose, ← legendrePoly_eval,
    two_mul_powerSum_one, legendrePoly_eval_eq_sum m hm]

-- With the constant coefficient zero, the recurrence multiplies the linear coefficient
-- in row m by `-m * (m + 1)` to give the linear coefficient in row m + 1.
private theorem legendreStirlingFirst_cast_one (m : ℕ) :
    (legendreStirlingFirst (m + 1) 1 : ℚ) =
      (-1 : ℚ) ^ m * (m.factorial : ℚ) * ((m + 1).factorial : ℚ) := by
  induction m with
  | zero => simp [legendreStirlingFirst_diag]
  | succ m ih =>
    rw [legendreStirlingFirst_succ (m + 1) 0]
    push_cast
    rw [legendreStirlingFirst_succ_zero m, Int.cast_zero, ih, zero_sub,
      pow_succ (-1 : ℚ), Nat.factorial_succ (m + 1), Nat.factorial_succ m]
    push_cast
    ring

/-- For `k ≥ 2`, the signed Legendre–Stirling coefficients of degree one cancel in the odd
power-sum expansion: their sum weighted by `R(k,m) / ((2m)! m)` is zero. This is equation
(21) of Cereceda's *Sums of Powers of Integers and the Sequence A304330*, with row index
`k` in place of `k + 1`. -/
theorem sum_arrayR_legendreStirlingFirst_one_eq_zero (k : ℕ) (hk : 2 ≤ k) :
    (∑ m ∈ Icc 1 k, (1 / (((2 * m).factorial : ℚ) * m)) *
      (arrayR k m : ℚ) * (legendreStirlingFirst m 1 : ℚ)) = 0 := by
  have hterm (m : ℕ) (hm : m ∈ Icc 1 k) :
      (1 / (((2 * m).factorial : ℚ) * m)) * (arrayR k m : ℚ) *
          (legendreStirlingFirst m 1 : ℚ) =
        -((-1 : ℚ) ^ m * ((Nat.factorial (m - 1) : ℚ) ^ 2 / ((2 * m).factorial : ℚ)) *
          (arrayR k m : ℚ)) := by
    have hm₀ : m ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hm).1
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm₀
    rw [legendreStirlingFirst_cast_one, Nat.factorial_succ j, pow_succ (-1 : ℚ),
      Nat.succ_sub_one]
    push_cast
    field_simp
  rw [sum_congr rfl hterm, sum_neg_distrib, sum_neg_factorial_sq_div_arrayR_eq_zero k hk, neg_zero]

private theorem six_mul_powerSum_two (n : ℕ) :
    (2 * (n : ℚ) + 1) * ((n : ℚ) * (n + 1)) = 6 * powerSum 2 n := by
  induction n with
  | zero => simp [powerSum]
  | succ n ih =>
    simp only [powerSum, sum_Icc_succ_top (Nat.succ_pos n), Nat.cast_succ] at ih ⊢
    linear_combination ih

/-- **The Faulhaber coefficients $b_{k,r}$.** For natural numbers $p$ and $q$, let
$R(p, q) = \sum_{j=0}^{q} (-1)^j \binom{2q}{j} (q - j)^{2p}$, and for natural numbers $q$
and $s$ let $\mathrm{Ps}_q^{(s)}$ be the Legendre–Stirling number of the first kind, the
coefficient of $x^s$ in $\prod_{i=0}^{q-1} (x - i(i+1))$. For natural numbers $k$ and $r$,
$b_{k,r}$ is the rational number
$\sum_{m=r}^{k} \frac{3 \cdot 2^r}{(2m+1)!}\, R(k, m)\, \mathrm{Ps}_m^{(r)}$. -/
@[expose] noncomputable def faulhaberB (k r : ℕ) : ℚ :=
  ∑ m ∈ Finset.Icc r k,
    (3 * 2 ^ r / (Nat.factorial (2 * m + 1) : ℚ)) *
      (arrayR k m : ℚ) * (MetaMathlibExt.legendreStirlingFirst m r : ℚ)

/-- **Faulhaber form of the even power sums.** For all natural numbers $k \ge 1$ and $n$,
writing $S_j(n) = 1^j + 2^j + \cdots + n^j$ for the power sums and $b_{k,r}$ for the Faulhaber
coefficients of Proposition 12, the rational numbers satisfy
$S_{2k}(n) = S_2(n) \sum_{r=1}^{k} b_{k,r} \, S_1(n)^{r-1}$.

Source: José L. Cereceda, "Sums of Powers of Integers and the
Sequence A304330", Proposition 12. -/
theorem powerSum_even_faulhaber (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) :
    powerSum (2 * k) n =
      powerSum 2 n * ∑ r ∈ Finset.Icc 1 k,
        faulhaberB k r * (powerSum 1 n) ^ (r - 1) := by
  have hs : powerSum 2 n = (2 * (n : ℚ) + 1) * powerSum 1 n / 3 := by
    have h := six_mul_powerSum_two n
    rw [two_mul_powerSum_one] at h
    linear_combination -h / 6
  let term (m r : ℕ) : ℚ :=
    powerSum 2 n * (((3 * 2 ^ r / ((2 * m + 1).factorial : ℚ)) * (arrayR k m : ℚ) *
      (legendreStirlingFirst m r : ℚ)) * (powerSum 1 n) ^ (r - 1))
  rw [powerSum_even_eq_sum k hk n]
  calc
    _ = ∑ m ∈ Icc 1 k, ∑ r ∈ Icc 1 m, term m r := by
      refine sum_congr rfl fun m hm ↦ ?_
      have hfac : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
      rw [choose_eq_legendreStirlingFirst_sum n m (mem_Icc.mp hm).1, sum_div, mul_sum]
      refine sum_congr rfl fun r hr ↦ ?_
      have hpow : (2 * powerSum 1 n) ^ r =
          2 ^ r * powerSum 1 n * (powerSum 1 n) ^ (r - 1) := by
        have hr₁ := (mem_Icc.mp hr).1
        rw [mul_pow, mul_assoc, ← pow_succ', Nat.sub_add_cancel hr₁]
      dsimp only [term]
      rw [hpow, hs, Nat.factorial_succ]
      push_cast
      field_simp [hfac, show 2 * (m : ℚ) + 1 ≠ 0 by positivity]
    _ = ∑ r ∈ Icc 1 k, ∑ m ∈ Icc r k, term m r := by
      apply sum_comm'
      intro m r
      simp only [mem_Icc]
      omega
    _ = _ := by
      simp only [term, faulhaberB, mul_sum, sum_mul]

end Faulhaber

end MathlibExt.Combinatorics.Enumerative.SumsOfPowersA304330Wanted
