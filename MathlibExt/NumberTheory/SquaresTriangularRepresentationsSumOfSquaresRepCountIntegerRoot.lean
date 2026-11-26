/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.Int.Interval
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Inverse

public import MathlibExt.NumberTheory.SquareRepresentationCongruences
public import MathlibExt.NumberTheory.TriangularRepresentationWindow

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Integer zeros of the sums-of-squares counting polynomial

Statements from Alegri and Christopher, *On Formulas, Recurrences, and
Congruences for Representations of Integers as Sums of Squares and Triangular
Numbers*, INTEGERS 26 (2026), Article A93. This module proves that for every
`n ≥ 0` there is a polynomial `P ∈ ℤ[z]` with `P(z) = n! r_z(n)` for every integer
`z`, where `r_z(n)` is the coefficient of `q^n` in `θ(q)^z` for the square theta
series `θ`, and that every nonzero integer `k` with `r_k(n) = 0` divides the
coefficient `c_1` of `P` and satisfies `|k| < 2 |c_i|^{1/(n-i)}` for some `i < n`.
-/

namespace MetaMathlibExt

@[expose] public section

-- The nonconstant part of the square theta series.
private noncomputable def ssF : PowerSeries ℤ := squareThetaSeries - 1

private noncomputable def ssU : (PowerSeries ℤ)ˣ := isUnit_squareThetaSeries.unit

private theorem ssU_val : (ssU : PowerSeries ℤ) = squareThetaSeries := IsUnit.unit_spec _

private theorem one_add_ssF : 1 + ssF = squareThetaSeries := by
  simp only [ssF]
  abel

private theorem coeff_zero_ssF : PowerSeries.coeff 0 ssF = 0 := by
  have h : PowerSeries.coeff 0 ssF
      = PowerSeries.coeff 0 squareThetaSeries - PowerSeries.coeff 0 1 := by
    simp only [ssF, map_sub]
  rw [h, coeff_squareThetaSeries_small.1]
  simp

private theorem X_dvd_ssF : PowerSeries.X ∣ ssF := by
  rw [PowerSeries.X_dvd_iff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_ssF]

private theorem coeff_ssF_pow_eq_zero (j m : ℕ) (hm : m < j) :
    PowerSeries.coeff m (ssF ^ j) = 0 :=
  PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd X_dvd_ssF j) m hm

-- Evaluations of Mathlib's falling factorial polynomial `descPochhammer ℤ j`.
private theorem descPochhammer_eval_succ_add_one (z : ℤ) (i : ℕ) :
    (descPochhammer ℤ (i + 1)).eval (z + 1)
      = (descPochhammer ℤ (i + 1)).eval z + ((i : ℤ) + 1) * (descPochhammer ℤ i).eval z := by
  have h1 : (descPochhammer ℤ (i + 1)).eval (z + 1) = (z + 1) * (descPochhammer ℤ i).eval z := by
    simp [descPochhammer_succ_left]
  rw [h1, descPochhammer_succ_eval]
  ring

-- The cofactor `n! / j!`.
private def cof (n j : ℕ) : ℤ := ((Nat.factorial n / Nat.factorial j : ℕ) : ℤ)

private theorem cof_mul_factorial (n j : ℕ) (h : j ≤ n) :
    cof n j * ((j.factorial : ℕ) : ℤ) = ((n.factorial : ℕ) : ℤ) := by
  have hdiv : n.factorial / j.factorial * j.factorial = n.factorial :=
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial h)
  calc cof n j * ((j.factorial : ℕ) : ℤ)
        = ((((n.factorial / j.factorial * j.factorial : ℕ))) : ℤ) := by
        simp only [cof]
        push_cast
        ring
    _ = ((n.factorial : ℕ) : ℤ) := by rw [hdiv]

private theorem cof_succ_mul (n i : ℕ) (h : i + 1 ≤ n) :
    cof n (i + 1) * ((i : ℤ) + 1) = cof n i := by
  have hfac : ((((i + 1).factorial : ℕ)) : ℤ)
      = ((i : ℤ) + 1) * (((i.factorial : ℕ)) : ℤ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have e1 := cof_mul_factorial n (i + 1) h
  have e2 := cof_mul_factorial n i (Nat.le_of_succ_le h)
  rw [hfac] at e1
  have hpos : ((((i.factorial : ℕ))) : ℤ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  apply mul_right_cancel₀ hpos
  calc cof n (i + 1) * (↑i + 1) * ↑(i.factorial)
        = cof n (i + 1) * ↑((i + 1).factorial) := by
        rw [hfac]
        ring
    _ = ↑(n.factorial) := e1
    _ = cof n i * ↑(i.factorial) := e2.symm

-- The truncated binomial expansion and its difference from the unit power.
private noncomputable def truncSum (n : ℕ) (z : ℤ) : PowerSeries ℤ :=
  ∑ j ∈ Finset.range (n + 1), PowerSeries.C (cof n j * (descPochhammer ℤ j).eval z) * ssF ^ j

private noncomputable def truncDiff (n : ℕ) (z : ℤ) : PowerSeries ℤ :=
  PowerSeries.C ((n.factorial : ℕ) : ℤ) * ((ssU ^ z : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
    - truncSum n z

private theorem unit_pow_natCast (m : ℕ) :
    ((ssU ^ (m : ℤ) : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = (1 + ssF) ^ m := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, ssU_val, ← one_add_ssF]

private theorem unit_pow_succ (z : ℤ) :
    ((ssU ^ (z + 1) : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      = ((ssU ^ z : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) * (1 + ssF) := by
  rw [zpow_add_one, Units.val_mul, ssU_val, ← one_add_ssF]

private theorem natCoeff_identity (n m j : ℕ) (hjm : j ≤ m) (hjn : j ≤ n) :
    ((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ)
      = cof n j * (descPochhammer ℤ j).eval (m : ℤ) := by
  have hchoose : ((m.choose j : ℕ) : ℤ) * (((j.factorial : ℕ)) : ℤ)
      * ((((m - j).factorial : ℕ)) : ℤ) = (((m.factorial : ℕ)) : ℤ) := by
    have h := Nat.choose_mul_factorial_mul_factorial hjm
    exact_mod_cast h
  have hfall : (descPochhammer ℤ j).eval (m : ℤ) * ((((m - j).factorial : ℕ)) : ℤ)
      = (((m.factorial : ℕ)) : ℤ) := by
    rw [descPochhammer_eval_eq_descFactorial, mul_comm]
    exact_mod_cast Nat.factorial_mul_descFactorial hjm
  have hcof := cof_mul_factorial n j hjn
  have hpos : ((((j.factorial : ℕ))) : ℤ) * ((((m - j).factorial : ℕ)) : ℤ) ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast Nat.factorial_ne_zero j
    · exact_mod_cast Nat.factorial_ne_zero (m - j)
  apply mul_right_cancel₀ hpos
  calc (((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ))
          * (↑(j.factorial) * ↑((m - j).factorial))
        = ((n.factorial : ℕ) : ℤ)
          * (((m.choose j : ℕ) : ℤ) * ↑(j.factorial) * ↑((m - j).factorial)) := by ring
    _ = ((n.factorial : ℕ) : ℤ) * (((m.factorial : ℕ)) : ℤ) := by rw [hchoose]
    _ = (cof n j * ↑(j.factorial))
          * ((descPochhammer ℤ j).eval (m : ℤ) * ↑((m - j).factorial)) := by
        rw [hcof, hfall]
    _ = (cof n j * (descPochhammer ℤ j).eval (m : ℤ))
          * (↑(j.factorial) * ↑((m - j).factorial)) := by ring

private theorem binom_expansion (m : ℕ) :
    (1 + ssF) ^ m
      = ∑ j ∈ Finset.range (m + 1), PowerSeries.C (((m.choose j : ℕ)) : ℤ) * ssF ^ j := by
  rw [add_comm (1 : PowerSeries ℤ) ssF, add_pow]
  apply Finset.sum_congr rfl
  intro k _
  rw [one_pow, mul_one, map_natCast, mul_comm]

private theorem dvd_truncDiff_nat (n m : ℕ) :
    PowerSeries.X ^ (n + 1) ∣ truncDiff n (m : ℤ) := by
  have hexpand : PowerSeries.C (((n.factorial : ℕ)) : ℤ)
        * (∑ j ∈ Finset.range (m + 1), PowerSeries.C (((m.choose j : ℕ)) : ℤ) * ssF ^ j)
      = ∑ j ∈ Finset.range (m + 1),
        PowerSeries.C (((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ)) * ssF ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_assoc, ← map_mul]
  simp only [truncDiff, truncSum, unit_pow_natCast, binom_expansion, hexpand]
  rcases le_total m n with hmn | hnm
  · have hsub : ∑ j ∈ Finset.range (n + 1),
          PowerSeries.C (cof n j * (descPochhammer ℤ j).eval (m : ℤ)) * ssF ^ j
        = ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C (cof n j * (descPochhammer ℤ j).eval (m : ℤ)) * ssF ^ j := by
      rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hmn)]
      have hzero : ∑ j ∈ Finset.Ico (m + 1) (n + 1),
          PowerSeries.C (cof n j * (descPochhammer ℤ j).eval (m : ℤ)) * ssF ^ j = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [Finset.mem_Ico] at hj
        rw [descPochhammer_eval_natCast_of_lt (by omega : m < j), mul_zero, map_zero, zero_mul]
      rw [hzero, add_zero]
    rw [hsub]
    have hterms : ∀ j ∈ Finset.range (m + 1),
        PowerSeries.C (((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ)) * ssF ^ j
          = PowerSeries.C (cof n j * (descPochhammer ℤ j).eval (m : ℤ)) * ssF ^ j := by
      intro j hj
      rw [Finset.mem_range] at hj
      congr 1
      congr 1
      exact natCoeff_identity n m j (by omega) (by omega)
    rw [Finset.sum_congr rfl hterms, sub_self]
    exact dvd_zero _
  · have hsplit : ∑ j ∈ Finset.range (m + 1),
          PowerSeries.C (((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ)) * ssF ^ j
        = ∑ j ∈ Finset.range (n + 1),
            PowerSeries.C (((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ)) * ssF ^ j
          + ∑ j ∈ Finset.Ico (n + 1) (m + 1),
            PowerSeries.C (((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ)) * ssF ^ j := by
      rw [Finset.sum_range_add_sum_Ico _ (Nat.succ_le_succ hnm)]
    rw [hsplit]
    have hterms : ∀ j ∈ Finset.range (n + 1),
        PowerSeries.C (((n.factorial : ℕ) : ℤ) * ((m.choose j : ℕ) : ℤ)) * ssF ^ j
          = PowerSeries.C (cof n j * (descPochhammer ℤ j).eval (m : ℤ)) * ssF ^ j := by
      intro j hj
      rw [Finset.mem_range] at hj
      congr 1
      congr 1
      exact natCoeff_identity n m j (by omega) (by omega)
    rw [Finset.sum_congr rfl hterms, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro j hj
    rw [Finset.mem_Ico] at hj
    have h1 : PowerSeries.X ^ (n + 1) ∣ ssF ^ j :=
      dvd_trans (pow_dvd_pow _ hj.1) (pow_dvd_pow_of_dvd X_dvd_ssF j)
    exact dvd_trans h1 (dvd_mul_left _ _)

-- Reindexing a sum by shifting the summation variable down by one.
private theorem shift_sum (n : ℕ) (F G : ℕ → PowerSeries ℤ) (hG0 : G 0 = 0)
    (hG : ∀ j, j < n → G (j + 1) = F j) (B : PowerSeries ℤ) (hB : F n = B) :
    ∑ j ∈ Finset.range (n + 1), F j = ∑ j ∈ Finset.range (n + 1), G j + B := by
  rw [Finset.sum_range_succ F n, hB]
  have hEq : ∑ j ∈ Finset.range n, F j = ∑ j ∈ Finset.range (n + 1), G j := by
    rw [Finset.sum_range_succ' G n, hG0, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    exact (hG j hj).symm
  rw [hEq]

private theorem cof_descPochhammer_succ (n i : ℕ) (z : ℤ) (h : i + 1 ≤ n) :
    cof n (i + 1) * (descPochhammer ℤ (i + 1)).eval (z + 1)
      = cof n (i + 1) * (descPochhammer ℤ (i + 1)).eval z
        + cof n i * (descPochhammer ℤ i).eval z := by
  have hfall := descPochhammer_eval_succ_add_one z i
  have hcof := cof_succ_mul n i h
  have hmul : cof n (i + 1) * (((i : ℤ) + 1) * (descPochhammer ℤ i).eval z)
      = cof n i * (descPochhammer ℤ i).eval z := by
    rw [← mul_assoc, hcof]
  rw [hfall, mul_add, hmul]

private theorem truncSum_step (n : ℕ) (z : ℤ) :
    truncSum n (z + 1) = truncSum n z * (1 + ssF)
      - PowerSeries.C (cof n n * (descPochhammer ℤ n).eval z) * ssF ^ (n + 1) := by
  set F : ℕ → PowerSeries ℤ :=
    fun j => PowerSeries.C (cof n j * (descPochhammer ℤ j).eval z) * ssF ^ (j + 1) with hF
  set G : ℕ → PowerSeries ℤ := fun j =>
    if j = 0 then 0
    else PowerSeries.C (cof n (j - 1) * (descPochhammer ℤ (j - 1)).eval z) * ssF ^ j with hG
  set B : PowerSeries ℤ :=
    PowerSeries.C (cof n n * (descPochhammer ℤ n).eval z) * ssF ^ (n + 1) with hB
  have hAF : truncSum n z * ssF = ∑ j ∈ Finset.range (n + 1), F j := by
    simp only [truncSum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [hF]
    rw [mul_assoc, ← pow_succ]
  have hG0 : G 0 = 0 := by
    rw [hG]
    simp
  have hGs : ∀ j, j < n → G (j + 1) = F j := by
    intro j _
    have hne : j + 1 ≠ 0 := by omega
    simp only [hG, hF, hne, ↓reduceIte, Nat.add_sub_cancel]
  have hBn : F n = B := by rw [hF, hB]
  have hGB : ∑ j ∈ Finset.range (n + 1), F j
      = ∑ j ∈ Finset.range (n + 1), G j + B := shift_sum n F G hG0 hGs B hBn
  have hterm : ∀ j ∈ Finset.range (n + 1),
      PowerSeries.C (cof n j * (descPochhammer ℤ j).eval (z + 1)) * ssF ^ j
        = PowerSeries.C (cof n j * (descPochhammer ℤ j).eval z) * ssF ^ j + G j := by
    intro j hj
    match j with
    | 0 => simp [hG]
    | i + 1 =>
      have hne : i + 1 ≠ 0 := by omega
      simp only [hG, hne, ↓reduceIte, Nat.add_sub_cancel]
      have hmem : i + 1 ≤ n := by
        rw [Finset.mem_range] at hj
        omega
      have hpas := cof_descPochhammer_succ n i z hmem
      rw [← add_mul, ← map_add, ← hpas]
  have hAS : truncSum n z + ∑ j ∈ Finset.range (n + 1), G j = truncSum n (z + 1) := by
    simp only [truncSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    exact (hterm j hj).symm
  have hA : truncSum n z * (1 + ssF) = truncSum n z + ∑ j ∈ Finset.range (n + 1), F j := by
    rw [mul_add, mul_one, hAF]
  rw [hA, hGB, ← hAS, hB]
  abel

private theorem truncDiff_step (n : ℕ) (z : ℤ) :
    truncDiff n (z + 1) = truncDiff n z * (1 + ssF)
      + PowerSeries.C (cof n n * (descPochhammer ℤ n).eval z) * ssF ^ (n + 1) := by
  simp only [truncDiff, unit_pow_succ, truncSum_step]
  ring

private theorem dvd_truncDiff_succ (n : ℕ) (z : ℤ)
    (h : PowerSeries.X ^ (n + 1) ∣ truncDiff n (z + 1)) :
    PowerSeries.X ^ (n + 1) ∣ truncDiff n z := by
  have hB : PowerSeries.X ^ (n + 1)
      ∣ PowerSeries.C (cof n n * (descPochhammer ℤ n).eval z) * ssF ^ (n + 1) :=
    dvd_trans (pow_dvd_pow_of_dvd X_dvd_ssF _) (dvd_mul_left _ _)
  have hmul : PowerSeries.X ^ (n + 1) ∣ truncDiff n z * (1 + ssF) := by
    have hstep := truncDiff_step n z
    have heq : truncDiff n z * (1 + ssF) = truncDiff n (z + 1)
        - PowerSeries.C (cof n n * (descPochhammer ℤ n).eval z) * ssF ^ (n + 1) := by
      rw [hstep]
      abel
    rw [heq]
    exact dvd_sub h hB
  have hunit : (1 + ssF : PowerSeries ℤ) * ((ssU⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    rw [one_add_ssF, ← ssU_val, Units.mul_inv]
  have hfactor : truncDiff n z
      = truncDiff n z * (1 + ssF) * ((ssU⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) := by
    rw [mul_assoc, hunit, mul_one]
  rw [hfactor]
  exact dvd_mul_of_dvd_left hmul _

private theorem dvd_truncDiff_neg (n : ℕ) (t : ℕ) :
    PowerSeries.X ^ (n + 1) ∣ truncDiff n (-(t : ℤ)) := by
  induction t with
  | zero => simpa using dvd_truncDiff_nat n 0
  | succ t ih =>
    have h2 : (-(t : ℤ)) - 1 + 1 = -(t : ℤ) := by ring
    have hcast : (-(((t + 1 : ℕ)) : ℤ)) = (-(t : ℤ)) - 1 := by push_cast; ring
    rw [hcast]
    apply dvd_truncDiff_succ n _
    rwa [h2]

private theorem dvd_truncDiff (n : ℕ) (z : ℤ) :
    PowerSeries.X ^ (n + 1) ∣ truncDiff n z := by
  rcases le_total 0 z with hz | hz
  · have hnat : (((z.toNat : ℕ)) : ℤ) = z := Int.toNat_of_nonneg hz
    rw [← hnat]
    exact dvd_truncDiff_nat n z.toNat
  · have hneg : 0 ≤ -z := by omega
    have hnat : ((((-z).toNat : ℕ)) : ℤ) = -z := Int.toNat_of_nonneg hneg
    have hz2 : z = -((((-z).toNat : ℕ)) : ℤ) := by
      rw [hnat, neg_neg]
    rw [hz2]
    exact dvd_truncDiff_neg n _

-- The counting polynomial.
private noncomputable def ssPoly (n : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (PowerSeries.coeff n (ssF ^ j) * cof n j) * descPochhammer ℤ j

private theorem eval_sum_poly (s : Finset ℕ) (f : ℕ → Polynomial ℤ) (z : ℤ) :
    (∑ j ∈ s, f j).eval z = ∑ j ∈ s, (f j).eval z := by
  rw [← Polynomial.coe_evalRingHom, map_sum]

private theorem ssPoly_eval (n : ℕ) (z : ℤ) :
    (ssPoly n).eval z = ((n.factorial : ℕ) : ℤ) * sumOfSquaresRepCount z n := by
  have hdiv := dvd_truncDiff n z
  have hcoeff := PowerSeries.X_pow_dvd_iff.mp hdiv n (by omega : n < n + 1)
  simp only [truncDiff, truncSum, map_sub, PowerSeries.coeff_C_mul, map_sum] at hcoeff
  have heval : (ssPoly n).eval z
      = ∑ j ∈ Finset.range (n + 1),
        (PowerSeries.coeff n (ssF ^ j) * cof n j) * (descPochhammer ℤ j).eval z := by
    simp only [ssPoly, eval_sum_poly, Polynomial.eval_mul, Polynomial.eval_C]
  have hmain : ((n.factorial : ℕ) : ℤ)
        * PowerSeries.coeff n ((ssU ^ z : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
      = ∑ j ∈ Finset.range (n + 1),
        (cof n j * (descPochhammer ℤ j).eval z) * PowerSeries.coeff n (ssF ^ j) :=
    sub_eq_zero.mp hcoeff
  calc (ssPoly n).eval z
      = ∑ j ∈ Finset.range (n + 1),
        (PowerSeries.coeff n (ssF ^ j) * cof n j) * (descPochhammer ℤ j).eval z := heval
    _ = ∑ j ∈ Finset.range (n + 1),
        (cof n j * (descPochhammer ℤ j).eval z) * PowerSeries.coeff n (ssF ^ j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = ((n.factorial : ℕ) : ℤ) * sumOfSquaresRepCount z n := by
        rw [← hmain]
        simp only [sumOfSquaresRepCount, ssU]

private theorem ssPoly_coeff_zero (n : ℕ) (hn : 1 ≤ n) : (ssPoly n).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, ssPoly_eval]
  have h0 : sumOfSquaresRepCount 0 n = 0 := by
    have hn0 : n ≠ 0 := by omega
    simp only [sumOfSquaresRepCount, zpow_zero, Units.val_one, PowerSeries.coeff_one, hn0,
      ↓reduceIte]
  rw [h0, mul_zero]

private theorem dvd_coeff_one_of_root (n : ℕ) (hn : 1 ≤ n) (k : ℤ) (hk : k ≠ 0)
    (h0 : sumOfSquaresRepCount k n = 0) : k ∣ (ssPoly n).coeff 1 := by
  have heval : (ssPoly n).eval k = 0 := by rw [ssPoly_eval, h0, mul_zero]
  have hc0 := ssPoly_coeff_zero n hn
  have hdecomp : ssPoly n = (ssPoly n).divX * Polynomial.X := by
    have h := Polynomial.divX_mul_X_add (ssPoly n)
    rw [hc0, Polynomial.C_0, add_zero] at h
    exact h.symm
  have hdivX0 : (ssPoly n).divX.eval k = 0 := by
    have h1 : (ssPoly n).divX.eval k * k = 0 := by
      have hcongr := congrArg (Polynomial.eval k) hdecomp
      rw [heval] at hcongr
      simpa [Polynomial.eval_mul, Polynomial.eval_X] using hcongr
    exact (mul_eq_zero.mp h1).resolve_right hk
  have hdvd := Polynomial.sub_dvd_eval_sub k 0 (ssPoly n).divX
  rw [hdivX0, sub_zero] at hdvd
  have heval0 : (ssPoly n).divX.eval 0 = (ssPoly n).coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact Polynomial.coeff_divX
  rw [heval0, zero_sub] at hdvd
  exact dvd_neg.mp hdvd

private theorem coeff_one_ssF : PowerSeries.coeff 1 ssF = 2 := by
  have h : PowerSeries.coeff 1 ssF
      = PowerSeries.coeff 1 squareThetaSeries - PowerSeries.coeff 1 1 := by
    simp only [ssF, map_sub]
  rw [h, coeff_squareThetaSeries_small.2.1]
  simp

private noncomputable def ssG : PowerSeries ℤ :=
  PowerSeries.mk fun m => PowerSeries.coeff (m + 1) ssF

private theorem coeff_zero_ssG : PowerSeries.coeff 0 ssG = 2 := by
  simp only [ssG, PowerSeries.coeff_mk, zero_add, coeff_one_ssF]

private theorem ssF_eq : ssF = PowerSeries.X * ssG := by
  rw [PowerSeries.ext_iff]
  intro m
  match m with
  | 0 => rw [coeff_zero_ssF, PowerSeries.coeff_zero_X_mul]
  | m + 1 =>
    rw [PowerSeries.coeff_succ_X_mul]
    simp only [ssG, PowerSeries.coeff_mk]

private theorem coeff_ssF_pow (t : ℕ) :
    PowerSeries.coeff t (ssF ^ t) = 2 ^ t := by
  have hpow : ssF ^ t = PowerSeries.X ^ t * ssG ^ t := by
    rw [ssF_eq, mul_pow]
  have hshift := PowerSeries.coeff_X_pow_mul (ssG ^ t) t 0
  rw [zero_add] at hshift
  rw [hpow, hshift]
  have h0 : PowerSeries.coeff 0 (ssG ^ t) = (PowerSeries.coeff 0 ssG) ^ t := by
    simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow]
  rw [h0, coeff_zero_ssG]

private theorem coeff_ssF_pow_ne_zero (t : ℕ) : PowerSeries.coeff t (ssF ^ t) ≠ 0 := by
  rw [coeff_ssF_pow]
  exact pow_ne_zero t (by norm_num)

private theorem natDegree_term_le' (n j : ℕ) :
    (Polynomial.C (PowerSeries.coeff n (ssF ^ j) * cof n j) * descPochhammer ℤ j).natDegree
      ≤ j := by
  calc (Polynomial.C (PowerSeries.coeff n (ssF ^ j) * cof n j) * descPochhammer ℤ j).natDegree
      ≤ (Polynomial.C (PowerSeries.coeff n (ssF ^ j) * cof n j)).natDegree
        + (descPochhammer ℤ j).natDegree := Polynomial.natDegree_mul_le
    _ = 0 + (descPochhammer ℤ j).natDegree := by rw [Polynomial.natDegree_C]
    _ ≤ 0 + j := add_le_add le_rfl (descPochhammer_natDegree ℤ j).le
    _ = j := zero_add j

private theorem natDegree_ssPoly_le (n : ℕ) : (ssPoly n).natDegree ≤ n := by
  simp only [ssPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  rw [Finset.mem_range] at hj
  exact le_trans (natDegree_term_le' n j) (by omega : j ≤ n)

private theorem cof_self (n : ℕ) : cof n n = 1 := by
  simp only [cof, Nat.div_self (Nat.factorial_pos n), Nat.cast_one]

private theorem coeff_finset_sum (s : Finset ℕ) (f : ℕ → Polynomial ℤ) (k : ℕ) :
    (∑ j ∈ s, f j).coeff k = ∑ j ∈ s, (f j).coeff k := by
  have h := map_sum (Polynomial.lcoeff ℤ k) f s
  rwa [Polynomial.lcoeff_apply] at h

private theorem coeff_ssPoly_self (n : ℕ) : (ssPoly n).coeff n ≠ 0 := by
  have hsum : (ssPoly n).coeff n
      = ∑ j ∈ Finset.range (n + 1),
        (Polynomial.C (PowerSeries.coeff n (ssF ^ j) * cof n j) * descPochhammer ℤ j).coeff n := by
    simp only [ssPoly, coeff_finset_sum]
  rw [hsum, Finset.sum_range_succ]
  have hzero : ∑ j ∈ Finset.range n,
      (Polynomial.C (PowerSeries.coeff n (ssF ^ j) * cof n j) * descPochhammer ℤ j).coeff n
        = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    calc (Polynomial.C (PowerSeries.coeff n (ssF ^ j) * cof n j) * descPochhammer ℤ j).natDegree
        ≤ j := natDegree_term_le' n j
      _ < n := hj
  have hlead : (descPochhammer ℤ n).coeff n = 1 := by
    simpa using (monic_descPochhammer ℤ n).coeff_natDegree
  rw [hzero, zero_add, Polynomial.coeff_C_mul, hlead, cof_self, mul_one, mul_one]
  exact coeff_ssF_pow_ne_zero n

private theorem geom_half_sum (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1 / 2 : ℝ) ^ (j + 1)) = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem geom_half_sum_lt (n : ℕ) :
    ∑ j ∈ Finset.range n, ((1 / 2 : ℝ) ^ (j + 1)) < 1 := by
  rw [geom_half_sum]
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  linarith

private theorem abs_le_of_rpow_bound (c : ℤ) (K : ℝ) (n i : ℕ) (hi : i < n)
    (h : 2 * (|(c : ℝ)|) ^ ((1 : ℝ) / ((n : ℝ) - (i : ℝ))) ≤ K) :
    |(c : ℝ)| ≤ (K / 2) ^ (n - i) := by
  have hni : (0 : ℝ) < (n : ℝ) - (i : ℝ) := by
    have hlt : (i : ℝ) < (n : ℝ) := by exact_mod_cast hi
    linarith
  have hne : (n : ℝ) - (i : ℝ) ≠ 0 := ne_of_gt hni
  set e : ℝ := (1 : ℝ) / ((n : ℝ) - (i : ℝ)) with he
  have hAK : (|(c : ℝ)|) ^ e ≤ K / 2 := by linarith
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg (abs_nonneg _) e) hAK (n - i)
  have hcast : ((((n - i : ℕ))) : ℝ) = (n : ℝ) - (i : ℝ) := Nat.cast_sub hi.le
  have hem : e * ((((n - i : ℕ))) : ℝ) = 1 := by
    rw [he, hcast, one_div_mul_cancel hne]
  have hLHS : ((|(c : ℝ)|) ^ e) ^ (n - i) = |(c : ℝ)| := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _), hem, Real.rpow_one]
  rw [hLHS] at hpow
  exact hpow

private theorem abs_bound_of_root (n : ℕ) (k : ℤ) (hk : k ≠ 0)
    (h0 : sumOfSquaresRepCount k n = 0) :
    ∃ i < n, (|k| : ℝ)
      < 2 * (|(ssPoly n).coeff i| : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - (i : ℝ))) := by
  have heval : (ssPoly n).eval k = 0 := by rw [ssPoly_eval, h0, mul_zero]
  have hdeg : (ssPoly n).natDegree < n + 1 := Nat.lt_succ_of_le (natDegree_ssPoly_le n)
  have hsum := Polynomial.eval_eq_sum_range' hdeg (k : ℤ)
  rw [heval, Finset.sum_range_succ] at hsum
  have hcn : (ssPoly n).coeff n ≠ 0 := coeff_ssPoly_self n
  have hsplit : (ssPoly n).coeff n * k ^ n
      = -∑ i ∈ Finset.range n, (ssPoly n).coeff i * k ^ i :=
    eq_neg_of_add_eq_zero_right hsum.symm
  have hsplitR : ((ssPoly n).coeff n : ℝ) * (k : ℝ) ^ n
      = -∑ i ∈ Finset.range n, ((ssPoly n).coeff i : ℝ) * (k : ℝ) ^ i := by
    exact_mod_cast hsplit
  have habs : |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n
      ≤ ∑ i ∈ Finset.range n, |((ssPoly n).coeff i : ℝ)| * |(k : ℝ)| ^ i := by
    have h2 : |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n
        = |∑ i ∈ Finset.range n, ((ssPoly n).coeff i : ℝ) * (k : ℝ) ^ i| := by
      have h3 := congrArg (abs : ℝ → ℝ) hsplitR
      rwa [abs_mul, abs_pow, abs_neg] at h3
    rw [h2]
    calc |∑ i ∈ Finset.range n, ((ssPoly n).coeff i : ℝ) * (k : ℝ) ^ i|
        ≤ ∑ i ∈ Finset.range n, |((ssPoly n).coeff i : ℝ) * (k : ℝ) ^ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ Finset.range n, |((ssPoly n).coeff i : ℝ)| * |(k : ℝ)| ^ i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_pow]
  by_contra hcon
  have hcon' : ∀ i, i < n →
      2 * (|((ssPoly n).coeff i : ℝ)|) ^ ((1 : ℝ) / ((n : ℝ) - (i : ℝ)))
        ≤ |(k : ℝ)| := by
    intro i hi
    apply le_of_not_gt
    intro hlt
    exact hcon ⟨i, hi, hlt⟩
  have hterm : ∀ i ∈ Finset.range n,
      |((ssPoly n).coeff i : ℝ)| * |(k : ℝ)| ^ i
        ≤ |(k : ℝ)| ^ n * (1 / 2 : ℝ) ^ (n - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hAi := abs_le_of_rpow_bound ((ssPoly n).coeff i) |(k : ℝ)| n i hi (hcon' i hi)
    have hKi : (0 : ℝ) ≤ |(k : ℝ)| ^ i := by positivity
    have hmi : (n - i) + i = n := by omega
    have hcalc : (|(k : ℝ)| / 2) ^ (n - i) * |(k : ℝ)| ^ i
        = |(k : ℝ)| ^ n * (1 / 2 : ℝ) ^ (n - i) := by
      have h2 : ((1 / 2 : ℝ) ^ (n - i)) = 1 / (2 : ℝ) ^ (n - i) := by
        rw [div_pow, one_pow]
      rw [div_pow, h2, div_mul_eq_mul_div, mul_one_div, ← pow_add, hmi]
    calc |((ssPoly n).coeff i : ℝ)| * |(k : ℝ)| ^ i
        ≤ (|(k : ℝ)| / 2) ^ (n - i) * |(k : ℝ)| ^ i :=
          mul_le_mul_of_nonneg_right hAi hKi
      _ = |(k : ℝ)| ^ n * (1 / 2 : ℝ) ^ (n - i) := hcalc
  have hsum_le : ∑ i ∈ Finset.range n, |((ssPoly n).coeff i : ℝ)| * |(k : ℝ)| ^ i
      ≤ |(k : ℝ)| ^ n * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact hterm i hi
  have hreindex : ∑ i ∈ Finset.range n, ((1 / 2 : ℝ) ^ (n - i))
      = ∑ j ∈ Finset.range n, ((1 / 2 : ℝ) ^ (j + 1)) := by
    rw [← Finset.sum_range_reflect (fun i => (1 / 2 : ℝ) ^ (n - i)) n]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    congr 1
    omega
  have hS_lt1 : ∑ i ∈ Finset.range n, ((1 / 2 : ℝ) ^ (n - i)) < 1 := by
    rw [hreindex]
    exact geom_half_sum_lt n
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hKn_pos : (0 : ℝ) < |(k : ℝ)| ^ n := pow_pos (abs_pos.mpr hkR) n
  have hcn1 : (1 : ℝ) ≤ |((ssPoly n).coeff n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |(ssPoly n).coeff n| := by
      have hpos : 0 < |(ssPoly n).coeff n| := abs_pos.mpr hcn
      omega
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|(ssPoly n).coeff n| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_one, Int.cast_abs] at h2
  have hchain1 : |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n < |(k : ℝ)| ^ n * 1 := by
    calc |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n
        ≤ ∑ i ∈ Finset.range n, |((ssPoly n).coeff i : ℝ)| * |(k : ℝ)| ^ i := habs
      _ ≤ |(k : ℝ)| ^ n * ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (n - i) := hsum_le
      _ < |(k : ℝ)| ^ n * 1 := mul_lt_mul_of_pos_left hS_lt1 hKn_pos
  have hchain2 : |(k : ℝ)| ^ n * 1 ≤ |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n := by
    calc |(k : ℝ)| ^ n * 1 = |(k : ℝ)| ^ n := mul_one _
      _ ≤ |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n := by
          have hle := mul_le_mul_of_nonneg_right hcn1 (le_of_lt hKn_pos)
          rwa [one_mul] at hle
  have hcontra : |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n
      < |((ssPoly n).coeff n : ℝ)| * |(k : ℝ)| ^ n :=
    lt_of_lt_of_le hchain1 hchain2
  exact lt_irrefl _ hcontra

private theorem repCount_zero_eq_one (k : ℤ) : sumOfSquaresRepCount k 0 = 1 := by
  have h1 : Units.map PowerSeries.constantCoeff.toMonoidHom ssU = 1 := by
    apply Units.ext
    change PowerSeries.constantCoeff (ssU : PowerSeries ℤ) = 1
    rw [ssU_val, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      coeff_squareThetaSeries_small.1]
  have hmap := map_zpow (Units.map PowerSeries.constantCoeff.toMonoidHom) ssU k
  rw [h1] at hmap
  have hval : PowerSeries.constantCoeff ((ssU ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    have hveq : PowerSeries.constantCoeff ((ssU ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ)
        = ((Units.map PowerSeries.constantCoeff.toMonoidHom (ssU ^ k) : ℤˣ) : ℤ) := rfl
    rw [hveq, hmap, one_zpow, Units.val_one]
  have hcoeff : PowerSeries.coeff 0 ((ssU ^ k : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hval
  simpa only [sumOfSquaresRepCount, ssU] using hcoeff

/-- **Integer zeros of the sums-of-squares counting polynomial.** For an integer $k$ and $n \ge 0$,
let $r_k(n)$ be the coefficient of $q^n$ in $\theta(q)^k$, where $\theta$ is the square theta
series. For every $n \ge 0$ there is a polynomial $P(z) = \sum_i c_i z^i$ with integer
coefficients such that $P(z) = n! \, r_z(n)$ for every integer $z$, and every nonzero integer $k$
with $r_k(n) = 0$ divides $c_1$ and satisfies $|k| < 2 |c_i|^{1/(n-i)}$ for some $i$ with
$0 \le i < n$.

Equivalently, $|k| < 2 R_n$ with $R_n = \max_{0 \le i \le n-1} |c_i|^{1/(n-i)}$.

Source: Alegri and Christopher, *On Formulas, Recurrences, and Congruences for
Representations of Integers as Sums of Squares and Triangular Numbers*, INTEGERS
26 (2026), Article A93, Theorem 9 (`integers-2026-A93-thm-9`). -/
public theorem sumOfSquaresRepCount_integer_root (n : ℕ) :
    ∃ P : Polynomial ℤ, (∀ z : ℤ, P.eval z = n.factorial * sumOfSquaresRepCount z n) ∧
      ∀ k : ℤ, k ≠ 0 → sumOfSquaresRepCount k n = 0 →
        k ∣ P.coeff 1 ∧
          ∃ i < n, (|k| : ℝ) < 2 * (|P.coeff i| : ℝ) ^ ((1 : ℝ) / ((n : ℝ) - i)) := by
  refine ⟨ssPoly n, ssPoly_eval n, ?_⟩
  intro k hk h0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exfalso
    rw [repCount_zero_eq_one] at h0
    exact one_ne_zero h0
  · exact ⟨dvd_coeff_one_of_root n hn k hk h0, abs_bound_of_root n k hk h0⟩

end

end MetaMathlibExt
