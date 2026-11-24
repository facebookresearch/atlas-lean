/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import MathlibExt.Combinatorics.Enumerative.QRWhitneyNumbers
public import MathlibExt.NumberTheory.QRDowlingPolynomial
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Exponential generating function of the Dowling numbers

`MetaMathlibExt.hasSum_dowling_egf` proves that the Dowling numbers
$D_n = \sum_{k=0}^{n} W_{2,1,1}(n, k)$ of the group of order $2$ have exponential generating
function $\exp\bigl(x + (e^{2x} - 1)/2\bigr)$ for every complex $x$.

The proof expands $(2j + 1)^n = \sum_{k} W_{2,1,1}(n, k) \, 2^k \, j^{\underline{k}}$ in falling
factorials, which gives the Dobinski-type formula
$e^{1/2} D_n = \sum_{j \ge 0} (2j + 1)^n / (2^j j!)$, and then sums the absolutely convergent
double series $\sum_{j, n} (2j + 1)^n x^n / (2^j j! \, n!)$ in both orders.
-/

namespace MetaMathlibExt

@[expose] public section

namespace hasSum_dowling_egf

open Finset

-- The `(q, r)`-Whitney numbers of the second kind with `m = 2`, `r = 1` and `q = 1`.
local notation "W" => QRWhitney.whitneySecond 2 1 1

private theorem whitney_succ_zero (n : ℕ) : W (n + 1) 0 = W n 0 := by
  rw [QRWhitney.whitneySecond_succ_zero, one_mul]

private theorem whitney_succ_succ (n k : ℕ) :
    W (n + 1) (k + 1) = W n k + (2 * ((k : ℂ) + 1) + 1) * W n (k + 1) := by
  have hq : QRWhitney.qBrack 1 (k + 1) = (k : ℂ) + 1 := by
    change ∑ i ∈ range (k + 1), (1 : ℂ) ^ i = (k : ℂ) + 1
    simp
  rw [QRWhitney.whitneySecond_succ_succ, one_pow, one_mul, hq]

private theorem cast_descFactorial_succ (j k : ℕ) :
    ((j.descFactorial (k + 1) : ℕ) : ℂ) = ((j : ℂ) - k) * (j.descFactorial k : ℂ) := by
  rcases le_or_gt k j with h | h
  · rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h,
      Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_succ_of_lt h)]
    simp

-- The expansion `(2j + 1)^n = ∑ₖ W(n, k) 2^k j(j - 1)⋯(j - k + 1)`.
private theorem pow_eq_sum_descFactorial (n j : ℕ) :
    (2 * (j : ℂ) + 1) ^ n =
      ∑ k ∈ range (n + 1), W n k * 2 ^ k * (j.descFactorial k : ℂ) := by
  induction n with
  | zero => simp [QRWhitney.whitneySecond_zero_zero]
  | succ n ih =>
    have hz : W n (n + 1) = 0 := QRWhitney.whitneySecond_eq_zero_of_lt (Nat.lt_succ_self n)
    have h2 := sum_range_succ' (fun k => (2 * (k : ℂ) + 1) * W n k * 2 ^ k *
      (j.descFactorial k : ℂ)) (n + 1)
    rw [sum_range_succ, hz] at h2
    simp only [mul_zero, zero_mul, add_zero, Nat.cast_zero, pow_zero, Nat.descFactorial_zero,
      Nat.cast_one, mul_one, zero_add, one_mul, Nat.cast_add] at h2
    rw [sum_range_succ', whitney_succ_zero, pow_succ, ih, sum_mul]
    simp only [whitney_succ_succ, pow_zero, Nat.descFactorial_zero, Nat.cast_one, mul_one,
      cast_descFactorial_succ]
    have h3 : ∀ k ∈ range (n + 1),
        (W n k + (2 * ((k : ℂ) + 1) + 1) * W n (k + 1)) * 2 ^ (k + 1) *
            (((j : ℂ) - k) * (j.descFactorial k : ℂ)) =
          W n k * 2 ^ (k + 1) * (((j : ℂ) - k) * (j.descFactorial k : ℂ)) +
          (2 * ((k : ℂ) + 1) + 1) * W n (k + 1) * 2 ^ (k + 1) *
            (j.descFactorial (k + 1) : ℂ) := by
      intro k _
      rw [cast_descFactorial_succ]
      ring
    rw [sum_congr rfl h3, sum_add_distrib, add_assoc, ← h2, ← sum_add_distrib]
    refine sum_congr rfl fun k _ => ?_
    ring

private theorem hasSum_cexp (z : ℂ) :
    HasSum (fun n : ℕ => z ^ n / n.factorial) (Complex.exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

private theorem hasSum_rexp (r : ℝ) :
    HasSum (fun n : ℕ => r ^ n / n.factorial) (Real.exp r) := by
  rw [Real.exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

-- `∑ⱼ 2^k j(j - 1)⋯(j - k + 1) / (2^j j!) = e^{1/2}` for every `k`.
private theorem hasSum_descFactorial_div (k : ℕ) :
    HasSum (fun j : ℕ => 2 ^ k * (j.descFactorial k : ℂ) / (2 ^ j * j.factorial))
      (Complex.exp (1 / 2)) := by
  rw [← hasSum_nat_add_iff' k]
  have h0 : ∑ i ∈ range k, (2 : ℂ) ^ k * (i.descFactorial k : ℂ) / (2 ^ i * i.factorial) =
      0 := by
    refine sum_eq_zero fun i hi => ?_
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (mem_range.mp hi)]
    simp
  rw [h0, sub_zero]
  refine (hasSum_cexp (1 / 2)).congr_fun fun i => ?_
  have hf : ((i.factorial : ℕ) : ℂ) * ((i + k).descFactorial k : ℂ) =
      ((i + k).factorial : ℂ) := by
    rw [← Nat.cast_mul, ← Nat.factorial_mul_descFactorial (Nat.le_add_left k i),
      Nat.add_sub_cancel]
  have hd : (((i + k).descFactorial k : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  have hi : ((i.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  rw [← hf, pow_add, div_pow, one_pow]
  field_simp

-- The Dobinski-type formula `∑ⱼ (2j + 1)^n / (2^j j!) = e^{1/2} D_n`.
private theorem hasSum_dobinski (n : ℕ) :
    HasSum (fun j : ℕ => (2 * (j : ℂ) + 1) ^ n / (2 ^ j * j.factorial))
      (Complex.exp (1 / 2) * qrDowlingNumber W n) := by
  rw [qrDowlingNumber_eq_sum, mul_comm, sum_mul]
  refine (hasSum_sum fun k _ => (hasSum_descFactorial_div k).mul_left (W n k)).congr_fun
    fun j => ?_
  rw [pow_eq_sum_descFactorial, div_eq_mul_inv, sum_mul]
  refine sum_congr rfl fun k _ => ?_
  ring

-- The double series of norms `∑_{j, n} ((2j + 1)‖x‖)^n / (2^j j! n!)` converges.
private theorem summable_norm_double (x : ℂ) :
    Summable (fun p : ℕ × ℕ =>
      1 / (2 ^ p.1 * (p.1.factorial : ℝ)) * (((2 * p.1 + 1) * ‖x‖) ^ p.2 / p.2.factorial)) := by
  have hGj : ∀ j : ℕ, HasSum (fun n : ℕ =>
      1 / (2 ^ j * (j.factorial : ℝ)) * (((2 * j + 1) * ‖x‖) ^ n / n.factorial))
      (1 / (2 ^ j * j.factorial) * Real.exp ((2 * j + 1) * ‖x‖)) :=
    fun j => (hasSum_rexp _).mul_left _
  refine (summable_prod_of_nonneg fun p => by positivity).mpr
    ⟨fun j => (hGj j).summable, ?_⟩
  have h : ∀ j : ℕ, ∑' n : ℕ,
      1 / (2 ^ j * (j.factorial : ℝ)) * (((2 * j + 1) * ‖x‖) ^ n / n.factorial) =
      Real.exp ‖x‖ * ((Real.exp (2 * ‖x‖) / 2) ^ j / j.factorial) := by
    intro j
    rw [(hGj j).tsum_eq, show (2 * (j : ℝ) + 1) * ‖x‖ = j * (2 * ‖x‖) + ‖x‖ by ring,
      Real.exp_add, Real.exp_nat_mul, div_pow]
    have : ((j.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  simp only [h]
  exact ((hasSum_rexp _).mul_left _).summable

-- The double series `∑_{j, n} (2j + 1)^n x^n / (2^j j! n!)` converges absolutely.
private theorem summable_double (x : ℂ) :
    Summable (fun p : ℕ × ℕ =>
      (2 * (p.1 : ℂ) + 1) ^ p.2 / (2 ^ p.1 * p.1.factorial) * (x ^ p.2 / p.2.factorial)) := by
  refine Summable.of_norm ((summable_norm_double x).congr fun p => ?_)
  have h1 : ‖(2 * (p.1 : ℂ) + 1)‖ = 2 * p.1 + 1 := by
    rw [show (2 * (p.1 : ℂ) + 1) = ((2 * p.1 + 1 : ℕ) : ℂ) by push_cast; ring,
      Complex.norm_natCast]
    push_cast
    ring
  rw [norm_mul, norm_div, norm_div, norm_pow, norm_pow, h1, norm_mul, norm_pow,
    Complex.norm_natCast, Complex.norm_natCast, Complex.norm_ofNat, mul_pow]
  ring

-- For fixed `j`, the sum over `n` is `e^{(2j + 1)x} / (2^j j!) = e^x (e^{2x} / 2)^j / j!`.
private theorem hasSum_double_fst (x : ℂ) (j : ℕ) :
    HasSum (fun n : ℕ =>
      (2 * (j : ℂ) + 1) ^ n / (2 ^ j * j.factorial) * (x ^ n / n.factorial))
      (Complex.exp x * ((Complex.exp (2 * x) / 2) ^ j / j.factorial)) := by
  have h := (hasSum_cexp ((2 * (j : ℂ) + 1) * x)).mul_left (1 / (2 ^ j * (j.factorial : ℂ)))
  have hval : 1 / (2 ^ j * (j.factorial : ℂ)) * Complex.exp ((2 * j + 1) * x) =
      Complex.exp x * ((Complex.exp (2 * x) / 2) ^ j / j.factorial) := by
    rw [show (2 * (j : ℂ) + 1) * x = j * (2 * x) + x by ring, Complex.exp_add,
      Complex.exp_nat_mul, div_pow]
    have : ((j.factorial : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [mul_pow]
  ring

end hasSum_dowling_egf

open hasSum_dowling_egf in
/-- **Exponential generating function of the Dowling numbers.** For $n \ge 0$ let $D_n$ be the
$n$-th Dowling number of the group of order $2$, that is, the $(q, r)$-Dowling number
$D_n = \sum_{k=0}^{n} W_{2,1,1}(n, k)$ built from the $(q, r)$-Whitney numbers of the second
kind with $m = 2$, $r = 1$, $q = 1$. Then for every complex number $x$ the series
$\sum_{n \ge 0} D_n x^n / n!$ is summable with sum $\exp\bigl(x + (e^{2x} - 1)/2\bigr)$.

Source: Buck, Elder, Figueroa, Harris, Harry, Simpson, *Flattened Stirling
Permutations*, INTEGERS 24 (2024), Article A104, Corollary 3, generating
function. -/
public theorem hasSum_dowling_egf (x : ℂ) :
    HasSum (fun n : ℕ => qrDowlingNumber (QRWhitney.whitneySecond 2 1 1) n * x ^ n / n.factorial)
      (Complex.exp (x + (Complex.exp (2 * x) - 1) / 2)) := by
  have hg := (summable_double x).hasSum
  -- Summing over `n` first identifies the sum of the double series.
  have hval := (hg.prod_fiberwise (hasSum_double_fst x)).unique ((hasSum_cexp _).mul_left _)
  -- Summing over `j` first gives `e^{1/2} D_n x^n / n!` by the Dobinski-type formula.
  have hs := ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr hg).prod_fiberwise
    fun n => (hasSum_dobinski n).mul_right (x ^ n / n.factorial)
  rw [hval] at hs
  have h := hs.mul_left (Complex.exp (-(1 / 2)))
  have hval' : Complex.exp (-(1 / 2)) * (Complex.exp x * Complex.exp (Complex.exp (2 * x) / 2)) =
      Complex.exp (x + (Complex.exp (2 * x) - 1) / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    ring_nf
  rw [hval'] at h
  refine h.congr_fun fun n => ?_
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul,
    mul_div_assoc]

end

end MetaMathlibExt
