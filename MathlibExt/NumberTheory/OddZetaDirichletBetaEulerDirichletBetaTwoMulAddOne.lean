/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta

import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry17Bernoullipolysymmetry
import MathlibExt.NumberTheory.TothOddZeta

/-!
# Dirichlet beta at odd positive integers

The value of the Dirichlet beta function at each odd positive integer is expressed using
an even-index Euler number, a power of pi, and a factorial.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 3, Equation (12)
(`integers-2025-A50-prop-3`), citing its references [3], [6].

The proof reuses existing formalizations: the value `bernoulli_eval_quarter_eq_chapter5EulerEven`
of the Bernoulli polynomials at $1/4$ in terms of the even-index Euler numbers comes from
`MathlibExt.NumberTheory.TothOddZeta` (itself derived from
`EulerNumbers.bernoulli_eval_quarter_of_recurrence`), and the identification
`sinZeta_quarter_eq_beta` of the sine zeta function at $1/4$ with $\beta$ comes from
`MathlibExt.Analysis.Ramanujan.Part1Ch7Entry17Bernoullipolysymmetry`.
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry17Bernoullipolysymmetry
open Finset

private lemma beta_signed (m : ℕ) (hm : m ≠ 0) :
    chapter7DirichletBeta (2 * m + 1) =
      (Real.pi : ℂ) ^ (2 * m + 1) * ((-1 : ℂ) ^ m * (chapter5EulerEven m : ℂ)) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ)) := by
  have hB : ((Polynomial.bernoulli (2 * m + 1)).map (algebraMap ℚ ℂ)).eval
      ((1 / 4 : ℝ) : ℂ) = (((Polynomial.bernoulli (2 * m + 1)).eval (1 / 4 : ℚ) : ℚ) : ℂ) := by
    rw [Polynomial.eval_map]
    have hq : ((1 / 4 : ℝ) : ℂ) = algebraMap ℚ ℂ (1 / 4 : ℚ) := by norm_num
    rw [hq, Polynomial.eval₂_at_apply]
    simp
  have hf4 : (4 : ℂ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfact : (((2 * m).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m)
  have hn : (2 * (m : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show (2 * m + 1 : ℕ) ≠ 0 by omega)
  have hb : (((Polynomial.bernoulli (2 * m + 1)).eval (1 / 4 : ℚ) : ℚ) : ℂ) =
      -((2 * (m : ℂ) + 1) * (chapter5EulerEven m : ℂ)) / (4 : ℂ) ^ (2 * m + 1) := by
    have h := congrArg ((↑) : ℚ → ℂ) (bernoulli_eval_quarter_eq_chapter5EulerEven m)
    push_cast at h
    rw [h]
    ring
  rw [← sinZeta_quarter_eq_beta, HurwitzZeta.sinZeta_two_mul_nat_add_one hm
    (by constructor <;> norm_num), hB, hb]
  have hfac : (((2 * m + 1).factorial : ℕ) : ℂ) =
      (2 * (m : ℂ) + 1) * ((2 * m).factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; rfl
  have hp4 : (4 : ℂ) ^ (2 * m + 1) =
      (2 : ℂ) ^ (2 * m + 1) * (2 : ℂ) ^ (2 * m + 1) := by
    rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_pow]
  have hexp : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [hfac, mul_pow, hp4, pow_succ (-1 : ℂ), hexp, pow_succ (2 : ℂ)]
  field_simp
  ring

private lemma beta_hurwitz (s : ℂ) :
    chapter7DirichletBeta s = 2 * (4 : ℂ) ^ (-s) *
      HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle) s := by
  rw [chapter7DirichletBeta, ZMod.LFunction_def_odd betaCharOdd, betaCharUnivFour]
  rw [Finset.sum_insert (by decide : (0 : ZMod 4) ∉
      ({(1 : ZMod 4), 2, 3} : Finset (ZMod 4))),
    Finset.sum_insert (by decide : (1 : ZMod 4) ∉ ({(2 : ZMod 4), 3} : Finset (ZMod 4))),
    Finset.sum_insert (by decide : (2 : ZMod 4) ∉ ({(3 : ZMod 4)} : Finset (ZMod 4))),
    Finset.sum_singleton]
  simp only [
    betaChar0, betaChar1, betaChar2, betaChar3, zero_mul, one_mul, neg_one_mul, zero_add,
    Nat.cast_ofNat]
  have hc1 : ZMod.toAddCircle (1 : ZMod 4) = ((1 / 4 : ℝ) : UnitAddCircle) := by
    rw [ZMod.toAddCircle_apply, show (1 : ZMod 4).val = 1 by decide]; norm_num
  have hc3 : ZMod.toAddCircle (3 : ZMod 4) = -((1 / 4 : ℝ) : UnitAddCircle) := by
    rw [show (3 : ZMod 4) = -1 by decide, map_neg, hc1]
  rw [hc1, hc3, HurwitzZeta.hurwitzZetaOdd_neg]
  ring
private lemma beta_nonneg (m : ℕ) (hm : m ≠ 0) :
    0 ≤ (chapter7DirichletBeta (2 * m + 1)).re := by
  have hs : 1 < (((2 * m + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast (show 1 < 2 * m + 1 by omega)
  have hh := HurwitzZeta.hasSum_nat_hurwitzZetaOdd_of_mem_Icc
    (a := (1 / 4 : ℝ)) (by constructor <;> norm_num) hs
  have hn : 0 ≤ (HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle)
      ((2 * m + 1 : ℕ) : ℂ)).re := by
    apply HasSum.nonneg _ (Complex.hasSum_re hh)
    intro n
    have he :
        ((1 / ((n : ℂ) + ((1 / 4 : ℝ) : ℂ)) ^ ((2 * m + 1 : ℕ) : ℂ) -
          1 / ((n : ℂ) + 1 - ((1 / 4 : ℝ) : ℂ)) ^ ((2 * m + 1 : ℕ) : ℂ)) / 2).re =
        (1 / ((n : ℝ) + 1 / 4) ^ (2 * m + 1) -
          1 / ((n : ℝ) + 3 / 4) ^ (2 * m + 1)) / 2 := by
      rw [Complex.cpow_natCast, Complex.cpow_natCast]
      have hthree : (n : ℂ) + 1 - ((1 / 4 : ℝ) : ℂ) =
          (((n : ℝ) + 3 / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [hthree]
      norm_cast
    rw [he]
    apply div_nonneg _ (by norm_num)
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpow : (4 : ℂ) ^ (-((2 * m + 1 : ℕ) : ℂ)) =
      ((1 / (4 : ℝ) ^ (2 * m + 1) : ℝ) : ℂ) := by
    rw [Complex.cpow_neg, Complex.cpow_natCast]
    norm_num [Complex.ofReal_inv, Complex.ofReal_pow]
  have hcast : (2 * (m : ℂ) + 1) = ((2 * m + 1 : ℕ) : ℂ) := by simp
  rw [hcast, beta_hurwitz, hpow]
  have hreal : (2 : ℂ) * ((1 / (4 : ℝ) ^ (2 * m + 1) : ℝ) : ℂ) =
      ((2 * (1 / (4 : ℝ) ^ (2 * m + 1)) : ℝ) : ℂ) := by push_cast; rfl
  rw [hreal, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) hn

private lemma beta_one : chapter7DirichletBeta 1 = (Real.pi : ℂ) / 4 := by
  have hb := ramanujan_part1_ch7_entry17_bernoullipolysymmetry.2.1 1 (by simp)
  have hp := Complex.continuous_ofReal.tendsto (Real.pi / 4) |>.comp Real.tendsto_sum_pi_div_four
  have hsum : chapter7DirichletBetaPartialSum 1 =
      fun N => ((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) : ℝ) : ℂ) := by
    funext N
    simp [chapter7DirichletBetaPartialSum, chapter7DirichletBetaTerm, Complex.cpow_one,
      Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_pow]
  rw [hsum] at hb
  simpa using tendsto_nhds_unique hb hp
private lemma euler_abs (m : ℕ) (hm : m ≠ 0) :
    (-1 : ℂ) ^ m * (chapter5EulerEven m : ℂ) = ((|chapter5EulerEven m| : ℤ) : ℂ) := by
  have heq : (chapter7DirichletBeta (2 * m + 1)).re =
      Real.pi ^ (2 * m + 1) * ((-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ)) := by
    rw [beta_signed m hm]
    have hc : (Real.pi : ℂ) ^ (2 * m + 1) * ((-1 : ℂ) ^ m * (chapter5EulerEven m : ℂ)) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ)) =
        ((Real.pi ^ (2 * m + 1) * ((-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)) /
          (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hc]
    rfl
  have hcoeff : 0 < Real.pi ^ (2 * m + 1) /
      (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ)) := by positivity
  have hnonneg : 0 ≤ (Real.pi ^ (2 * m + 1) /
      (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ))) *
      ((-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)) := by
    have h := beta_nonneg m hm
    rw [heq] at h
    convert h using 1
    ring
  have hs := (mul_nonneg_iff_of_pos_left hcoeff).mp hnonneg
  have habs : |(-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)| = |(chapter5EulerEven m : ℝ)| := by
    rw [abs_mul, abs_pow]
    simp
  have hr : (-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ) = ((|chapter5EulerEven m| : ℤ) : ℝ) := by
    rw [Int.cast_abs, ← habs, abs_of_nonneg hs]
  have h := congrArg Complex.ofReal hr
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_intCast] using h

/-- **Dirichlet beta at odd positive integers.** Let $\beta$ be the Dirichlet $L$-function of the
nontrivial character modulo $4$, which for $\operatorname{Re} s > 1$ is the series
$\beta(s) = \sum_{n \ge 1} (-1)^{n-1}/(2n-1)^s$, and let $E_0 = 1, E_2 = -1, E_4 = 5,
E_6 = -61, \dots$ be the even-index Euler numbers. Then for every natural number $m$,
$$\beta(2m+1) = \frac{\pi^{2m+1} \, |E_{2m}|}{2^{2m+2} \, (2m)!}.$$

For example $\beta(1) = \pi/4$, $\beta(3) = \pi^3/32$, $\beta(5) = 5\pi^5/1536$ and
$\beta(7) = 61\pi^7/184320$. With $k = 2m+2$ this is the source's Equation (12),
$\beta(k-1) = (\pi/2)^{k-1} |E_{k-2}| / (2 (k-2)!)$ for even $k \ge 2$. At $s = 1$ the series
converges only conditionally, and its sum is the value of the $L$-function there.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 3, Equation (12)
(`integers-2025-A50-prop-3`), citing its references [3], [6]. -/
public theorem dirichletBeta_two_mul_add_one (m : ℕ) :
    chapter7DirichletBeta (2 * m + 1) =
      (Real.pi : ℂ) ^ (2 * m + 1) * ((|chapter5EulerEven m| : ℤ) : ℂ) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · norm_num [chapter5EulerEven_zero]
    exact beta_one
  · rw [beta_signed m hm, euler_abs m hm]

end

end MetaMathlibExt
