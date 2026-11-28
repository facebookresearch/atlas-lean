/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Combinatorics.ReducedComplexities
import Mathlib.NumberTheory.ZetaValues
import MathlibExt.Analysis.Asymptotics.CatalanAsymptoticExpansion

/-!
# Hurwitz zeta and paperfolding series at odd arguments

We express the Hurwitz zeta value at three quarters and each odd integer greater than one
in terms of the Riemann zeta value and an even-index Euler number. We also evaluate the
signed paperfolding Dirichlet series at those integers.
-/

namespace MetaMathlibExt

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry

/-- **Bernoulli polynomials at one quarter and Euler numbers.** For every natural number $k$,
$B_{2k+1}(1/4) = -(2k+1) E_{2k} / 4^{2k+1}$, where $E_{2k}$ is the even-index Euler number
`chapter5EulerEven k`. -/
public theorem bernoulli_eval_quarter_eq_chapter5EulerEven (k : ℕ) :
    (Polynomial.bernoulli (2 * k + 1)).eval (1 / 4) =
      -(2 * k + 1 : ℚ) * chapter5EulerEven k / 4 ^ (2 * k + 1) := by
  -- Extend the even-index sequence by zero at odd indices.
  let E (n : ℕ) := if n % 2 = 0 then chapter5EulerEven (n / 2) else 0
  have hE (n : ℕ) (hn : 0 < n) :
      ∑ j ∈ Finset.range (n / 2 + 1), (n.choose (2 * j) : ℤ) * E (n - 2 * j) = 0 := by
    by_cases he : n % 2 = 0
    · obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp (Nat.even_iff.mpr he)
      rw [Nat.mul_div_cancel_left _ (by decide : 0 < 2), ← Finset.sum_range_reflect]
      convert (chapter5EulerEven_recurrence m).trans (ite_eq_right (by omega)) using 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjm : j ≤ m := Finset.mem_range_succ_iff.mp hj
      rw [show m + 1 - 1 - j = m - j by omega,
        show 2 * (m - j) = 2 * m - 2 * j by omega,
        Nat.choose_symm (by omega), show 2 * m - (2 * m - 2 * j) = 2 * j by omega]
      simp [E]
    · apply Finset.sum_eq_zero
      intro j hj
      have hjn : j < n / 2 + 1 := Finset.mem_range.mp hj
      simp [E, show (n - 2 * j) % 2 ≠ 0 by omega]
  simpa [E] using EulerNumbers.bernoulli_eval_quarter_of_recurrence E
    ⟨by simp [E, chapter5EulerEven_zero], hE⟩ k

namespace hurwitzZeta_three_quarters_two_mul_add_one

private noncomputable def term (s n : ℕ) : ℝ := 1 / (n : ℝ) ^ s

private noncomputable def progression (s r : ℕ) : ℝ := ∑' n, term s (4 * n + r)

private lemma summable_progression {s : ℕ} (hs : 1 < s) (r : ℕ) :
    Summable (fun n => term s (4 * n + r)) :=
  (Real.summable_one_div_nat_pow.mpr hs).comp_injective
    (i := fun n : ℕ => 4 * n + r) (by intro a b h; dsimp at h; omega)

private lemma odd_sum {s : ℕ} (hs : 1 < s) :
    progression s 1 + progression s 3 = (1 - 1 / (2 : ℝ) ^ s) * ∑' n, term s n := by
  have ht : Summable (term s) := Real.summable_one_div_nat_pow.mpr hs
  have split {f : ℕ → ℝ} (hf : Summable f) :
      ∑' n, f (2 * n) + ∑' n, f (2 * n + 1) = ∑' n, f n :=
    tsum_even_add_odd
      (hf.comp_injective (i := fun n : ℕ => 2 * n) (by intro a b h; dsimp at h; omega))
      (hf.comp_injective (i := fun n : ℕ => 2 * n + 1) (by intro a b h; dsimp at h; omega))
  have ho : Summable (fun n => term s (2 * n + 1)) :=
    ht.comp_injective (i := fun n : ℕ => 2 * n + 1) (by intro a b h; dsimp at h; omega)
  have hodd := split ho
  simp only [show ∀ n : ℕ, 2 * (2 * n) + 1 = 4 * n + 1 by intro n; omega,
    show ∀ n : ℕ, 2 * (2 * n + 1) + 1 = 4 * n + 3 by intro n; omega] at hodd
  have heven (n : ℕ) : term s (2 * n) = (1 / (2 : ℝ) ^ s) * term s n := by
    simp [term, mul_pow, mul_comm]
  have h := split ht
  simp_rw [heven] at h
  rw [tsum_mul_left] at h
  rw [progression, progression, hodd]
  linarith

private lemma sine_sum {s : ℕ} (hs : 1 < s) :
    HasSum (fun n : ℕ => term s n * Real.sin (2 * Real.pi * n * (1 / 4)))
      (progression s 1 - progression s 3) := by
  let f (n : ℕ) := term s n * Real.sin (2 * Real.pi * n * (1 / 4))
  have h₀ (n : ℕ) : f (2 * n) = 0 := by
    simp only [f, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (2 * n) * (1 / 4) = n * Real.pi by ring, Real.sin_nat_mul_pi,
      mul_zero]
  have h₁ (n : ℕ) : f (2 * (2 * n) + 1) = term s (4 * n + 1) := by
    rw [show 2 * (2 * n) + 1 = 4 * n + 1 by omega]
    simp only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [show 2 * Real.pi * (4 * n + 1) * (1 / 4) = Real.pi / 2 + n * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two, mul_one]
  have h₃ (n : ℕ) : f (2 * (2 * n + 1) + 1) = -term s (4 * n + 3) := by
    rw [show 2 * (2 * n + 1) + 1 = 4 * n + 3 by omega]
    simp only [f, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [show 2 * Real.pi * (4 * n + 3) * (1 / 4) =
        (Real.pi / 2 + Real.pi) + n * (2 * Real.pi) by ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_add_pi, Real.sin_pi_div_two, mul_neg_one]
  have ho : HasSum (fun n => f (2 * n + 1)) (progression s 1 + -progression s 3) :=
    HasSum.even_add_odd ((summable_progression hs 1).hasSum.congr_fun h₁)
      ((summable_progression hs 3).hasSum.neg.congr_fun h₃)
  simpa only [zero_add, sub_eq_add_neg] using
    (HasSum.even_add_odd (f := f) (hasSum_zero.congr_fun h₀) ho)

private lemma odd_difference (k : ℕ) (hk : 1 ≤ k) :
    progression (2 * k + 1) 1 - progression (2 * k + 1) 3 =
      Real.pi ^ (2 * k + 1) * (|chapter5EulerEven k| : ℤ) /
        (2 * 2 ^ (2 * k + 1) * (2 * k).factorial) := by
  let s := 2 * k + 1
  have hs : 1 < s := by dsimp [s]; omega
  have hle : progression s 3 ≤ progression s 1 := by
    apply Summable.tsum_le_tsum _ (summable_progression hs 3) (summable_progression hs 1)
    intro n
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : 4 * n + 1 ≤ 4 * n + 3)) s
  have hB : bernoulliFun s (1 / 4) =
      -(s : ℝ) * (chapter5EulerEven k : ℝ) / (4 : ℝ) ^ s := by
    change (Polynomial.map (algebraMap ℚ ℝ) _).eval _ = _
    rw [show (1 / 4 : ℝ) = (algebraMap ℚ ℝ) (1 / 4 : ℚ) by norm_num,
      Polynomial.eval_map_apply, bernoulli_eval_quarter_eq_chapter5EulerEven]
    simp [s]
  have h := (sine_sum hs).unique
    (hasSum_one_div_nat_pow_mul_sin (k := k) (by omega)
      (show (1 / 4 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num))
  change progression s 1 - progression s 3 =
    (-1 : ℝ) ^ (k + 1) * (2 * Real.pi) ^ s / 2 / (s.factorial : ℝ) * bernoulliFun s _ at h
  have habs := congrArg abs h
  rw [abs_of_nonneg (sub_nonneg.mpr hle), hB] at habs
  have hval : progression s 1 - progression s 3 =
      (2 * Real.pi) ^ s / 2 / s.factorial *
        (s * |(chapter5EulerEven k : ℝ)| / 4 ^ s) := by
    simpa [abs_mul, abs_div, abs_pow, abs_of_pos Real.pi_pos] using habs
  rw [hval, Int.cast_abs, mul_pow, show (4 : ℝ) ^ s = (2 ^ s) ^ 2 by
    rw [sq, ← mul_pow]; norm_num]
  dsimp only [s]
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp

private lemma hurwitz_series (s : ℕ) (hs : 1 < s) :
    HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) s =
      ((4 ^ s * progression s 3 : ℝ) : ℂ) := by
  have h := HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
    (show (3 / 4 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (s := (s : ℂ)) (by simpa using hs)
  rw [← h.tsum_eq, Complex.ofReal_mul, progression, Complex.ofReal_tsum,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [term, Complex.cpow_natCast]
  push_cast
  rw [show (n : ℂ) + 3 / 4 = (4 * n + 3) / 4 by ring, div_pow]
  simp [div_eq_mul_inv, mul_comm]

private lemma riemann_series (s : ℕ) (hs : 1 < s) :
    riemannZeta s = ((∑' n, term s n : ℝ) : ℂ) := by
  rw [zeta_nat_eq_tsum_of_gt_one hs, Complex.ofReal_tsum]
  simp [term]

end hurwitzZeta_three_quarters_two_mul_add_one

open hurwitzZeta_three_quarters_two_mul_add_one

/-- **Hurwitz zeta at $3/4$ and odd arguments.** For every integer $k \ge 1$,
$$
\zeta(2k+1, \tfrac34) = -\frac{2^{2k-1} \pi^{2k+1} |E_{2k}|}{(2k)!} +
2^{2k} (2^{2k+1} - 1) \zeta(2k+1),
$$
where $\zeta(s, a)$ is the Hurwitz zeta function (for $\operatorname{Re} s > 1$,
$\zeta(s, a) = \sum_{n \ge 0} (n + a)^{-s}$), $\zeta(s)$ is the Riemann zeta function and $E_{2k}$
is the even-index Euler number.

The even-index Euler numbers are defined by a binomial recurrence equivalent to the generating
function $1 / \cosh t = \sum_n E_n t^n / n!$. The source writes $k \in \mathbb{N}$; $k = 0$ is
excluded since $s = 1$ is the pole of both zeta functions.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 3
(`jis-2025-25.4.4-lem-3`). -/
public theorem hurwitzZeta_three_quarters_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    HurwitzZeta.hurwitzZeta ((3 / 4 : ℝ) : UnitAddCircle) (2 * k + 1) =
      -((2 : ℂ) ^ (2 * k - 1) / (2 * k).factorial) * (Real.pi : ℂ) ^ (2 * k + 1) *
          ((|chapter5EulerEven k| : ℤ) : ℂ) +
        2 ^ (2 * k) * (2 ^ (2 * k + 1) - 1) * riemannZeta (2 * k + 1) := by
  let s := 2 * k + 1
  have hs : 1 < s := by dsimp [s]; omega
  rw [show (2 * (k : ℂ) + 1) = (s : ℂ) by simp [s], hurwitz_series s hs, riemann_series s hs]
  suffices h : (4 : ℝ) ^ s * progression s 3 =
      -(2 ^ (2 * k - 1) / (2 * k).factorial) * Real.pi ^ s * (|chapter5EulerEven k| : ℤ) +
        2 ^ (2 * k) * (2 ^ s - 1) * ∑' n, term s n by
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_intCast, Complex.ofReal_natCast,
      Complex.ofReal_one, Complex.ofReal_ofNat] using congrArg Complex.ofReal h
  have hsum := odd_sum hs
  have hdiff := odd_difference k hk
  change progression s 1 - progression s 3 = _ at hdiff
  have hthree : progression s 3 =
      ((1 - 1 / (2 : ℝ) ^ s) * (∑' n, term s n) -
        Real.pi ^ s * (|chapter5EulerEven k| : ℤ) /
          (2 * 2 ^ s * (2 * k).factorial)) / 2 := by
    linarith
  rw [hthree]
  have hfour : (4 : ℝ) ^ s = (2 ^ s) ^ 2 := by rw [sq, ← mul_pow]; norm_num
  have hpred : (2 : ℝ) ^ (2 * k - 1) * 2 = 2 ^ (2 * k) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  rw [hfour]
  dsimp only [s]
  simp only [pow_succ (2 : ℝ) (2 * k)]
  rw [← hpred]
  field_simp
  ring

open MathlibExt.Combinatorics.ReducedComplexitiesWanted
  (paperfoldingSeq paperfoldingSeq_even paperfoldingSeq_odd)

namespace tsum_neg_one_pow_paperfolding

-- The sequence index is one less than the denominator.
private noncomputable def signedTerm (s n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (paperfoldingSeq n).toNat * term s (n + 1)

private lemma summable_signedTerm {s : ℕ} (hs : 1 < s) : Summable (signedTerm s) := by
  apply Summable.of_norm
  refine ((Real.summable_one_div_nat_pow.mpr hs).comp_injective
    (i := fun n : ℕ => n + 1) (by intro a b h; dsimp at h; omega)).congr fun n => ?_
  change term s (n + 1) = ‖signedTerm s n‖
  have ht : 0 ≤ term s (n + 1) := by unfold term; positivity
  simp [signedTerm, Real.norm_eq_abs, abs_of_nonneg ht]

private lemma hasSum_even_index_signedTerm {s : ℕ} (hs : 1 < s) :
    HasSum (fun n => signedTerm s (2 * n)) (progression s 1 - progression s 3) := by
  have h₁ (n : ℕ) : signedTerm s (2 * (2 * n)) = term s (4 * n + 1) := by
    simp [signedTerm, paperfoldingSeq_even, show 2 * (2 * n) + 1 = 4 * n + 1 by omega]
  have h₃ (n : ℕ) : signedTerm s (2 * (2 * n + 1)) = -term s (4 * n + 3) := by
    simp [signedTerm, paperfoldingSeq_even, show 2 * (2 * n + 1) + 1 = 4 * n + 3 by omega]
  rw [sub_eq_add_neg]
  exact HasSum.even_add_odd ((summable_progression hs 1).hasSum.congr_fun h₁)
    ((summable_progression hs 3).hasSum.neg.congr_fun h₃)

private lemma hasSum_odd_index_signedTerm {s : ℕ} (hs : 1 < s) :
    HasSum (fun n => signedTerm s (2 * n + 1)) ((1 / (2 : ℝ) ^ s) * ∑' n, signedTerm s n) := by
  refine ((summable_signedTerm hs).hasSum.mul_left _).congr_fun fun n => ?_
  have hterm : term s (2 * (n + 1)) = (1 / (2 : ℝ) ^ s) * term s (n + 1) := by
    simp [term, mul_pow, mul_comm]
  simp only [signedTerm, paperfoldingSeq_odd, show 2 * n + 1 + 1 = 2 * (n + 1) by omega, hterm]
  ring

end tsum_neg_one_pow_paperfolding

open tsum_neg_one_pow_paperfolding

/-- **The $\pm 1$ paperfolding Dirichlet series at odd integers.** Let $(f_n)_{n \ge 0}$ be the
regular paperfolding sequence, indexed from $0$, and let $E_{2k}$ be the even-index Euler number.
For every integer $k \ge 1$,
$$
\sum_{n \ge 0} \frac{(-1)^{f_n}}{(n+1)^{2k+1}} =
\frac{\pi^{2k+1} |E_{2k}|}{(2^{2k+2} - 2)(2k)!}.
$$

In the source's indexing $b_n = f_{n-1}$ for $n \ge 1$, this is the sum over $n \ge 1$ of
$(-1)^{b_n}/n^{2k+1}$. The source prints the sum as $\sum_{n \ge 0} (-1)^{b_n}/(n+1)^{2k+1}$,
which uses $b_0$, left undetermined by the recurrence $b_{2n} = b_n$; its proof (from Lemma 5)
gives the sum over $n \ge 1$ stated here.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Corollary 7
(`jis-2025-25.4.4-cor-7`); `bₙ` read from arXiv:2508.04151v1. -/
public theorem tsum_neg_one_pow_paperfolding (k : ℕ) (hk : 1 ≤ k) :
    ∑' n : ℕ, (-1 : ℝ) ^ (paperfoldingSeq n).toNat / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) =
      Real.pi ^ (2 * k + 1) * ((|chapter5EulerEven k| : ℤ) : ℝ) /
        (((2 : ℝ) ^ (2 * k + 2) - 2) * (2 * k).factorial) := by
  let s := 2 * k + 1
  have hs : 1 < s := by dsimp [s]; omega
  have hsplit := (HasSum.even_add_odd (hasSum_even_index_signedTerm hs)
    (hasSum_odd_index_signedTerm hs)).tsum_eq
  let S : ℝ := ∑' n, signedTerm s n
  have hbalance : S - (1 / (2 : ℝ) ^ s) * S = progression s 1 - progression s 3 := by
    change S = (progression s 1 - progression s 3) + (1 / (2 : ℝ) ^ s) * S at hsplit
    linarith only [hsplit]
  have hpow : 1 < (2 : ℝ) ^ s := one_lt_pow₀ (by norm_num) (by omega)
  have hden : 0 < ((2 : ℝ) ^ s * 2 - 2) * (2 * k).factorial := by
    exact mul_pos (by linarith) (by positivity)
  -- This is the odd-residue difference used in the Hurwitz zeta evaluation above.
  have hdiff := (eq_div_iff (by positivity : (2 * (2 : ℝ) ^ s * (2 * k).factorial) ≠ 0)).mp
    (odd_difference k hk)
  trans S
  · exact tsum_congr fun n => div_eq_mul_one_div _ _
  rw [show (2 : ℝ) ^ (2 * k + 2) = 2 ^ s * 2 from pow_succ 2 s, eq_div_iff hden.ne']
  calc
    _ = (S - (1 / (2 : ℝ) ^ s) * S) * (2 * (2 : ℝ) ^ s * (2 * k).factorial) := by
      field_simp
    _ = _ := by rw [hbalance]; exact hdiff

end MetaMathlibExt
