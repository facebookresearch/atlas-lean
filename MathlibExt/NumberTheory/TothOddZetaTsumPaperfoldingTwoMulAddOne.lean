/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Combinatorics.ReducedComplexities
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.Analysis.Asymptotics.CatalanAsymptoticExpansion

/-!
# A paperfolding Dirichlet series at odd integers

We evaluate the Dirichlet series with regular-paperfolding coefficients at each odd integer
greater than one in terms of an even-index Euler number and a power of π.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 5 (`jis-2025-25.4.4-lem-5`);
`bₙ` read from arXiv:2508.04151v1.
-/

namespace MetaMathlibExt

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Combinatorics.ReducedComplexitiesWanted (paperfoldingSeq)

namespace tsum_paperfolding_two_mul_add_one

-- Extend the even-index sequence by zero at odd indices.
private lemma bernoulli_quarter (k : ℕ) :
    (Polynomial.bernoulli (2 * k + 1)).eval (1 / 4) =
      -(2 * k + 1 : ℚ) * chapter5EulerEven k / 4 ^ (2 * k + 1) := by
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

private noncomputable def term (s n : ℕ) : ℝ := 1 / (n : ℝ) ^ s

private noncomputable def progression (s r : ℕ) : ℝ := ∑' n, term s (4 * n + r)

private lemma summable_progression {s : ℕ} (hs : 1 < s) (r : ℕ) :
    Summable (fun n => term s (4 * n + r)) :=
  (Real.summable_one_div_nat_pow.mpr hs).comp_injective
    (i := fun n : ℕ => 4 * n + r) (by intro a b h; dsimp at h; omega)

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
      Polynomial.eval_map_apply, bernoulli_quarter]
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

private theorem paperfoldingSeq_even (j : ℕ) :
    paperfoldingSeq (2 * j) = decide (j % 2 = 1) := by
  have h : (2 * j + 1).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_remainder j (by decide)
  rw [Bool.eq_iff_iff]
  simp only [paperfoldingSeq, h, pow_zero, Nat.div_one, decide_eq_true_eq]
  omega

private theorem paperfoldingSeq_odd (j : ℕ) :
    paperfoldingSeq (2 * j + 1) = paperfoldingSeq j := by
  have hj1 : j + 1 ≠ 0 := by omega
  have hmul : (2 * (j + 1)).factorization 2 = (j + 1).factorization 2 + 1 := by
    rw [Nat.factorization_mul (by norm_num) hj1, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two]
    omega
  have h2j : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
  simp only [paperfoldingSeq, h2j, hmul, pow_add, pow_one]
  rw [show (2 : ℕ) ^ (j + 1).factorization 2 * 2 = 2 * 2 ^ (j + 1).factorization 2 by ring,
    Nat.mul_div_mul_left _ _ (by positivity)]

private noncomputable def pfterm (s n : ℕ) : ℝ :=
  (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ s

private lemma summable_pfterm {s : ℕ} (hs : 1 < s) : Summable (pfterm s) := by
  have hbase : Summable (fun n : ℕ => term s (n + 1)) :=
    (Real.summable_one_div_nat_pow.mpr hs).comp_injective
      (i := fun n : ℕ => n + 1) (by intro a b h; dsimp at h; omega)
  apply Summable.of_norm_bounded hbase
  intro n
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) ^ s := by positivity
  have habs : |2 * ((paperfoldingSeq n).toNat : ℝ) - 1| = 1 := by
    cases paperfoldingSeq n <;> norm_num [Bool.toNat_false, Bool.toNat_true]
  simp only [pfterm, term, Real.norm_eq_abs, abs_div]
  rw [habs, abs_of_pos hpos]

private lemma pfterm_odd (s j : ℕ) :
    pfterm s (2 * j + 1) = (1 / (2 : ℝ) ^ s) * pfterm s j := by
  have h2 : ((2 * j + 1 + 1 : ℕ) : ℝ) = 2 * ((j + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [pfterm, paperfoldingSeq_odd, h2, mul_pow]
  have h1 : ((j + 1 : ℕ) : ℝ) ^ s ≠ 0 := by positivity
  have h2s : (2 : ℝ) ^ s ≠ 0 := by positivity
  field_simp

private lemma pfterm_even_of_even (s t : ℕ) :
    pfterm s (2 * (2 * t)) = -term s (4 * t + 1) := by
  have hf : paperfoldingSeq (2 * (2 * t)) = false := by
    rw [paperfoldingSeq_even]
    simp
  have h41 : 2 * (2 * t) + 1 = 4 * t + 1 := by omega
  simp only [pfterm, term, hf, Bool.toNat_false, Nat.cast_zero, mul_zero, zero_sub, h41,
    neg_div]

private lemma pfterm_even_of_odd (s t : ℕ) :
    pfterm s (2 * (2 * t + 1)) = term s (4 * t + 3) := by
  have hf : paperfoldingSeq (2 * (2 * t + 1)) = true := by
    rw [paperfoldingSeq_even]
    simp [(by omega : (2 * t + 1) % 2 = 1)]
  have h43 : 2 * (2 * t + 1) + 1 = 4 * t + 3 := by omega
  simp only [pfterm, term, hf, Bool.toNat_true, Nat.cast_one, mul_one, h43]
  norm_num

private lemma pfterm_split (s : ℕ) (hs : 1 < s) :
    ∑' n, pfterm s n =
      (progression s 3 - progression s 1) + (1 / (2 : ℝ) ^ s) * ∑' n, pfterm s n := by
  have hS : Summable (pfterm s) := summable_pfterm hs
  have hSeven : Summable (fun j => pfterm s (2 * j)) :=
    hS.comp_injective (i := fun j : ℕ => 2 * j) (by intro a b h; dsimp at h; omega)
  have hSodd : Summable (fun j => pfterm s (2 * j + 1)) :=
    hS.comp_injective (i := fun j : ℕ => 2 * j + 1) (by intro a b h; dsimp at h; omega)
  have hsplit := tsum_even_add_odd hSeven hSodd
  have hodd : (∑' j, pfterm s (2 * j + 1)) = (1 / (2 : ℝ) ^ s) * ∑' n, pfterm s n := by
    calc (∑' j, pfterm s (2 * j + 1)) = ∑' j, (1 / (2 : ℝ) ^ s) * pfterm s j :=
            tsum_congr fun j => pfterm_odd s j
      _ = (1 / (2 : ℝ) ^ s) * ∑' n, pfterm s n := tsum_mul_left
  have heven : (∑' j, pfterm s (2 * j)) = progression s 3 - progression s 1 := by
    have h1 : Summable (fun t => pfterm s (2 * (2 * t))) :=
      hSeven.comp_injective (i := fun t : ℕ => 2 * t) (by intro a b h; dsimp at h; omega)
    have h2 : Summable (fun t => pfterm s (2 * (2 * t + 1))) :=
      hSeven.comp_injective (i := fun t : ℕ => 2 * t + 1) (by intro a b h; dsimp at h; omega)
    have hsplit2 := tsum_even_add_odd (f := fun j => pfterm s (2 * j)) h1 h2
    have e1 : (∑' t, pfterm s (2 * (2 * t))) = -progression s 1 := by
      calc (∑' t, pfterm s (2 * (2 * t))) = ∑' t, -term s (4 * t + 1) :=
              tsum_congr fun t => pfterm_even_of_even s t
        _ = -∑' t, term s (4 * t + 1) := tsum_neg
        _ = -progression s 1 := rfl
    have e2 : (∑' t, pfterm s (2 * (2 * t + 1))) = progression s 3 := by
      calc (∑' t, pfterm s (2 * (2 * t + 1))) = ∑' t, term s (4 * t + 3) :=
              tsum_congr fun t => pfterm_even_of_odd s t
        _ = progression s 3 := rfl
    rw [e1, e2] at hsplit2
    linarith [hsplit2]
  rw [heven, hodd] at hsplit
  exact hsplit.symm

end tsum_paperfolding_two_mul_add_one

open tsum_paperfolding_two_mul_add_one

/-- **A paperfolding Dirichlet series at odd integers.** Let $(f_n)_{n \ge 0}$ be the regular
paperfolding sequence, indexed from $0$, and let $E_{2k}$ be the even-index Euler number. For
every integer $k \ge 1$,
$$
(2^{4k+1} - 2^{2k}) \sum_{n \ge 0} \frac{2 f_n - 1}{(n+1)^{2k+1}}
= -\frac{2^{2k-1} \pi^{2k+1} |E_{2k}|}{(2k)!}.
$$

In the source's indexing $b_n = f_{n-1}$ for $n \ge 1$, the sum is
$\sum_{n \ge 1} (2 b_n - 1)/n^{2k+1}$.

Source: László Tóth, *Evaluating ζ(s) at Odd Positive Integers Using Automatic Dirichlet
Series*, Journal of Integer Sequences 28 (2025), Article 25.4.4, Lemma 5 (`jis-2025-25.4.4-lem-5`);
`bₙ` read from arXiv:2508.04151v1. -/
public theorem tsum_paperfolding_two_mul_add_one (k : ℕ) (hk : 1 ≤ k) :
    ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) *
        ∑' n : ℕ, (2 * ((paperfoldingSeq n).toNat : ℝ) - 1) / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 1) =
      -((2 : ℝ) ^ (2 * k - 1) / (2 * k).factorial) * Real.pi ^ (2 * k + 1) *
        ((|chapter5EulerEven k| : ℤ) : ℝ) := by
  let s := 2 * k + 1
  have hs : 1 < s := by dsimp [s]; omega
  have hsplit := pfterm_split s hs
  have hdiff := odd_difference k hk
  change progression s 1 - progression s 3 = _ at hdiff
  change ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k)) * ∑' n, pfterm s n =
    -((2 : ℝ) ^ (2 * k - 1) / (2 * k).factorial) * Real.pi ^ s *
      ((|chapter5EulerEven k| : ℤ) : ℝ)
  have h2s0 : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hkey : ((2 : ℝ) ^ s - 1) * ∑' n, pfterm s n
      = (2 : ℝ) ^ s * (progression s 3 - progression s 1) := by
    field_simp at hsplit ⊢
    linear_combination hsplit
  have hC : ((2 : ℝ) ^ (4 * k + 1) - 2 ^ (2 * k))
      = 2 ^ (2 * k) * ((2 : ℝ) ^ s - 1) := by
    have hs_eq : s = 2 * k + 1 := rfl
    rw [hs_eq, show 4 * k + 1 = 2 * k + (2 * k + 1) by omega, pow_add]
    ring
  have hD : progression s 3 - progression s 1
      = -(progression s 1 - progression s 3) := by ring
  have hpred : (2 : ℝ) ^ (2 * k - 1) * 2 = 2 ^ (2 * k) := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  conv_lhs => rw [hC, mul_assoc, hkey, hD, hdiff]
  dsimp only [s]
  simp only [pow_succ (2 : ℝ) (2 * k)]
  rw [← hpred]
  field_simp

end MetaMathlibExt
