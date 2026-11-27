/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Binomial
import MathlibExt.NumberTheory.AlternatingChooseSums
import MathlibExt.NumberTheory.HigherOrderHarmonic
import MathlibExt.NumberTheory.WolstenholmeBinomialCongruence
import MathlibExt.NumberTheory.WolstenholmeBinomialExtension
import MathlibExt.NumberTheory.WolstenholmeCongruenceEquivalence

/-!
# Congruence form of the higher p-adic mean value theorem

`norm_sub_taylor_le_zpow_valuation` bounds a polynomial's Taylor remainder in an
ultrametric normed space over the p-adic numbers using the valuation of the step.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 2
(`integers-2026-A32-thm-2`).
-/

namespace MetaMathlibExt

private theorem factorial_valuation_le {p : ℕ} [Fact p.Prime] (q : ℕ) (hpq : p ≤ q) :
    multiplicity p q.factorial ≤ q - p + 1 := by
  have hp := (Fact.out : p.Prime).two_le
  have hq : q ≠ 0 := by omega
  have hv := sub_one_mul_multiplicity_factorial_lt_of_ne_zero p hq
  have hp' : p - 1 + 1 = p := by omega
  have hq' : q - p + p = q := Nat.sub_add_cancel hpq
  by_contra! h
  have hmul := Nat.mul_le_mul_left (p - 1) h
  nlinarith [Nat.zero_le ((p - 2) * (q - p))]

private theorem norm_div_factorial_le {p : ℕ} [Fact p.Prime] (h : ℚ_[p]) (m q : ℕ)
    (d : ℝ) (hh : h ≠ 0) (hv : 1 ≤ (h.valuation : ℝ)) (hmq : m ≤ q)
    (hf : (multiplicity p q.factorial : ℝ) ≤ (q : ℝ) - m + d) :
    ‖h ^ q / (q.factorial : ℚ_[p])‖ ≤
      (p : ℝ) ^ (-((m : ℝ) * h.valuation - d)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hn : (q.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  rw [norm_div, norm_pow, Padic.norm_eq_zpow_neg_valuation hh,
    Padic.norm_eq_zpow_neg_valuation hn, Padic.valuation_natCast,
    ← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hp.le, ← Real.rpow_sub hp]
  apply Real.rpow_le_rpow_of_exponent_le hp₁
  simp only [Int.cast_neg, Int.cast_natCast]
  have hmq' : (m : ℝ) ≤ q := by exact_mod_cast hmq
  nlinarith [mul_nonneg (sub_nonneg.mpr hmq') (sub_nonneg.mpr hv)]

private theorem taylor_term_eq {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] (j m q : ℕ) (hmq : m ≤ q)
    (t h : ℚ_[p]) (b : B) :
    ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • b =
      (t ^ (j - q) * (h ^ q / (q.factorial : ℚ_[p]))) •
        ((j - m).descFactorial (q - m) • (j.descFactorial m • b)) := by
  have hn : (q.factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  have hc : (q.factorial : ℚ_[p]) * (j.choose q : ℚ_[p]) =
      ((j - m).descFactorial (q - m) : ℚ_[p]) * (j.descFactorial m : ℚ_[p]) := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose j q).symm.trans
      (Nat.descFactorial_mul_descFactorial hmq).symm
  simp only [← Nat.cast_smul_eq_nsmul ℚ_[p], ← mul_smul]
  congr 1
  rw [← hc]
  field_simp [hn]

private theorem binomial_sum_eq {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] (K j : ℕ) (hj : j < K)
    (t h : ℚ_[p]) (b : B) :
    (t + h) ^ j • b =
      ∑ q ∈ Finset.range K, ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • b := by
  classical
  calc
    (t + h) ^ j • b =
        ∑ q ∈ Finset.range (j + 1),
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • b := by
      rw [add_comm t h, add_pow, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      ring
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega : j + 1 ≤ K))
      intro q _ hq
      simp only [Finset.mem_range] at hq
      have hjq : j < q := by omega
      simp [Nat.choose_eq_zero_of_lt hjq]

private theorem sub_taylor_eq_sum {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) :
    ∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j =
      ∑ j ∈ Finset.range N, ∑ q ∈ Finset.Ico m (N + m),
        ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j := by
  classical
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < N + m := by
    have := Finset.mem_range.mp hj
    omega
  rw [binomial_sum_eq (N + m) j hj' t h (a j),
    ← Finset.sum_Ico_eq_sub _ (by omega : m ≤ N + m)]

private theorem norm_taylor_term_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B]
    (j m q : ℕ) (t h : ℚ_[p]) (b : B) (w d : ℝ) (ht : ‖t‖ ≤ 1)
    (hh : h ≠ 0) (hv : 1 ≤ (h.valuation : ℝ)) (hmq : m ≤ q)
    (hf : (multiplicity p q.factorial : ℝ) ≤ (q : ℝ) - m + d)
    (hb : ‖j.descFactorial m • b‖ ≤ (p : ℝ) ^ (-w)) :
    ‖((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • b‖ ≤
      (p : ℝ) ^ (-((m : ℝ) * h.valuation + w - d)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [taylor_term_eq j m q hmq t h b, norm_smul, norm_mul]
  have hb' := (IsUltrametricDist.norm_nsmul_le (j.descFactorial m • b)
    ((j - m).descFactorial (q - m))).trans hb
  have ht' : ‖t ^ (j - q)‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg t) ht
  have hs : ‖t ^ (j - q)‖ * ‖h ^ q / (q.factorial : ℚ_[p])‖ ≤
      (p : ℝ) ^ (-((m : ℝ) * h.valuation - d)) := by
    simpa only [one_mul] using mul_le_mul ht'
      (norm_div_factorial_le h m q d hh hv hmq hf) (norm_nonneg _) zero_le_one
  calc
    _ ≤ (p : ℝ) ^ (-((m : ℝ) * h.valuation - d)) * (p : ℝ) ^ (-w) :=
      mul_le_mul hs hb' (norm_nonneg _) (Real.rpow_pos_of_pos hp _).le
    _ = _ := by
      rw [← Real.rpow_add hp]
      congr 1
      ring

private theorem norm_sub_taylor_le {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B]
    (N m : ℕ) (a : ℕ → B) (t h : ℚ_[p]) (w d : ℝ) (ht : ‖t‖ ≤ 1)
    (hv : 0 < (h.valuation : ℝ))
    (hf : ∀ q, m ≤ q → (multiplicity p q.factorial : ℝ) ≤ (q : ℝ) - m + d)
    (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ (p : ℝ) ^ (-w)) :
    ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖ ≤
      (p : ℝ) ^ (-((m : ℝ) * h.valuation + w - d)) := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hh : h ≠ 0 := by
    intro hh
    simp [hh] at hv
  have hv' : 1 ≤ h.valuation := by
    have : 0 < h.valuation := by exact_mod_cast hv
    omega
  have hv'' : 1 ≤ (h.valuation : ℝ) := by exact_mod_cast hv'
  rw [sub_taylor_eq_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Real.rpow_pos_of_pos hp _).le
  intro j hj
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (Real.rpow_pos_of_pos hp _).le
  intro q hq
  have hmq := (Finset.mem_Ico.mp hq).1
  exact norm_taylor_term_le j m q t h (a j) w d ht hh hv'' hmq (hf q hmq) (hC j hj)

private theorem factorial_valuation_bound {p : ℕ} [Fact p.Prime] (m q : ℕ)
    (hmp : m ≤ p) (hne : m ≠ p) (hmq : m ≤ q) :
    (multiplicity p q.factorial : ℝ) ≤ (q : ℝ) - m := by
  by_cases hqp : q < p
  · have hz : multiplicity p q.factorial = 0 :=
      multiplicity_eq_zero_of_not_dvd (fun hd =>
        (Nat.not_le.mpr hqp) ((Fact.out : p.Prime).dvd_factorial.mp hd))
    rw [hz, Nat.cast_zero]
    exact sub_nonneg.mpr (by exact_mod_cast hmq)
  · have hv := factorial_valuation_le q (by omega : p ≤ q)
    have hbound : multiplicity p q.factorial + m ≤ q := by omega
    have hbound' : (multiplicity p q.factorial : ℝ) + m ≤ q := by
      exact_mod_cast hbound
    linarith

@[expose] public section

/-- **Congruence form of the higher $p$-adic mean value theorem.** Let $p$ be a prime, let
$|\cdot|$ be the $p$-adic absolute value on $\mathbb{Q}_p$, and let $B$ be a normed vector space
over $\mathbb{Q}_p$ whose norm is ultrametric. Let $N$ and $m$ be natural numbers with
$1 \le m \le p$, let $f(t) = \sum_{j<N} a_j t^j$ with $a_j \in B$, let $t, h \in \mathbb{Q}_p$
with $|t| \le 1$, and let $w$ be a real number with
$\|j(j-1)\cdots(j-m+1) \, a_j\| \le p^{-w}$ for every $j < N$. Write
$$R = \Big\| f(t+h) - \sum_{q<m} \sum_{q \le j < N} \binom{j}{q} t^{j-q} h^q a_j \Big\|$$
and let $v_p(h)$ be the $p$-adic valuation of $h$, taken to be $0$ when $h = 0$. Then
$R \le p^{-(m v_p(h) + w)}$ if $m < p$ and $v_p(h) \ge 1/(p-m)$;
$R \le p^{-(p v_p(h) + w - 1)}$ if $m = p$ and $v_p(h) \ge 1/p$; and $R = 0$ if $h = 0$.

Reading a congruence modulo $p^v$ in $B$ as norm at most $p^{-v}$, the first two bounds say
$f(t+h) \equiv \sum_{q<m} f^{(q)}(t) h^q / q!$ modulo $p^{m v_p(h) + w}$ and
$p^{p v_p(h) + w - 1}$ respectively.

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Theorem 2
(`integers-2026-A32-thm-2`). -/
public theorem norm_sub_taylor_le_zpow_valuation {p : ℕ} [Fact p.Prime] {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℚ_[p] B] [IsUltrametricDist B] (N m : ℕ) (a : ℕ → B)
    (t h : ℚ_[p]) (w : ℝ) (ht : ‖t‖ ≤ 1) (hm : 1 ≤ m) (hmp : m ≤ p)
    (hC : ∀ j ∈ Finset.range N, ‖j.descFactorial m • a j‖ ≤ (p : ℝ) ^ (-w)) :
    let R : ℝ := ‖∑ j ∈ Finset.range N, (t + h) ^ j • a j -
        ∑ q ∈ Finset.range m, ∑ j ∈ Finset.range N,
          ((j.choose q : ℚ_[p]) * t ^ (j - q) * h ^ q) • a j‖
    (m < p → 1 / ((p : ℝ) - m) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((m : ℝ) * h.valuation + w))) ∧
      (m = p → 1 / (p : ℝ) ≤ h.valuation →
        R ≤ (p : ℝ) ^ (-((p : ℝ) * h.valuation + w - 1))) ∧
      (h = 0 → R = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro hmp' hv
    have hpden : 0 < (p : ℝ) - m := sub_pos.mpr (by exact_mod_cast hmp')
    have hv' : 0 < (h.valuation : ℝ) := (one_div_pos.mpr hpden).trans_le hv
    simpa only [sub_zero] using norm_sub_taylor_le N m a t h w 0 ht hv'
      (fun q hmq => by
        simpa only [add_zero] using factorial_valuation_bound m q hmp (ne_of_lt hmp') hmq)
      hC
  · intro hmp' hv
    subst m
    have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hv' : 0 < (h.valuation : ℝ) := (one_div_pos.mpr hp).trans_le hv
    apply norm_sub_taylor_le N p a t h w 1 ht hv' _ hC
    intro q hpq
    have hf := factorial_valuation_le q hpq
    have hf' : (multiplicity p q.factorial : ℝ) ≤ ((q - p : ℕ) : ℝ) + 1 := by
      exact_mod_cast hf
    simpa only [Nat.cast_sub hpq] using hf'
  · intro hh
    subst h
    rw [sub_taylor_eq_sum]
    have hz : (∑ j ∈ Finset.range N, ∑ q ∈ Finset.Ico m (N + m),
        ((j.choose q : ℚ_[p]) * t ^ (j - q) * (0 : ℚ_[p]) ^ q) • a j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro q hq
      have hmq := (Finset.mem_Ico.mp hq).1
      have hq' : q ≠ 0 := by omega
      simp [zero_pow hq']
    rw [hz, norm_zero]

end

end MetaMathlibExt
