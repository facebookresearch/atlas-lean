/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.Divisors

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Consecutive smooth integers in the upper half of an interval

We prove the location variant of Erdős Problem 369 using the cyclotomic construction
in [Bober–Fretwell–Martin–Wooley, §2](https://arxiv.org/html/1710.01970#S2).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.SmoothConsecutiveIntegersWanted

/-- **Erdős Problem 369, location variant.** This is the statement that for every real
$\varepsilon > 0$ and every natural number $k \ge 2$ there is a natural number $N$ such that for
every natural number $n \ge N$ there is a natural number $a$ with $\lfloor n/2 \rfloor \le a + 1$
and $a + k \le n$ for which every prime factor $p$ of each of the $k$ consecutive integers
$a + 1, \dots, a + k$ satisfies $p \le n^\varepsilon$.

Erdős Problem 369 as written allows the run anywhere in $\{1, \dots, n\}$, which is trivially
true (take $1, \dots, k$ once $n^\varepsilon \ge k$); here the run must start at or after
$\lfloor n/2 \rfloor$. -/
def conjecture : Prop :=
  ∀ ε : Real, 0 < ε →
    ∀ k : Nat, 2 ≤ k →
      ∃ N : Nat, ∀ n : Nat, N ≤ n →
        ∃ a : Nat, n / 2 ≤ a + 1 ∧ a + k ≤ n ∧
          ∀ j : Nat, j < k →
            ∀ p ∈ (a + 1 + j).primeFactors, (p : Real) ≤ (n : Real) ^ ε

open Filter Finset Polynomial
open scoped Topology

private lemma exists_small_totient_coprime (M : ℕ) (hM : 0 < M) {δ : ℝ} (hδ : 0 < δ) :
    ∃ d : ℕ, 0 < d ∧ d.Coprime M ∧ (d.totient : ℝ) < δ * d := by
  classical
  let f (p : ℕ) : ℝ := if p.Prime ∧ M < p then 1 / (p : ℝ) else 0
  have hf : ¬ Summable f := by
    intro hs
    apply not_summable_one_div_on_primes
    apply hs.congr_atTop
    filter_upwards [eventually_gt_atTop M] with p hp
    by_cases h : p.Prime <;> simp [f, h, hp]
  obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, -Real.log δ < ∑ p ∈ s, f p := by
    by_contra! h
    exact hf (summable_of_sum_le (fun p ↦ by unfold f; split <;> positivity) h)
  let t := s.filter fun p ↦ p.Prime ∧ M < p
  have ht : ∀ p ∈ t, p.Prime ∧ M < p := fun _ hp ↦ (mem_filter.mp hp).2
  have hsum : -Real.log δ < ∑ p ∈ t, 1 / (p : ℝ) := by
    simpa only [t, sum_filter, f] using hs
  let d := ∏ p ∈ t, p
  have hd : 0 < d := prod_pos fun p hp ↦ (ht p hp).1.pos
  have hcop : d.Coprime M := Nat.Coprime.prod_left fun p hp ↦
    (ht p hp).1.coprime_iff_not_dvd.mpr fun h ↦ (ht p hp).2.not_ge (Nat.le_of_dvd hM h)
  refine ⟨d, hd, hcop, (div_lt_iff₀ (by exact_mod_cast hd)).mp ?_⟩
  have hprod := Nat.totient_eq_mul_prod_factors d
  rw [show d.primeFactors = t from Nat.primeFactors_prod fun p hp ↦ (ht p hp).1] at hprod
  have hreal := congrArg (fun q : ℚ ↦ (q : ℝ)) hprod
  push_cast at hreal
  have hbound : (d.totient : ℝ) / d ≤ Real.exp (-(∑ p ∈ t, 1 / (p : ℝ))) := by
    rw [hreal, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hd.ne'),
      ← sum_neg_distrib, Real.exp_sum]
    refine prod_le_prod₀ (fun p hp ↦ ?_) (fun p _ ↦ ?_)
    · have hp' : 1 ≤ (p : ℝ) := by exact_mod_cast (ht p hp).1.one_le
      exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hp')
    · simpa [one_div, sub_eq_neg_add] using Real.add_one_le_exp (-(p : ℝ)⁻¹)
  exact hbound.trans_lt (by rw [← Real.exp_log hδ]; exact Real.exp_lt_exp.mpr (by linarith))

-- Each shift gets its own cyclotomic exponent, coprime to all the other exponents.
private lemma exists_small_totient_moduli {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ < 1) (k : ℕ) :
    ∃ d : Fin k → ℕ, Pairwise (fun i j ↦ (d i).Coprime (d j)) ∧
      ∀ i, 1 < d i ∧ ((d i).totient : ℝ) < δ * d i := by
  induction k with
  | zero => exact ⟨Fin.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0⟩
  | succ k ih =>
    obtain ⟨d, hcop, hsmall⟩ := ih
    obtain ⟨q, hq, hqcop, hqsmall⟩ := exists_small_totient_coprime (∏ i, d i)
      (prod_pos fun i _ ↦ zero_lt_one.trans (hsmall i).1) hδ
    have hq₁ : 1 < q := by
      by_contra! h
      have : q = 1 := by omega
      simp [this, hδ₁.not_gt] at hqsmall
    have hqcop' := Nat.coprime_prod_right_iff.mp hqcop
    refine ⟨Fin.cons q d, pairwise_fin_succ_iff.mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · intro i
      simpa using (hqcop' i (mem_univ i)).symm
    · intro i
      simpa using hqcop' i (mem_univ i)
    · simpa only [Fin.cons_succ] using hcop
    · exact Fin.cases ⟨hq₁, hqsmall⟩ hsmall

-- The Chinese remainder theorem makes the coefficient a multiple of each shift by a power.
private lemma exists_power_coefficient {k : ℕ} (d : Fin k → ℕ)
    (hd : ∀ i, 1 < d i) (hcop : Pairwise (fun i j ↦ (d i).Coprime (d j))) :
    ∃ B : ℕ, 0 < B ∧ ∀ i : Fin k, ∃ b : ℕ, 0 < b ∧ B = (i.val + 1) * b ^ d i := by
  classical
  let e (j : Fin k) := Nat.chineseRemainderOfFinset
    (fun i ↦ if j = i then 1 else 0) d univ
    (fun i _ ↦ (zero_lt_one.trans (hd i)).ne') (fun _ _ _ _ h ↦ hcop h)
  have he (j i : Fin k) : (e j : ℕ) % d i = if j = i then 1 else 0 := by
    have h := (e j).prop i (mem_univ i)
    change (e j : ℕ) % d i = _ % d i at h
    have hi := hd i
    have hlt : (if j = i then 1 else 0) < d i := by split <;> omega
    rwa [Nat.mod_eq_of_lt hlt] at h
  refine ⟨∏ j : Fin k, (j.val + 1) ^ (e j : ℕ), prod_pos (fun j _ ↦ by positivity), fun i ↦ ?_⟩
  refine ⟨∏ j : Fin k, (j.val + 1) ^ ((e j : ℕ) / d i), prod_pos (fun j _ ↦ by positivity), ?_⟩
  calc
    (∏ j : Fin k, (j.val + 1) ^ (e j : ℕ)) =
        ∏ j : Fin k, (j.val + 1) ^ (if j = i then 1 else 0) *
          ((j.val + 1) ^ ((e j : ℕ) / d i)) ^ d i := by
      apply prod_congr rfl
      intro j _
      rw [← pow_mul, mul_comm ((e j : ℕ) / d i), ← pow_add, ← he, Nat.mod_add_div]
    _ = _ := by
      rw [prod_mul_distrib, ← prod_pow]
      congr 1
      simp only [pow_ite, pow_one, pow_zero, prod_ite_eq', mem_univ, ite_true]

private lemma prime_le_of_dvd_pow_sub_one {d z p : ℕ} (hd : 0 < d) (hz : 1 < z)
    (hp : p.Prime) (hpd : p ∣ z ^ d - 1) : (p : ℝ) ≤ ((z : ℝ) + 1) ^ d.totient := by
  have hz' : 1 ≤ z ^ d := Nat.one_le_pow _ _ (by omega)
  have hdiv : (p : ℤ) ∣ (z : ℤ) ^ d - 1 := by
    exact_mod_cast hpd
  have hfactor := congrArg (Polynomial.eval (z : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hd ℤ)
  simp only [eval_prod, eval_sub, eval_pow, eval_X, eval_one] at hfactor
  rw [← hfactor] at hdiv
  obtain ⟨l, hl, hpl⟩ := ((Nat.prime_iff_prime_int.mp hp).dvd_finsetProd_iff _).mp hdiv
  have hpos := cyclotomic_pos' l (show (1 : ℤ) < z by exact_mod_cast hz)
  have hle := Int.le_of_dvd hpos hpl
  have hcast : (p : ℝ) ≤ (cyclotomic l ℝ).eval (z : ℝ) := by
    rw [show (z : ℝ) = (algebraMap ℤ ℝ) (z : ℤ) by simp, cyclotomic.eval_apply]
    change (p : ℝ) ≤ ↑((cyclotomic l ℤ).eval (z : ℤ))
    exact_mod_cast hle
  refine hcast.trans ((cyclotomic_eval_le_add_one_pow_totient (by exact_mod_cast hz) l).trans ?_)
  exact pow_le_pow_right₀ (le_add_of_nonneg_left (Nat.cast_nonneg z))
    (Nat.le_of_dvd (Nat.totient_pos.mpr hd) (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hl)))

-- For the sequence of endpoints, the ratio of successive values tends to one.
private lemma eventually_next_mul_pow_le (B D : ℕ) :
    ∀ᶠ t : ℕ in atTop, 2 * (B * (t + 1) ^ D) ≤ 3 * (B * t ^ D) := by
  have hlim : Tendsto (fun t : ℕ ↦ (1 + (t : ℝ)⁻¹) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds.add
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)) (a := (1 : ℝ))).pow D
  filter_upwards [hlim.eventually (eventually_lt_nhds (show (1 : ℝ) < 3 / 2 by norm_num)),
    eventually_gt_atTop 0] with t ht ht₀
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht₀
  have hx : (t : ℝ) * (1 + (t : ℝ)⁻¹) = (t : ℝ) + 1 := by
    rw [mul_add, mul_one, mul_inv_cancel₀ ht'.ne']
  have h := mul_le_mul_of_nonneg_left ht.le (show 0 ≤ (B : ℝ) * (t : ℝ) ^ D by positivity)
  have hnext : (B : ℝ) * ((t : ℝ) + 1) ^ D ≤ (B : ℝ) * (t : ℝ) ^ D * (3 / 2) := by
    simpa only [mul_assoc, ← mul_pow, hx] using h
  exact_mod_cast (show 2 * ((B : ℝ) * ((t : ℝ) + 1) ^ D) ≤ 3 * ((B : ℝ) * (t : ℝ) ^ D) by
    linarith only [hnext])

-- Once the exponent ratio is small, the remaining fixed factors are absorbed by the power bound.
private lemma eventually_prime_le_of_shift {k B D : ℕ} {δ ε : ℝ} (hB : 0 < B) (hD : 0 < D)
    (hδ : 0 < δ) (hδε : δ < ε) (d b : Fin k → ℕ) (hd : ∀ i, 1 < d i)
    (hdD : ∀ i, d i ∣ D) (hsmall : ∀ i, ((d i).totient : ℝ) ≤ δ * d i)
    (hb : ∀ i, 0 < b i) (hBbinom : ∀ i, B = (i.val + 1) * b i ^ d i) :
    ∀ᶠ t : ℕ in atTop, ∀ i : Fin k, ∀ p ∈ (B * t ^ D - (i.val + 1)).primeFactors,
      (p : ℝ) ≤ ((B * t ^ D : ℕ) : ℝ) ^ ε := by
  let m (t : ℕ) := B * t ^ D
  have hm : Tendsto m atTop atTop := (tendsto_pow_atTop hD.ne').const_mul_atTop' hB
  have hlim : Tendsto (fun t : ℕ ↦ (m t : ℝ) ^ (ε - δ)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hδε)).comp (tendsto_natCast_atTop_atTop.comp hm)
  filter_upwards [eventually_ge_atTop 2,
    hlim.eventually (eventually_ge_atTop (max (k : ℝ) ((2 : ℝ) ^ D)))] with t ht htC
  have hm₀ : 0 < m t := by dsimp [m]; positivity
  have hm₁ : (1 : ℝ) ≤ m t := by exact_mod_cast hm₀
  have hpower : (m t : ℝ) ^ (ε - δ) * (m t : ℝ) ^ δ = (m t : ℝ) ^ ε := by
    rw [← Real.rpow_add (by positivity), sub_add_cancel]
  intro i p hp
  let r := D / d i
  let z := b i * t ^ r
  have hrd : r * d i = D := Nat.div_mul_cancel (hdD i)
  have hr : r ≠ 0 := by
    intro he
    rw [he, zero_mul] at hrd
    exact hD.ne' hrd.symm
  have hz : 1 < z :=
    (show 1 < t from ht).trans_le ((Nat.le_self_pow hr t).trans
      (Nat.le_mul_of_pos_left _ (hb i)))
  have hfactor : m t = (i.val + 1) * z ^ d i := by
    dsimp only [m, z]
    rw [mul_pow, ← pow_mul, hrd, hBbinom i, mul_assoc]
  have hzsub : m t - (i.val + 1) = (i.val + 1) * (z ^ d i - 1) := by
    rw [hfactor, Nat.mul_sub, mul_one]
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hp
  rw [hzsub] at hpd
  change (p : ℝ) ≤ (m t : ℝ) ^ ε
  rw [← hpower]
  rcases hpp.dvd_mul.mp hpd with hpdiv | hpdiv
  · have hpk : (p : ℝ) ≤ k := by
      exact_mod_cast (Nat.le_of_dvd (Nat.succ_pos _) hpdiv).trans i.isLt
    calc
      (p : ℝ) ≤ (m t : ℝ) ^ (ε - δ) := hpk.trans ((le_max_left _ _).trans htC)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hm₁ hδ.le)
  have hdz : 0 < (d i : ℝ) := by exact_mod_cast (zero_lt_one.trans (hd i))
  have hzpow : (z : ℝ) ^ d i ≤ m t := by
    exact_mod_cast hfactor ▸ Nat.le_mul_of_pos_left _ (Nat.succ_pos i.val)
  have hratio : ((d i).totient : ℝ) / d i ≤ δ := (div_le_iff₀ hdz).mpr (hsmall i)
  have hroot : (z : ℝ) ^ (d i).totient =
      ((z : ℝ) ^ d i) ^ (((d i).totient : ℝ) / d i) := by
    rw [← Real.rpow_natCast (z : ℝ) (d i), ← Real.rpow_mul (Nat.cast_nonneg z),
      ← mul_div_assoc, mul_div_cancel_left₀ _ hdz.ne', Real.rpow_natCast]
  calc
    (p : ℝ) ≤ ((z : ℝ) + 1) ^ (d i).totient :=
      prime_le_of_dvd_pow_sub_one (zero_lt_one.trans (hd i)) hz hpp hpdiv
    _ ≤ (2 * (z : ℝ)) ^ (d i).totient := by
      have hz₁ : (1 : ℝ) ≤ z := by exact_mod_cast hz.le
      gcongr
      linarith
    _ = (2 : ℝ) ^ (d i).totient * (z : ℝ) ^ (d i).totient := mul_pow _ _ _
    _ ≤ (m t : ℝ) ^ (ε - δ) * (m t : ℝ) ^ δ := by
      apply mul_le_mul
      · have hdegree := (d i).totient_le.trans (Nat.le_of_dvd hD (hdD i))
        exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hdegree).trans
          ((le_max_right _ _).trans htC)
      · rw [hroot]
        exact (Real.rpow_le_rpow (by positivity) hzpow (by positivity)).trans
          (Real.rpow_le_rpow_of_exponent_le hm₁ hratio)
      · positivity
      · positivity

/--
**Solution of Erdős Problem 369, location variant.** For every real $\varepsilon > 0$ and every
natural number $k \ge 2$ there is a natural number $N$ such that for every natural number
$n \ge N$ there is a natural number $a$ with $\lfloor n/2 \rfloor \le a + 1$ and $a + k \le n$
for which every prime factor $p$ of each of the $k$ consecutive integers $a + 1, \dots, a + k$
satisfies $p \le n^\varepsilon$.

Source: Balog-Wooley 1998; Bober-Fretwell-Martin-Wooley 2020.

Source: Lean proof of
EP-369 location variant (plby/lean-proofs),
https://github.com/plby/lean-proofs/blob/1d7b3f00780b85ed0462e79a1cd5650ee9055655/src/v4.29.1/ErdosProblems/Erdos369.lean.
Moved from `OpenConjectures/NumberTheory/SmoothConsecutiveIntegers`.
-/
public theorem conjecture_holds : conjecture := by
  intro ε hε k hk
  obtain ⟨δ, hδ, hδmin⟩ := exists_between (lt_min hε zero_lt_one)
  have hδε := hδmin.trans_le (min_le_left _ _)
  obtain ⟨d, hcop, hsmall⟩ := exists_small_totient_moduli hδ
    (hδmin.trans_le (min_le_right _ _)) k
  obtain ⟨B, hB, hcoeff⟩ := exists_power_coefficient d (fun i ↦ (hsmall i).1) hcop
  choose b hb hBbinom using hcoeff
  let D := ∏ i, d i
  have hD : 0 < D := prod_pos fun i _ ↦ zero_lt_one.trans (hsmall i).1
  have hdD (i : Fin k) : d i ∣ D := dvd_prod_of_mem d (mem_univ i)
  let m (t : ℕ) := B * t ^ D
  have hm : Tendsto m atTop atTop :=
    (tendsto_pow_atTop hD.ne').const_mul_atTop' hB
  have hevent : ∀ᶠ t : ℕ in atTop, (4 * k + 4 ≤ m t ∧ 2 * m (t + 1) ≤ 3 * m t) ∧
      ∀ i : Fin k, ∀ p ∈ (m t - (i.val + 1)).primeFactors, (p : ℝ) ≤ (m t : ℝ) ^ ε :=
    ((hm.eventually (eventually_ge_atTop (4 * k + 4))).and (eventually_next_mul_pow_le B D)).and
      (eventually_prime_le_of_shift hB hD hδ hδε d b (fun i ↦ (hsmall i).1) hdD
        (fun i ↦ (hsmall i).2.le) hb hBbinom)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hevent
  refine ⟨m T, fun n hn ↦ ?_⟩
  obtain ⟨t, ht, htn, hnt⟩ := hm.exists_le_lt_succ hn
  obtain ⟨⟨hlarge, hnext⟩, hsmooth⟩ := hT t ht
  refine ⟨m t - (k + 1), by omega, by omega, fun j hj p hp ↦ ?_⟩
  let i : Fin k := ⟨k - 1 - j, by omega⟩
  have heq : m t - (k + 1) + 1 + j = m t - (i.val + 1) := by dsimp [i]; omega
  rw [heq] at hp
  exact (hsmooth i p hp).trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast htn) hε.le)

end MathlibExt.NumberTheory.SmoothConsecutiveIntegersWanted
