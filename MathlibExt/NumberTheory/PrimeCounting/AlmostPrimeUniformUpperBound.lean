/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.LandauAlmostPrimeAsymptotic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.DivisorSummatoryBound
import MathlibExt.NumberTheory.ArithmeticFunction.PrimePowerValues

/-!
# The Erdős–Sárközy bound for almost primes

For every natural number `k ≥ 1` and every real `t ≥ 1`, the number of positive integers up to
`t` with exactly `k + 1` prime factors counted with multiplicity is at most an absolute constant
times `k⁴ t log t / 2ᵏ`. We split off the power of two and majorize the weighted count of odd
integers by a convolution of the divisor-counting function with a kernel supported on odd
squareful integers (including `1`).

## References

* Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
  INTEGERS 24 (2024), Article A99, pp. 1–17, Lemma 3.
* P. Erdős and A. Sárközy, *On the number of prime factors of integers*, Acta Sci. Math.
  (Szeged) 42 (1980), pp. 237–246, Theorem 1, bound (17). The proof here uses a different
  divisor-counting majorant on the odd part.
* The kernel uses `ArithmeticFunction.ofPrimePowerValues` from
  `MathlibExt.NumberTheory.ArithmeticFunction.PrimePowerValues`.
-/

namespace MetaMathlibExt

open ArithmeticFunction Finset Nat
open scoped ArithmeticFunction.Omega

/-- Local coefficients of a nonnegative majorant: keep repeated odd prime factors only. -/
private noncomputable def oddKernelCoeff (p a : ℕ) : ℝ :=
  if a = 0 then 1 else if p ≠ 2 ∧ 2 ≤ a then 2 ^ a else 0

private noncomputable def oddKernel : ArithmeticFunction ℝ :=
  ofPrimePowerValues oddKernelCoeff

private theorem oddKernel_multiplicative : oddKernel.IsMultiplicative :=
  isMultiplicative_ofPrimePowerValues oddKernelCoeff

private theorem oddKernel_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    oddKernel (p ^ a) = oddKernelCoeff p a := by
  obtain rfl | ha := eq_or_ne a 0
  · simp [oddKernel_multiplicative.map_one, oddKernelCoeff]
  · exact ofPrimePowerValues_prime_pow oddKernelCoeff hp ha

private theorem oddKernel_nonneg (n : ℕ) : 0 ≤ oddKernel n := by
  by_cases hn : n = 0
  · simp [hn]
  rw [oddKernel, ofPrimePowerValues_apply_of_ne_zero _ hn]
  exact Finset.prod_nonneg fun p _ => by
    unfold oddKernelCoeff
    split_ifs <;> positivity

/-- On odd integers, the divisor count supplies the weight at exponent one, and the
kernel supplies it at all higher exponents. -/
private theorem pow_omega_le_convolution {n : ℕ} (hn : n ≠ 0) (hodd : ¬ 2 ∣ n) :
    (2 : ℝ) ^ Ω n ≤ (oddKernel * (sigma 0 : ArithmeticFunction ℝ)) n := by
  have hmul := oddKernel_multiplicative.mul (isMultiplicative_sigma (k := 0)).natCast
    (R := ℝ)
  rw [hmul.multiplicative_factorization _ hn, cardFactors_eq_sum_factorization]
  simp only [Finsupp.sum, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun he => hodd (he ▸ Nat.dvd_of_mem_primeFactors hp)
  let a := n.factorization p
  have ha : a ≠ 0 := Finsupp.mem_support_iff.mp hp
  change (2 : ℝ) ^ a ≤ (oddKernel * (sigma 0 : ArithmeticFunction ℝ)) (p ^ a)
  rw [ArithmeticFunction.mul_apply]
  have hnonneg (i : ℕ × ℕ) :
      0 ≤ oddKernel i.1 * ((sigma 0 i.2 : ℕ) : ℝ) :=
    mul_nonneg (oddKernel_nonneg _) (Nat.cast_nonneg _)
  rcases eq_or_ne a 1 with ha1 | ha1
  · rw [ha1, pow_one, pow_one]
    have hm : (1, p) ∈ p.divisorsAntidiagonal := by
      simp [Nat.mem_divisorsAntidiagonal, pp.ne_zero]
    have hs : sigma 0 p = 2 := by
      simpa only [pow_one] using sigma_zero_apply_prime_pow (i := 1) pp
    simpa [oddKernel_multiplicative.map_one, hs] using
      (Finset.single_le_sum (fun i _ => hnonneg i) hm)
  · have ha2 : 2 ≤ a := by omega
    have hm : (p ^ a, 1) ∈ (p ^ a).divisorsAntidiagonal := by
      simp [Nat.mem_divisorsAntidiagonal, pp.ne_zero]
    simpa [oddKernel_prime_pow pp, oddKernelCoeff, ha, hp2, ha2] using
      (Finset.single_le_sum (fun i _ => hnonneg i) hm)

private noncomputable def kernelTerm (n : ℕ) : ℝ := oddKernel n / n

private theorem kernelTerm_nonneg (n : ℕ) : 0 ≤ kernelTerm n :=
  div_nonneg (oddKernel_nonneg _) (Nat.cast_nonneg _)

/-- For each prime, the reciprocal-weighted tail starts at exponent two and is
bounded by a geometric series of ratio at most `2 / 3`. -/
private theorem kernelTerm_prime_series {p : ℕ} (hp : p.Prime) :
    Summable (fun a : ℕ => kernelTerm (p ^ a)) ∧
      ∑' a : ℕ, kernelTerm (p ^ a) ≤ 1 + 12 / (p : ℝ) ^ 2 := by
  have htail (a : ℕ) : kernelTerm (p ^ (a + 2)) ≤
      (4 / (p : ℝ) ^ 2) * (2 / 3) ^ a := by
    rw [kernelTerm, oddKernel_prime_pow hp, oddKernelCoeff, ite_eq_right (by omega), Nat.cast_pow]
    split_ifs with he
    · have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hp.two_le; omega)
      have hr : (2 : ℝ) / p ≤ 2 / 3 := by gcongr
      rw [← div_pow, pow_add, div_pow (2 : ℝ) _ 2, mul_comm]
      norm_num
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hr _) (by positivity)
    · simp only [zero_div]
      positivity
  have hgeo := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (2 / 3 : ℝ) < 1)).mul_left (4 / (p : ℝ) ^ 2)
  have hsumTail : Summable (fun a : ℕ => kernelTerm (p ^ (a + 2))) :=
    Summable.of_nonneg_of_le (fun a => kernelTerm_nonneg (p ^ (a + 2))) htail hgeo
  have hsum : Summable (fun a : ℕ => kernelTerm (p ^ a)) :=
    (summable_nat_add_iff 2).mp hsumTail
  refine ⟨hsum, ?_⟩
  rw [← hsum.sum_add_tsum_nat_add 2]
  have hb := hsumTail.tsum_le_tsum htail hgeo
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
    (by norm_num : (2 / 3 : ℝ) < 1)] at hb
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one]
  rw [show kernelTerm 1 = 1 by simp [kernelTerm, oddKernel_multiplicative.map_one],
    show kernelTerm p = 0 by
      have hp1 : oddKernel p = 0 := by simpa [oddKernelCoeff] using oddKernel_prime_pow hp 1
      simp [kernelTerm, hp1]]
  linarith only [hb, show (4 / (p : ℝ) ^ 2) * (1 - 2 / 3)⁻¹ = 12 / (p : ℝ) ^ 2 by ring]

/-- The reciprocal-weighted kernel has bounded partial sums by finite Euler products. -/
private theorem kernelTerm_partial_sum_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, kernelTerm n ≤ Real.exp (∑' n : ℕ, 12 / (n : ℝ) ^ 2) := by
  have hone : kernelTerm 1 = 1 := by simp [kernelTerm, oddKernel_multiplicative.map_one]
  have hmul {m n : ℕ} (h : m.Coprime n) :
      kernelTerm (m * n) = kernelTerm m * kernelTerm n := by
    rw [kernelTerm, kernelTerm, kernelTerm, oddKernel_multiplicative.map_mul_of_coprime h,
      Nat.cast_mul]
    exact (div_mul_div_comm (oddKernel m) (m : ℝ) (oddKernel n) (n : ℝ)).symm
  let s := Ioc 0 N
  have hf := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum hone
    (@hmul) (fun {p} hp => by
      simpa only [Real.norm_of_nonneg (kernelTerm_nonneg _)] using
        (kernelTerm_prime_series hp).1) s
  let e : (n : ℕ) → n ∈ s → Nat.factoredNumbers s := fun n hn =>
    ⟨n, Nat.mem_factoredNumbers_of_primeFactors_subset (mem_Ioc.mp hn).1.ne'
      (fun p hp => mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).pos,
        (Nat.le_of_dvd (mem_Ioc.mp hn).1 (Nat.dvd_of_mem_primeFactors hp)).trans
          (mem_Ioc.mp hn).2⟩)⟩
  classical
  let emb : (↥s) ↪ Nat.factoredNumbers s :=
    ⟨fun n => e n.1 n.2, fun _ _ h =>
      Subtype.ext (congrArg (fun x : Nat.factoredNumbers s => x.val) h)⟩
  let u := s.attach.map emb
  calc
    _ = ∑ n ∈ u, kernelTerm n := by
      change _ = ∑ n ∈ s.attach.map emb, kernelTerm n
      rw [Finset.sum_map]
      exact (Finset.sum_attach s kernelTerm).symm
    _ ≤ ∑' n : Nat.factoredNumbers s, kernelTerm n :=
      hf.2.summable.sum_le_tsum u (fun n _ => kernelTerm_nonneg n)
    _ = ∏ p ∈ s with p.Prime, ∑' a : ℕ, kernelTerm (p ^ a) := hf.2.tsum_eq
    _ ≤ ∏ p ∈ s with p.Prime, Real.exp (12 / (p : ℝ) ^ 2) := by
      refine Finset.prod_le_prod₀ (fun p _ => tsum_nonneg fun _ => kernelTerm_nonneg _) ?_
      intro p hp
      exact (kernelTerm_prime_series (mem_filter.mp hp).2).2.trans (by
        simpa [add_comm] using Real.add_one_le_exp (12 / (p : ℝ) ^ 2))
    _ ≤ _ := by
      rw [← Real.exp_sum]
      apply Real.exp_le_exp.mpr
      have hs : Summable (fun p : ℕ => 12 / (p : ℝ) ^ 2) := by
        simpa [div_eq_mul_inv] using
          (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ))).mul_left 12
      exact hs.sum_le_tsum _ (fun p _ => by positivity)

private theorem quotient_log_mul_le {N n : ℕ} (hn : n ∈ Ioc 0 N) :
    ((N / n : ℕ) : ℝ) * (1 + Real.log (N / n : ℕ)) ≤
      ((N : ℝ) / n) * (1 + Real.log N) := by
  obtain ⟨hn0, hnN⟩ := mem_Ioc.mp hn
  have hq : 0 < N / n := Nat.div_pos hnN hn0
  have hqR : (0 : ℝ) < ((N / n : ℕ) : ℝ) := by exact_mod_cast hq
  have hqN : ((N / n : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N n
  have hlogq : 0 ≤ Real.log (N / n : ℕ) := Real.log_nonneg (by exact_mod_cast hq)
  exact mul_le_mul Nat.cast_div_le (add_le_add_right (Real.log_le_log hqR hqN) 1)
    (by positivity) (by positivity)

private noncomputable def oddWeight : ArithmeticFunction ℝ :=
  ⟨fun n => if 2 ∣ n then 0 else 2 ^ Ω n, by simp⟩

private theorem oddWeight_nonneg (n : ℕ) : 0 ≤ oddWeight n := by
  change 0 ≤ if 2 ∣ n then 0 else (2 : ℝ) ^ Ω n
  split_ifs <;> positivity

private theorem oddWeight_sum_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, oddWeight n ≤
      Real.exp (∑' n : ℕ, 12 / (n : ℝ) ^ 2) * (N : ℝ) * (1 + Real.log N) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, (oddKernel * (sigma 0 : ArithmeticFunction ℝ)) n := by
      apply Finset.sum_le_sum
      intro n hn
      change (if 2 ∣ n then 0 else (2 : ℝ) ^ Ω n) ≤ _
      split_ifs with h
      · rw [ArithmeticFunction.mul_apply]
        exact Finset.sum_nonneg fun i _ => mul_nonneg (oddKernel_nonneg _) (Nat.cast_nonneg _)
      · exact pow_omega_le_convolution (mem_Ioc.mp hn).1.ne' h
    _ = ∑ n ∈ Ioc 0 N, oddKernel n * ∑ m ∈ Ioc 0 (N / n), ((sigma 0 m : ℕ) : ℝ) :=
      sum_Ioc_mul_eq_sum_sum ..
    _ ≤ ∑ n ∈ Ioc 0 N, kernelTerm n * ((N : ℝ) * (1 + Real.log N)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [show kernelTerm n * ((N : ℝ) * (1 + Real.log N)) =
          oddKernel n * ((N : ℝ) / n * (1 + Real.log N)) by unfold kernelTerm; ring]
      apply mul_le_mul_of_nonneg_left _ (oddKernel_nonneg n)
      have hτ := sum_tau_le (N / n)
      rw [show Icc 1 (N / n) = Ioc 0 (N / n) from Icc_add_one_left_eq_Ioc 0 _] at hτ
      simpa only [sigma_zero_apply] using hτ.trans (quotient_log_mul_le hn)
    _ = (∑ n ∈ Ioc 0 N, kernelTerm n) * ((N : ℝ) * (1 + Real.log N)) := Finset.sum_mul .. |>.symm
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right (kernelTerm_partial_sum_le _)
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
        positivity

/-- The even part contributes its value when it is a power of two with exponent at most `k`. -/
private noncomputable def powTwoWeight (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 2 ^ Ω n ∧ Ω n ≤ k then n else 0, by simp⟩

private theorem powTwoWeight_nonneg (k n : ℕ) : 0 ≤ powTwoWeight k n := by
  change 0 ≤ if n = 2 ^ Ω n ∧ Ω n ≤ k then (n : ℝ) else 0
  split_ifs <;> positivity

private theorem powTwoWeight_quotient_sum_le (k N : ℕ) :
    ∑ n ∈ Ioc 0 N, powTwoWeight k n / n ≤ (k : ℝ) + 1 := by
  let s := (Ioc 0 N).filter fun n => n = 2 ^ Ω n ∧ Ω n ≤ k
  have hcard : s.card ≤ (range (k + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => Ω n) ?_ ?_
    · intro n hn
      exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hn).2.2)
    · intro n hn m hm h
      change Ω n = Ω m at h
      rw [(mem_filter.mp hn).2.1, (mem_filter.mp hm).2.1, h]
  calc
    _ = (s.card : ℝ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.mp hn).1.ne'
      change (if n = 2 ^ Ω n ∧ Ω n ≤ k then (n : ℝ) else 0) / n =
        if n = 2 ^ Ω n ∧ Ω n ≤ k then ((1 : ℕ) : ℝ) else 0
      split_ifs <;> simp only [Nat.cast_one, div_self hn0, zero_div]
    _ ≤ _ := by simpa using (Nat.cast_le (α := ℝ)).mpr hcard

private theorem almostPrimeCounting_nat_bound (k N : ℕ) :
    (almostPrimeCounting k N : ℝ) * 2 ^ k ≤
      Real.exp (∑' n : ℕ, 12 / (n : ℝ) ^ 2) * ((k : ℝ) + 1) * N * (1 + Real.log N) := by
  let C := Real.exp (∑' n : ℕ, 12 / (n : ℝ) ^ 2)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  calc
    _ = ∑ n ∈ (Ioc 0 N).filter (Nat.IsAlmostPrime k), (2 : ℝ) ^ k := by
      rw [almostPrimeCounting_eq_card_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Ioc 0 N, (powTwoWeight k * oddWeight) n := by
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro n hn
      rw [ArithmeticFunction.mul_apply]
      have hnn (i : ℕ × ℕ) : 0 ≤ powTwoWeight k i.1 * oddWeight i.2 :=
        mul_nonneg (powTwoWeight_nonneg _ _) (oddWeight_nonneg _)
      split_ifs with h
      · let d := ordProj[2] n
        let m := ordCompl[2] n
        have hd : d * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
        have hmem : (d, m) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨hd, h.1⟩
        have hdΩ : Ω d = n.factorization 2 := cardFactors_apply_prime_pow Nat.prime_two
        have hΩ := cardFactors_mul (Nat.ordProj_pos n 2).ne' (Nat.ordCompl_pos 2 h.1).ne'
        change Ω (d * m) = Ω d + Ω m at hΩ
        rw [hd, h.2] at hΩ
        have hdW : powTwoWeight k d = d := by
          change (if d = 2 ^ Ω d ∧ Ω d ≤ k then (d : ℝ) else 0) = d
          rw [ite_eq_left ⟨by rw [hdΩ], by omega⟩]
        have hmW : oddWeight m = (2 : ℝ) ^ Ω m := by
          simp [oddWeight, m, Nat.not_dvd_ordCompl Nat.prime_two h.1]
        refine (le_of_eq ?_).trans (Finset.single_le_sum (fun i _ => hnn i) hmem)
        change (2 : ℝ) ^ k = powTwoWeight k d * oddWeight m
        rw [hdW, hmW, hΩ, pow_add, hdΩ]
        simp [d]
      · exact Finset.sum_nonneg fun i _ => hnn i
    _ = ∑ n ∈ Ioc 0 N, powTwoWeight k n * ∑ m ∈ Ioc 0 (N / n), oddWeight m :=
      sum_Ioc_mul_eq_sum_sum ..
    _ ≤ ∑ n ∈ Ioc 0 N, (powTwoWeight k n / n) * (C * N * (1 + Real.log N)) := by
      apply Finset.sum_le_sum
      intro n hn
      have heq : (powTwoWeight k n / n) * (C * N * (1 + Real.log N)) =
          powTwoWeight k n * (C * ((N : ℝ) / n) * (1 + Real.log N)) := by ring
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (powTwoWeight_nonneg _ _)
      refine (oddWeight_sum_le (N / n)).trans ?_
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (quotient_log_mul_le hn) hC
    _ = (∑ n ∈ Ioc 0 N, powTwoWeight k n / n) * (C * N * (1 + Real.log N)) :=
      (Finset.sum_mul ..).symm
    _ ≤ _ := by
      have heq : C * ((k : ℝ) + 1) * N * (1 + Real.log N) =
          ((k : ℝ) + 1) * (C * N * (1 + Real.log N)) := by ring
      rw [heq]
      apply mul_le_mul_of_nonneg_right (powTwoWeight_quotient_sum_le _ _)
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN)
        positivity

/-- **Erdős–Sárközy bound for almost primes.** There is a real constant $C$ such that for every
integer $k \ge 1$ and every real $t \ge 1$, the number $\pi_{k+1}(t)$ of integers $n$ with
$1 \le n \le t$ that have exactly $k + 1$ prime factors, counted with multiplicity, satisfies
$\pi_{k+1}(t) \le C \cdot \frac{k^4}{2^k} \, t \log t$.

Source: Paul Kinlaw, Megan Triplett, and William Tripp, *Almost Primes of Almost Prime Index*,
INTEGERS 24 (2024), Article A99, Lemma 3 (quoting Erdős and Sárközy) (`integers-2024-A99-lem-3`). -/
public theorem almostPrime_count_le_erdos_sarkozy :
    ∃ C : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, 1 ≤ t →
      (almostPrimeCounting (k + 1) ⌊t⌋₊ : ℝ) ≤
        C * ((k : ℝ) ^ 4 / 2 ^ k) * t * Real.log t := by
  let A := Real.exp (∑' n : ℕ, 12 / (n : ℝ) ^ 2)
  have hA : 0 ≤ A := (Real.exp_pos _).le
  refine ⟨3 * A * (1 + (Real.log 2)⁻¹), fun k hk t ht => ?_⟩
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  by_cases ht2 : 2 ≤ t
  · let N := ⌊t⌋₊
    have hN : (1 : ℕ) ≤ N := Nat.le_floor (by exact_mod_cast ht)
    have hNt : (N : ℝ) ≤ t := Nat.floor_le (by positivity)
    have hlogN : Real.log (N : ℝ) ≤ Real.log t :=
      Real.log_le_log (by exact_mod_cast hN) hNt
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hscale : 1 + Real.log t ≤ (1 + (Real.log 2)⁻¹) * Real.log t := by
      have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) ht2
      have ht' := (le_div_iff₀ hlog2).mpr (by simpa using h : 1 * Real.log 2 ≤ Real.log t)
      linarith only [ht', show (1 + (Real.log 2)⁻¹) * Real.log t =
        Real.log t + Real.log t / Real.log 2 by ring]
    have hk4 : (k : ℝ) ≤ (k : ℝ) ^ 4 := by
      simpa using pow_le_pow_right₀ hkR (show 1 ≤ (4 : ℕ) by decide)
    have hk2 : (k : ℝ) + 2 ≤ 3 * (k : ℝ) ^ 4 := by linarith
    have hmono := almostPrimeCounting_nat_bound (k + 1) N
    push_cast at hmono
    have hbound : (almostPrimeCounting (k + 1) N : ℝ) * 2 ^ (k + 1) ≤
        A * (3 * (k : ℝ) ^ 4) * t * ((1 + (Real.log 2)⁻¹) * Real.log t) := by
      refine hmono.trans ?_
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hk2]) hA)
        hNt (Nat.cast_nonneg _) (by positivity)) ((add_le_add_right hlogN 1).trans hscale)
        (by have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast hN); positivity)
        (by positivity)
    calc
      _ ≤ (A * (3 * (k : ℝ) ^ 4) * t * ((1 + (Real.log 2)⁻¹) * Real.log t)) / 2 ^ k := by
        apply (le_div_iff₀ (by positivity)).2
        refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) hbound
        rw [pow_succ]
        linarith only [show (0 : ℝ) ≤ 2 ^ k by positivity]
      _ = _ := by ring
  · have hN : ⌊t⌋₊ < 2 := (Nat.floor_lt (by positivity)).mpr (by exact_mod_cast lt_of_not_ge ht2)
    have hs : (Ioc 0 ⌊t⌋₊).filter (Nat.IsAlmostPrime (k + 1)) = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr fun n hn => ?_
      obtain ⟨hn', hap⟩ := mem_filter.mp hn
      obtain ⟨hn₁, hn₂⟩ := mem_Ioc.mp hn'
      have he : n = 1 := by omega
      simpa [he] using hap.2
    rw [almostPrimeCounting_eq_card_filter, hs, Finset.card_empty, Nat.cast_zero]
    positivity

end MetaMathlibExt
