/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.PrimeFin
public import MathlibExt.Data.Set.Density
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Erdős Problem 690

The fourth smallest prime-factor density has a strict local minimum at 17.
This gives Cambie's counterexample to unimodality on the primes.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem690Wanted

/-- **The $k$-th smallest prime factor.** For natural numbers $k$, $n$ and $p$, $p$ is the $k$-th
smallest prime factor of $n$ when $n \ne 0$, $p$ is a prime dividing $n$, and exactly $k - 1$
primes dividing $n$ are smaller than $p$.

For $k = 0$ the count $k - 1$ is read as $0$ (truncated subtraction), so $k = 0$ and $k = 1$
agree. -/
def IsKthSmallestPrimeFactor (k n p : ℕ) : Prop :=
  p ∈ Nat.primeFactors n ∧
    ((Nat.primeFactors n).filter (fun q => q < p)).card = k - 1

/-- **The $k$-th prime-factor density.** For natural numbers $k$ and $p$, let $S_{k,p}$ be the set
of natural numbers whose $k$-th smallest prime factor is $p$. The $k$-th prime-factor density
$d_k(p)$ is the natural density of $S_{k,p}$, that is, the limit of
$\lvert S_{k,p} \cap \{0, 1, \dots, N - 1\} \rvert / N$ as $N \to \infty$, when this limit
exists; otherwise $d_k(p)$ is an unspecified real number. -/
noncomputable def kthPrimeFactorDensity (k p : ℕ) : ℝ :=
  Classical.epsilon (fun d : ℝ =>
    Set.HasDensity {n : ℕ | IsKthSmallestPrimeFactor k n p} d)

/-- **Unimodality on the primes.** A function $f \colon \mathbb{N} \to \mathbb{R}$ is unimodal on
the primes if there is a prime $p_0$ such that $f(p) \le f(q)$ for all primes $p$ and $q$ with
$p \le q \le p_0$, and $f(q) \le f(p)$ for all primes $p$ and $q$ with $p_0 \le p \le q$. -/
def IsUnimodalOnPrimes (f : ℕ → ℝ) : Prop :=
  ∃ p₀ : ℕ, p₀.Prime ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p ≤ q → q ≤ p₀ → f p ≤ f q) ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p₀ ≤ p → p ≤ q → f q ≤ f p)

/-- **Erdős Problem 690.** The proposition that for every natural number $k \ge 1$ the $k$-th
prime-factor density $d_k$ is unimodal on the primes: there is a prime $p_0$ such that
$d_k(p) \le d_k(q)$ for all primes $p$ and $q$ with $p \le q \le p_0$, and $d_k(q) \le d_k(p)$ for
all primes $p$ and $q$ with $p_0 \le p \le q$. Here $d_k(p)$ is the natural density of the set of
natural numbers whose $k$-th smallest prime factor is $p$ (an unspecified real number if this
density does not exist). -/
def conjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → IsUnimodalOnPrimes (kthPrimeFactorDensity k)

open Finset Filter Topology

-- Indicator for multiples of d divisible by exactly r entries of qs.
private def sieveIndicator (qs : List ℕ) (d : ℕ) (r : ℤ) (n : ℕ) : ℝ :=
  if d ∣ n ∧ (qs.countP (fun q => q ∣ n) : ℤ) = r then 1 else 0

-- Among multiples of d, replace the multiples of q with r hits in the tail by those
-- with r - 1 hits. Both correction terms count multiples of lcm(d, q).
private def sieveDensity : List ℕ → ℕ → ℤ → ℚ
  | [], d, r => if r = 0 then 1 / (d : ℚ) else 0
  | q :: qs, d, r =>
    sieveDensity qs d r - sieveDensity qs (d.lcm q) r + sieveDensity qs (d.lcm q) (r - 1)

private lemma sieveIndicator_cons (q : ℕ) (qs : List ℕ) (d : ℕ) (r : ℤ) (n : ℕ) :
    sieveIndicator (q :: qs) d r n = sieveIndicator qs d r n -
      sieveIndicator qs (d.lcm q) r n + sieveIndicator qs (d.lcm q) (r - 1) n := by
  by_cases hd : d ∣ n <;> by_cases hq : q ∣ n <;>
    simp [sieveIndicator, Nat.lcm_dvd_iff, hd, hq, eq_sub_iff_add_eq]

private lemma tendsto_sieve (qs : List ℕ) (d : ℕ) (r : ℤ) :
    Tendsto (fun N : ℕ => (∑ n ∈ Ioc 0 N, sieveIndicator qs d r n) / (N : ℝ))
      atTop (𝓝 (sieveDensity qs d r : ℝ)) := by
  induction qs generalizing d r with
  | nil =>
    by_cases hr : r = 0
    · subst r
      have h := (tendsto_nat_floor_mul_div_atTop (a := 1 / (d : ℝ)) (by positivity)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
      simp only [Function.comp_def, one_div_mul_eq_div, Nat.floor_div_eq_div] at h
      simpa [sieveIndicator, sieveDensity, ← sum_filter, Nat.Ioc_filter_dvd_card_eq_div] using h
    · simp [sieveDensity, sieveIndicator, hr, Ne.symm hr]
  | cons q qs ih =>
    simpa [sieveIndicator_cons, sieveDensity, sum_add_distrib, sum_sub_distrib, add_div, sub_div]
      using ((ih d r).sub (ih (d.lcm q) r)).add (ih (d.lcm q) (r - 1))

private def smallerPrimes (p : ℕ) : List ℕ := (List.range p).filter Nat.Prime

private lemma isKth_iff {n p : ℕ} (k : ℕ) (hn : n ≠ 0) (hp : p.Prime) :
    IsKthSmallestPrimeFactor k n p ↔
      p ∣ n ∧ (smallerPrimes p).countP (fun q => q ∣ n) = k - 1 := by
  have hs : (n.primeFactors.filter (· < p)) = (smallerPrimes p).toFinset.filter (· ∣ n) := by
    ext q
    simp only [mem_filter, Nat.mem_primeFactors_of_ne_zero hn, smallerPrimes, List.mem_toFinset,
      List.mem_filter, List.mem_range, decide_eq_true_eq]
    tauto
  have hnodup : (smallerPrimes p).Nodup := (List.nodup_range).filter _
  simp [IsKthSmallestPrimeFactor, Nat.mem_primeFactors_of_ne_zero hn, hp, hs, hnodup.card_eq_countP]

private lemma kthDensity_eq (k p : ℕ) (hp : p.Prime) (value : ℚ)
    (hv : sieveDensity (smallerPrimes p) p (k - 1 : ℕ) = value) :
    kthPrimeFactorDensity k p = (value : ℝ) := by
  subst value
  let S := {n : ℕ | IsKthSmallestPrimeFactor k n p}
  suffices h : S.HasDensity (sieveDensity (smallerPrimes p) p (k - 1 : ℕ)) from
    tendsto_nhds_unique (Classical.epsilon_spec (p := fun d : ℝ => S.HasDensity d) ⟨_, h⟩) h
  -- Below N + 1, zero is excluded and the remaining candidates form (0, N].
  rw [Set.HasDensity, ← tendsto_add_atTop_iff_nat 1]
  have h := (tendsto_sieve (smallerPrimes p) p (k - 1 : ℕ)).mul
    (tendsto_natCast_div_add_atTop (1 : ℝ))
  rw [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hset : S ∩ Set.Iio (N + 1) =
      ↑((Ioc 0 N).filter fun n => p ∣ n ∧
        (smallerPrimes p).countP (fun q => q ∣ n) = k - 1) := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp [S, IsKthSmallestPrimeFactor]
    · simp [S, isKth_iff k hn hp, Nat.pos_of_ne_zero hn, and_comm]
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter, hset, Set.ncard_coe_finset,
    Set.ncard_Iio_nat, Nat.cast_add_one]
  have hnR : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [div_mul_div_cancel₀ hnR]
  simp [sieveIndicator]

/--
**Erdős Problem 690 is false.** There is a natural number $k \ge 1$ such that the $k$-th
prime-factor density $d_k$ is not unimodal on the primes, that is, there is no prime $p_0$ such
that $d_k(p) \le d_k(q)$ for all primes $p$ and $q$ with $p \le q \le p_0$ and
$d_k(q) \le d_k(p)$ for all primes $p$ and $q$ with $p_0 \le p \le q$. Here $d_k(p)$ is the
natural density of the set of natural numbers whose $k$-th smallest prime factor is $p$ (an
unspecified real number if this density does not exist).

Cambie (Theorem 5) proves that $d_k$ is unimodal for $k = 1, 2, 3$ and not unimodal for
$4 \le k \le 20$; for example $d_4(13) = 31/5005 > d_4(17) = 206/36465 < d_4(19) = 1308/230945$.

Source: S. Cambie, Resolution of Erdős' problems
about unimodularity, arXiv preprint (2025), arXiv:2501.10333, https://arxiv.org/abs/2501.10333.
Moved from `OpenConjectures/NumberTheory/ErdosProblem690`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨peak, _, hinc, hdec⟩ := h 4 (by decide)
  have h13 : Nat.Prime 13 := by decide
  have h17 : Nat.Prime 17 := by decide
  have h19 : Nat.Prime 19 := by decide
  have d13 := kthDensity_eq 4 13 h13 (31 / 5005) (by decide +kernel)
  have d17 := kthDensity_eq 4 17 h17 (206 / 36465) (by decide +kernel)
  have d19 := kthDensity_eq 4 19 h19 (1308 / 230945) (by decide +kernel)
  rcases le_total 17 peak with hpeak | hpeak
  · have hle := hinc 13 17 h13 h17 (by decide) hpeak
    norm_num [d13, d17] at hle
  · have hle := hdec 17 19 h17 h19 hpeak (by decide)
    norm_num [d17, d19] at hle

end MathlibExt.NumberTheory.ErdosProblem690Wanted
