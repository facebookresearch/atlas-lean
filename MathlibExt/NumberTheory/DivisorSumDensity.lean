/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Data.Set.Density
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import MathlibExt.NumberTheory.PrimeCounting.DirichletDensityArithmeticProgression
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Divisibility of divisor sums

For every positive integer `N`, the natural numbers whose divisor sum is not divisible by `N`
have natural density zero. The proof sieves by primes congruent to `-1` modulo `N` that divide
the argument exactly once.
-/

set_option autoImplicit false

public section

namespace MathlibExt.NumberTheory.AmicableWanted

open Filter Finset
open scoped Topology

private lemma exists_large_sum {ι : Type*} {f : ι → ℝ} (hf : 0 ≤ f) (hs : ¬ Summable f)
    (B : ℝ) : ∃ s : Finset ι, B < ∑ i ∈ s, f i := by
  by_contra! h
  exact hs (summable_of_sum_le hf h)

-- Finite subsums approach their reciprocal sums as the exponent approaches one.
private lemma prime_series_tendsto_atTop :
    Tendsto (fun s : ℝ ↦ ∑' p : Nat.Primes, (p.val : ℝ) ^ (-s)) (𝓝[>] 1) atTop := by
  refine tendsto_atTop.2 fun B ↦ ?_
  obtain ⟨t, ht⟩ := exists_large_sum (fun p : Nat.Primes ↦ by positivity)
    Nat.Primes.not_summable_one_div B
  have hlim : Tendsto (fun s : ℝ ↦ ∑ p ∈ t, (p.val : ℝ) ^ (-s)) (𝓝[>] 1)
      (𝓝 (∑ p ∈ t, 1 / (p.val : ℝ))) := by
    apply tendsto_finsetSum
    intro p _
    have hp : (p.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.ne_zero
    simpa [one_div, Real.rpow_neg_one, Function.comp_def] using
      ((Real.continuousAt_const_rpow hp).comp (continuous_neg.continuousAt (x := (1 : ℝ)))).tendsto
        |>.mono_left nhdsWithin_le_nhds
  filter_upwards [hlim.eventually (eventually_gt_nhds ht), self_mem_nhdsWithin] with s hBs hs
  exact hBs.le.trans ((Nat.Primes.summable_rpow.mpr (by linarith [show 1 < s from hs])).sum_le_tsum
    t fun p _ ↦ by positivity)

private abbrev progressionPrimes (N : ℕ) := {p : ℕ // p.Prime ∧ p ≡ N - 1 [MOD N]}

private lemma not_summable_progression (N : ℕ) (hN : 1 ≤ N) :
    ¬ Summable (fun p : progressionPrimes N ↦ 1 / (p.val : ℝ)) := by
  intro h
  have hcop : (N - 1).Coprime N := (Nat.coprime_self_sub_left hN).2 (Nat.coprime_one_left N)
  have hratio :=
    MetaMathlibExt.NumberTheory.PrimeCounting.dirichlet_density_primes_arithmetic_progression
      (N - 1) N hN hcop
  have hφ := Nat.totient_pos.mpr hN
  have hprod := hratio.pos_mul_atTop (by positivity) prime_series_tendsto_atTop
  have hev := hprod.eventually_gt_atTop (∑' p : progressionPrimes N, 1 / (p.val : ℝ))
  have hright : ∀ᶠ s : ℝ in 𝓝[>] 1, 1 < s := self_mem_nhdsWithin
  obtain ⟨s, hgt, hs, hpos⟩ :=
    (hev.and (hright.and (prime_series_tendsto_atTop.eventually_gt_atTop 0))).exists
  change _ < ((∑' p : progressionPrimes N, (p.val : ℝ) ^ (-s)) /
    (∑' p : Nat.Primes, (p.val : ℝ) ^ (-s))) * _ at hgt
  rw [div_mul_cancel₀ _ hpos.ne'] at hgt
  apply hgt.not_ge
  have hle (p : progressionPrimes N) : (p.val : ℝ) ^ (-s) ≤ 1 / (p.val : ℝ) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (mod_cast p.prop.1.one_le) (by linarith)
  exact (h.of_nonneg_of_le (fun p ↦ by positivity) hle).tsum_le_tsum hle h

-- Both error terms can be made small with the same finite set of primes.
private lemma exists_sieving_primes (N : ℕ) (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ p ≡ N - 1 [MOD N]) ∧
      Real.exp (-(∑ p ∈ s, 1 / (p : ℝ))) < δ ∧ (∑ p ∈ s, 1 / (p : ℝ) ^ 2) < δ := by
  classical
  have hsquare : Summable (fun p : progressionPrimes N ↦ 1 / (p.val : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).subtype _
  obtain ⟨u, hu⟩ := summable_iff_vanishing_norm.mp hsquare δ hδ
  let f (p : progressionPrimes N) : ℝ := 1 / p.val
  have hf : 0 ≤ f := fun p ↦ by dsimp [f]; positivity
  obtain ⟨v, hv⟩ := exists_large_sum hf (not_summable_progression N hN)
    (-Real.log δ + ∑ p ∈ u, f p)
  let t := (u ∪ v) \ u
  have hsum := sum_sdiff (f := f) (subset_union_left (s₂ := v) : u ⊆ u ∪ v)
  have hmono := sum_le_sum_of_subset_of_nonneg (f := f) (subset_union_right (s₁ := u) (s₂ := v))
    (fun p _ _ ↦ hf p)
  refine ⟨t.map (.subtype _), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, _, rfl⟩ := mem_map.mp hp
    exact q.prop
  · rw [sum_map, ← Real.exp_log hδ, Real.exp_lt_exp]
    change -(∑ p ∈ t, f p) < Real.log δ
    dsimp [t]
    linarith
  · rw [sum_map]
    have h := hu t sdiff_disjoint
    rwa [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg fun p _ ↦ by positivity)] at h

private lemma dvd_sigma_of_exact_factor {N p n : ℕ} (hN : 1 ≤ N) (hp : p.Prime)
    (hc : p ≡ N - 1 [MOD N]) (hd : p ∣ n) (hsq : ¬ p ^ 2 ∣ n) :
    N ∣ ArithmeticFunction.sigma 1 n := by
  obtain ⟨m, rfl⟩ := hd
  have hcop : p.Coprime m := hp.coprime_iff_not_dvd.2 fun hm ↦
    hsq (by simpa [pow_two] using Nat.mul_dvd_mul_left p hm)
  have hsum : ArithmeticFunction.sigma 1 p = p + 1 := by
    simpa [sum_range_succ, add_comm] using ArithmeticFunction.sigma_one_apply_prime_pow (i := 1) hp
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop, hsum]
  apply dvd_mul_of_dvd_left
  apply Nat.modEq_zero_iff_dvd.mp
  exact (hc.add_right 1).trans (by simp [Nat.sub_add_cancel hN, Nat.ModEq])

private lemma totient_ratio_le_exp (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ((∏ p ∈ s, p).totient : ℝ) / (∏ p ∈ s, p : ℕ) ≤ Real.exp (-(∑ p ∈ s, 1 / (p : ℝ))) := by
  let Q := ∏ p ∈ s, p
  have hQ : 0 < Q := prod_pos (fun p hp ↦ (hs p hp).pos)
  have hprod := Nat.totient_eq_mul_prod_factors Q
  rw [show Q.primeFactors = s from Nat.primeFactors_prod hs] at hprod
  have hreal := congrArg (fun r : ℚ ↦ (r : ℝ)) hprod
  push_cast at hreal
  change (Q.totient : ℝ) / Q ≤ _
  rw [hreal, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hQ.ne'), ← sum_neg_distrib, Real.exp_sum]
  apply prod_le_prod₀
  · intro p hp
    have : 1 ≤ (p : ℝ) := mod_cast (hs p hp).one_le
    exact sub_nonneg.mpr (inv_le_one_of_one_le₀ this)
  · intro p _
    simpa [one_div, sub_eq_neg_add] using Real.add_one_le_exp (-(p : ℝ)⁻¹)

-- An exception is coprime to the product of the sieving primes, or divisible by a sieving square.
private lemma exceptional_count_le (N x : ℕ) (hN : 1 ≤ N) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≡ N - 1 [MOD N]) :
    ({n : ℕ | ¬ N ∣ ArithmeticFunction.sigma 1 n} ∩ Set.Iio x).ncard ≤
      (∏ p ∈ s, p).totient * (x / (∏ p ∈ s, p) + 1) + ∑ p ∈ s, x / p ^ 2 := by
  classical
  let Q := ∏ p ∈ s, p
  let a := (Ico 0 x).filter (Q.Coprime ·)
  let b (p : ℕ) := (Ioc 0 x).filter (p ^ 2 ∣ ·)
  have hsub : {n : ℕ | ¬ N ∣ ArithmeticFunction.sigma 1 n} ∩ Set.Iio x ⊆
      (↑(a ∪ s.biUnion b) : Set ℕ) := by
    rintro n ⟨hn, hx⟩
    change ¬ N ∣ ArithmeticFunction.sigma 1 n at hn
    change n < x at hx
    by_cases hc : Q.Coprime n
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Ico.mpr ⟨Nat.zero_le _, hx⟩, hc⟩)
    · change ¬ Nat.Coprime (∏ p ∈ s, p) n at hc
      rw [Nat.coprime_prod_left_iff] at hc
      push Not at hc
      obtain ⟨p, hp, hpn⟩ := hc
      have hd : p ∣ n := by simpa [(hs p hp).1.coprime_iff_not_dvd] using hpn
      have hsq : p ^ 2 ∣ n := by
        by_contra h
        exact hn (dvd_sigma_of_exact_factor hN (hs p hp).1 (hs p hp).2 hd h)
      have hn0 : n ≠ 0 := by rintro rfl; simp at hn
      exact mem_union_right _ (mem_biUnion.mpr ⟨p, hp,
        mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, hx.le⟩, hsq⟩⟩)
  have hQ : 0 < Q := prod_pos fun p hp ↦ (hs p hp).1.pos
  have ha : a.card ≤ Q.totient * (x / Q + 1) := by
    simpa [a] using Nat.Ico_filter_coprime_le 0 x hQ.ne'
  calc
    _ ≤ (↑(a ∪ s.biUnion b) : Set ℕ).ncard := Set.ncard_le_ncard hsub
    _ = (a ∪ s.biUnion b).card := Set.ncard_coe_finset _
    _ ≤ a.card + (s.biUnion b).card := card_union_le _ _
    _ ≤ _ := add_le_add ha (by simpa [b, Nat.Ioc_filter_dvd_card_eq_div] using
      (card_biUnion_le (s := s) (t := b)))

/-- **A fixed positive integer divides the divisor sum of almost every natural number.** For
a natural number $l$ let $\sigma(l)$ denote the sum of the positive divisors of $l$, with
$\sigma(0) = 0$. Then for every positive integer $N$, the set of natural numbers $l$ such
that $N$ does not divide $\sigma(l)$ has natural density $0$.

Source: Stoyan Dimitrov, "Generalizations of Amicable
Numbers", Lemma 1. -/
theorem tendsto_density_not_dvd_sigma (N : ℕ)
    (hN : 1 ≤ N) :
    {l : ℕ | ¬ N ∣ ArithmeticFunction.sigma 1 l}.HasDensity 0 := by
  simp only [Set.HasDensity, Set.partialDensity, Set.inter_univ, Set.univ_inter,
    Set.ncard_Iio_nat, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨s, hs, hexp, hsquare⟩ := exists_sieving_primes N hN (show 0 < ε / 3 by positivity)
  let Q := ∏ p ∈ s, p
  have hQ : 0 < Q := prod_pos fun p hp ↦ (hs p hp).1.pos
  have hφ : (Q.totient : ℝ) / Q < ε / 3 :=
    (totient_ratio_le_exp s fun p hp ↦ (hs p hp).1).trans_lt hexp
  filter_upwards [eventually_ge_atTop Q] with x hx
  have hQ' : (0 : ℝ) < Q := mod_cast hQ
  have hx' : (Q : ℝ) ≤ x := mod_cast hx
  have hx0 := hQ'.trans_le hx'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hx0]
  have h := Nat.cast_le (α := ℝ) |>.mpr (exceptional_count_le N x hN s hs)
  change _ ≤ ((Q.totient * (x / Q + 1) + ∑ p ∈ s, x / p ^ 2 : ℕ) : ℝ) at h
  push_cast at h
  apply h.trans_lt
  have hdiv : (↑(x / Q) : ℝ) + 1 ≤ 2 * ((x : ℝ) / Q) := by
    linarith [Nat.cast_div_le (α := ℝ) (m := x) (n := Q), (one_le_div hQ').2 hx']
  calc
    _ ≤ (Q.totient : ℝ) * (2 * (x / Q)) + ∑ p ∈ s, (x : ℝ) / (p : ℝ) ^ 2 := by
      apply add_le_add (mul_le_mul_of_nonneg_left hdiv (by positivity))
      exact sum_le_sum fun p _ ↦ by
        rw [← Nat.cast_pow]
        exact Nat.cast_div_le
    _ = (2 * (Q.totient / (Q : ℝ)) + ∑ p ∈ s, 1 / (p : ℝ) ^ 2) * x := by
      rw [add_mul, sum_mul]
      simp only [div_eq_mul_inv]
      ring_nf
    _ < ε * x := mul_lt_mul_of_pos_right (by linarith) hx0

end MathlibExt.NumberTheory.AmicableWanted
