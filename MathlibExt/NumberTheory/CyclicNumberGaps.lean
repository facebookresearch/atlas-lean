/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.PrimeCounting
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsup

/-!
# Gaps between cyclic numbers

We prove the little-o bound for consecutive cyclic-number gaps using inclusion–exclusion and
Gronwall's bound on the sum of divisors. For a squarefree integer, failure to be cyclic gives
a factorization of the form $p(pk+1)r$. Counting separately by small $k$ and small $r$ bounds
these exceptions in a short interval. This argument gives the estimate unconditionally.
-/

open Asymptotics Filter Finset Topology

namespace MetaMathlibExt.cyclicNumber_gap_isLittleO_of_riemannHypothesis

private lemma prime_cyclic {p : ℕ} (hp : p.Prime) : IsCyclicNumber p := by
  refine ⟨hp.pos, hp.coprime_iff_not_dvd.mpr ?_⟩
  rw [Nat.totient_prime hp]
  have := hp.two_le
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)

private lemma cyclic_of_squarefree {n : ℕ} (hn : 0 < n) (hs : Squarefree n)
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → ¬p ∣ q - 1) :
    IsCyclicNumber n := by
  refine ⟨hn, Nat.coprime_of_dvd fun p hp hpn hpt ↦ ?_⟩
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hs,
    Nat.div_self hn, one_mul] at hpt
  obtain ⟨q, hq, hpq⟩ := (hp.prime.dvd_finsetProd_iff _).mp hpt
  exact h p q hp (Nat.prime_of_mem_primeFactors hq) hpn
    (Nat.dvd_of_mem_primeFactors hq) hpq

open Classical in
/-- Count an affine progression in a half-open interval using the floors of its endpoints. -/
private lemma card_affine_le {a b d e : ℕ} (hab : a ≤ b) (hd : 0 < d) :
    (#{n ∈ Ioc a b | ∃ k : ℕ, n = d * k + e} : ℝ) ≤ ((b : ℝ) - a) / d + 1 := by
  classical
  let A : ℝ := ((a : ℝ) - e) / d
  let B : ℝ := ((b : ℝ) - e) / d
  have hAB : A ≤ B := by
    dsimp [A, B]
    gcongr
  let f : ℕ → ℤ := fun n ↦ ((n : ℤ) - e) / d
  have hf {n k : ℕ} (h : n = d * k + e) : f n = k := by
    simp only [f, h, Nat.cast_add, Nat.cast_mul, add_sub_cancel_right]
    exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hd.ne')
  have hcard : #{n ∈ Ioc a b | ∃ k : ℕ, n = d * k + e} ≤ #(Ioc ⌊A⌋ ⌊B⌋) := by
    apply card_le_card_of_injOn f
    · intro n hn
      obtain ⟨hn, k, hk⟩ := mem_filter.mp hn
      obtain ⟨han, hnb⟩ := mem_Ioc.mp hn
      change f n ∈ Ioc ⌊A⌋ ⌊B⌋
      rw [mem_Ioc, hf hk, Int.floor_lt, Int.le_floor]
      have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      have h₁ : (a : ℝ) < n := by exact_mod_cast han
      have h₂ : (n : ℝ) ≤ b := by exact_mod_cast hnb
      push_cast [hk] at h₁ h₂
      exact ⟨(div_lt_iff₀ hd').mpr (by push_cast; linarith),
        (le_div_iff₀ hd').mpr (by push_cast; linarith)⟩
    · intro i hi j hj hij
      obtain ⟨_, k, hk⟩ := mem_filter.mp hi
      obtain ⟨_, l, hl⟩ := mem_filter.mp hj
      rw [hf hk, hf hl] at hij
      exact hk.trans ((congrArg (fun k : ℕ ↦ d * k + e)
        (by exact_mod_cast hij)).trans hl.symm)
  refine (Nat.cast_le.mpr hcard).trans ?_
  rw [Int.card_Ioc, ← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr (Int.floor_mono hAB)),
    Int.cast_sub]
  have hdiff : B - A = ((b : ℝ) - a) / d := by dsimp [A, B]; ring
  linarith [Int.floor_le B, Int.lt_floor_add_one A]

private lemma card_multiples_error {a b d : ℕ} (hab : a ≤ b) (hd : 0 < d) :
    |(#{n ∈ Ioc a b | d ∣ n} : ℝ) - ((b : ℝ) - a) / d| ≤ 1 := by
  let f : ℕ → ℕ := fun k ↦ d * k
  have heq : {n ∈ Ioc a b | d ∣ n} = (Ioc (a / d) (b / d)).image f := by
    ext n
    simp only [mem_filter, mem_Ioc, mem_image, f, dvd_def]
    constructor
    · rintro ⟨⟨_, _⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rw [Nat.div_lt_iff_lt_mul hd, mul_comm]
        assumption
      · rw [Nat.le_div_iff_mul_le hd, mul_comm]
        assumption
    · rintro ⟨k, ⟨hk₁, hk₂⟩, rfl⟩
      rw [Nat.div_lt_iff_lt_mul hd, mul_comm k] at hk₁
      rw [Nat.le_div_iff_mul_le hd, mul_comm k] at hk₂
      exact ⟨⟨hk₁, hk₂⟩, k, rfl⟩
  rw [heq, card_image_of_injective _ (fun i j hij ↦ Nat.eq_of_mul_eq_mul_left hd hij),
    Nat.card_Ioc, Nat.cast_sub (Nat.div_le_div_right hab)]
  have hf (n : ℕ) : ⌊(n : ℝ) / d⌋₊ = n / d := by simp [Nat.floor_div_natCast]
  rw [← hf a, ← hf b, sub_div]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h₁ := Nat.floor_le (div_nonneg (Nat.cast_nonneg a) hd'.le)
  have h₂ := Nat.floor_le (div_nonneg (Nat.cast_nonneg b) hd'.le)
  rw [abs_le]
  constructor <;> linarith [Nat.lt_floor_add_one ((a : ℝ) / d),
    Nat.lt_floor_add_one ((b : ℝ) / d)]

private noncomputable def sieveWeight (s : Finset ℕ) : ℝ :=
  ∏ p ∈ s, (1 - (p : ℝ)⁻¹)

private lemma sieveWeight_pos {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    0 < sieveWeight s :=
  prod_pos fun p hp ↦ sub_pos.mpr (inv_lt_one_of_one_lt₀ (by exact_mod_cast (hs p hp).one_lt))

/-- Inclusion–exclusion incurs at most one unit of rounding error for each subset of primes. -/
private lemma sieve_lower {a b : ℕ} (hab : a ≤ b) {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime) :
    ((b : ℝ) - a) * sieveWeight s - (2 : ℝ) ^ #s ≤
      (#{n ∈ Ioc a b | ∀ p ∈ s, ¬p ∣ n} : ℝ) := by
  classical
  let P (t : Finset ℕ) := ∏ p ∈ t, p
  let sign (t : Finset ℕ) := (-1 : ℝ) ^ #t
  let L := (b : ℝ) - a
  let N (t : Finset ℕ) := (#{n ∈ Ioc a b | P t ∣ n} : ℝ)
  have hprod_dvd {t : Finset ℕ} (ht : t ⊆ s) (n : ℕ) :
      P t ∣ n ↔ ∀ p ∈ t, p ∣ n := by
    refine ⟨fun h p hp ↦ (dvd_prod_of_mem id hp).trans h, ?_⟩
    apply Finset.prod_dvd_of_isRelPrime
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hs p (ht hp)) (hs q (ht hq))).mpr hpq)
  have hind (n : ℕ) :
      (if ∀ p ∈ s, ¬p ∣ n then (1 : ℝ) else 0) =
        ∏ p ∈ s, (1 - if p ∣ n then (1 : ℝ) else 0) := by
    split_ifs with h
    · symm
      exact prod_eq_one fun p hp ↦ by simp [h p hp]
    · push Not at h
      obtain ⟨p, hp, hpn⟩ := h
      exact (prod_eq_zero hp (by simp [hpn])).symm
  have hcount : (#{n ∈ Ioc a b | ∀ p ∈ s, ¬p ∣ n} : ℝ) =
      ∑ t ∈ s.powerset, sign t * N t := by
    rw [← sum_boole]
    simp_rw [hind, prod_sub, prod_const_one, mul_one]
    rw [sum_comm]
    refine sum_congr rfl fun t ht ↦ ?_
    have hI (n : ℕ) : (∏ p ∈ t, if p ∣ n then (1 : ℝ) else 0) =
        if P t ∣ n then 1 else 0 := by
      simp only [hprod_dvd (mem_powerset.mp ht)]
      split_ifs with h
      · exact prod_eq_one fun p hp ↦ ite_eq_left (h p hp)
      · push Not at h
        obtain ⟨p, hp, hpn⟩ := h
        exact prod_eq_zero hp (ite_eq_right hpn)
    simp_rw [hI, ← mul_sum, sum_boole, N, sign]
  have hweight : L * sieveWeight s =
      ∑ t ∈ s.powerset, sign t * (L / P t) := by
    simp only [sieveWeight, prod_sub, prod_const_one, mul_one, mul_sum, P, sign]
    refine sum_congr rfl fun t _ ↦ ?_
    rw [Nat.cast_prod, Finset.prod_inv_distrib]
    ring
  have herr : ∀ t ∈ s.powerset, sign t * (L / P t) - sign t * N t ≤ 1 := by
    intro t ht
    have hd : 0 < P t := prod_pos fun p hp ↦ (hs p (mem_powerset.mp ht hp)).pos
    have he := card_multiples_error hab hd
    have hId : sign t * (L / P t) - sign t * N t = sign t * -(N t - L / P t) := by ring
    rw [hId]
    calc
      _ ≤ |sign t * -(N t - L / P t)| := le_abs_self _
      _ ≤ 1 := by simpa [abs_mul, abs_sub_comm, sign, N, L] using he
  have hsum := sum_le_sum herr
  rw [sum_sub_distrib, ← hweight, ← hcount, sum_const, card_powerset, nsmul_eq_mul,
    mul_one, Nat.cast_pow, Nat.cast_ofNat] at hsum
  linarith

open Classical in
private lemma card_indexed_affine_le {a b p : ℕ} (hab : a ≤ b) (hb : 1 ≤ b)
    (hp : 0 < p) {d e : ℕ → ℕ} (hd : ∀ i, p ^ 2 * i ≤ d i) :
    let M := ⌊Real.sqrt b / p⌋₊
    (#((Icc 1 M).biUnion fun i ↦ {n ∈ Ioc a b | ∃ j : ℕ, n = d i * j + e i}) : ℝ) ≤
      ((b : ℝ) - a) / (p : ℝ) ^ 2 * (1 + Real.log b) + Real.sqrt b / p := by
  classical
  dsimp only
  let M := ⌊Real.sqrt b / p⌋₊
  change (#((Icc 1 M).biUnion _) : ℝ) ≤ _
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hM : (M : ℝ) ≤ Real.sqrt b / p := Nat.floor_le (by positivity)
  have hMb : M ≤ b := by
    apply Nat.cast_le.mp (hM.trans ?_)
    exact (div_le_self (Real.sqrt_nonneg _) (by exact_mod_cast hp)).trans
      (Real.sqrt_le_self_iff.mpr (Or.inr hb'))
  have hH : ∑ i ∈ Icc 1 M, (i : ℝ)⁻¹ ≤ 1 + Real.log b := by
    calc
      _ ≤ ∑ i ∈ Icc 1 b, (i : ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hMb) (fun _ _ _ ↦ by positivity)
      _ ≤ _ := by simpa [harmonic_eq_sum_Icc] using harmonic_le_one_add_log b
  calc
    _ ≤ ∑ i ∈ Icc 1 M, (#{n ∈ Ioc a b | ∃ j : ℕ, n = d i * j + e i} : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ i ∈ Icc 1 M, (((b : ℝ) - a) / (p : ℝ) ^ 2 * (i : ℝ)⁻¹ + 1) := by
      refine sum_le_sum fun i hi ↦ ?_
      have hi' := (mem_Icc.mp hi).1
      have hpos : 0 < p ^ 2 * i := Nat.mul_pos (pow_pos hp _) (by omega)
      refine (card_affine_le hab (hpos.trans_le (hd i))).trans ?_
      rw [← div_eq_mul_inv, div_div]
      gcongr
      exact_mod_cast hd i
    _ = ((b : ℝ) - a) / (p : ℝ) ^ 2 * (∑ i ∈ Icc 1 M, (i : ℝ)⁻¹) + M := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
      simp
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hH (by positivity)) hM

open Classical in
/-- Cover noncyclic integers by multiples of $p^2$ and by progressions from $p(pk+1)r$.
Since $p^2kr ≤ b$, one of $k$ and $r$ is at most $√b/p$. -/
private lemma bad_upper {a b z : ℕ} (hab : a ≤ b) (hb : 1 ≤ b) :
    let s := (Nat.primesLE ⌊Real.sqrt b⌋₊).filter (z < ·)
    (#{n ∈ Ioc a b | (∀ p ∈ z.primesLE, ¬p ∣ n) ∧ ¬ IsCyclicNumber n} : ℝ) ≤
      (((b : ℝ) - a) * (3 + 2 * Real.log b)) * (∑ p ∈ s, (p : ℝ)⁻¹ ^ 2) +
        3 * Real.sqrt b * (∑ p ∈ s, (p : ℝ)⁻¹) := by
  classical
  let s := (Nat.primesLE ⌊Real.sqrt b⌋₊).filter (z < ·)
  let sq (p : ℕ) := {n ∈ Ioc a b | p * p ∣ n}
  let left (p : ℕ) := (Icc 1 ⌊Real.sqrt b / p⌋₊).biUnion
    fun k ↦ {n ∈ Ioc a b | ∃ r : ℕ, n = (p * (p * k + 1)) * r + 0}
  let right (p : ℕ) := (Icc 1 ⌊Real.sqrt b / p⌋₊).biUnion
    fun r ↦ {n ∈ Ioc a b | ∃ k : ℕ, n = (p ^ 2 * r) * k + p * r}
  let cover (p : ℕ) := (sq p ∪ left p) ∪ right p
  have hsub : {n ∈ Ioc a b | (∀ p ∈ z.primesLE, ¬p ∣ n) ∧ ¬ IsCyclicNumber n} ⊆
      s.biUnion cover := by
    intro n hn
    obtain ⟨hn, hr, hc⟩ := mem_filter.mp hn
    have hnpos : 0 < n := (Nat.zero_le a).trans_lt (mem_Ioc.mp hn).1
    have hnb := (mem_Ioc.mp hn).2
    have hmem {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hsq : p ^ 2 ≤ n) : p ∈ s := by
      refine mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨?_, hp⟩, ?_⟩
      · apply Nat.le_floor
        apply (Real.le_sqrt (by positivity) (by positivity)).mpr
        exact_mod_cast hsq.trans hnb
      · by_contra! h
        exact hr p (Nat.mem_primesLE.mpr ⟨h, hp⟩) hpn
    by_cases hsq : Squarefree n
    · have hex : ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ∣ n ∧ q ∣ n ∧ p ∣ q - 1 := by
        by_contra! h
        apply hc
        apply cyclic_of_squarefree hnpos hsq
        exact h
      obtain ⟨p, q, hp, hq, hpn, hqn, k, hk⟩ := hex
      have hq2 := hq.two_le
      have hqk : q = p * k + 1 := by omega
      have hkn : 0 < k := by
        by_contra! h
        interval_cases k
        simp_all
      have hpq : p ≠ q := by
        have hm : p ≤ p * k := Nat.le_mul_of_pos_right _ hkn
        omega
      obtain ⟨r, hrn⟩ := ((Nat.coprime_primes hp hq).mpr hpq).mul_dvd_of_dvd_of_dvd hpn hqn
      rw [hqk] at hrn
      have hr0 : 0 < r := by
        by_contra! h
        interval_cases r
        simp_all
      have hpkr : p ^ 2 * (k * r) ≤ n := by
        rw [hrn]
        calc
          p ^ 2 * (k * r) = p * (p * k) * r := by ring
          _ ≤ _ := by gcongr; omega
      have hp2 : p ^ 2 ≤ n := (Nat.le_mul_of_pos_right _
        (Nat.mul_pos hkn hr0)).trans hpkr
      refine mem_biUnion.mpr ⟨p, hmem hp hpn hp2, ?_⟩
      have ht {i : ℕ} (hi : i ^ 2 ≤ k * r) : i ≤ ⌊Real.sqrt b / p⌋₊ := by
        apply Nat.le_floor
        refine (le_div_iff₀ (by exact_mod_cast hp.pos)).mpr ?_
        apply (Real.le_sqrt (by positivity) (by positivity)).mpr
        have hm := Nat.mul_le_mul_left (p ^ 2) hi
        have he : (i * p) ^ 2 = p ^ 2 * i ^ 2 := by ring
        rw [← he] at hm
        exact_mod_cast hm.trans (hpkr.trans hnb)
      rcases le_total k r with hkr | hrk
      · apply mem_union.mpr
        left
        apply mem_union.mpr
        right
        refine mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨hkn, ht ?_⟩, ?_⟩
        · simpa [pow_two] using Nat.mul_le_mul_left k hkr
        · exact mem_filter.mpr ⟨hn, r, by simpa using hrn⟩
      · apply mem_union.mpr
        right
        refine mem_biUnion.mpr ⟨r, mem_Icc.mpr ⟨hr0, ht ?_⟩, ?_⟩
        · simpa [pow_two] using Nat.mul_le_mul_right r hrk
        · refine mem_filter.mpr ⟨hn, k, ?_⟩
          rw [hrn]
          ring
    · rw [Nat.squarefree_iff_prime_squarefree] at hsq
      push Not at hsq
      obtain ⟨p, hp, hpd⟩ := hsq
      have hpn := (dvd_mul_right p p).trans hpd
      have hp2 : p ^ 2 ≤ n := by simpa [pow_two] using Nat.le_of_dvd hnpos hpd
      exact mem_biUnion.mpr ⟨p, hmem hp hpn hp2,
        mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hn, hpd⟩))⟩
  have hcard : (#(s.biUnion cover) : ℝ) ≤ ∑ p ∈ s, (#(cover p) : ℝ) := by
    exact_mod_cast card_biUnion_le
  refine ((Nat.cast_le.mpr (card_le_card hsub)).trans hcard).trans ?_
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun p hp ↦ ?_
  obtain ⟨hp', _⟩ := mem_filter.mp hp
  have hp0 := (Nat.prime_of_mem_primesLE hp').pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hps : (p : ℝ) ≤ Real.sqrt b :=
    (Nat.cast_le.mpr (Nat.le_of_mem_primesLE hp')).trans (Nat.floor_le (by positivity))
  have hpS : 1 ≤ Real.sqrt b / p := (le_div_iff₀ hpR).mpr (by simpa)
  have hsq : (#(sq p) : ℝ) ≤ ((b : ℝ) - a) / (p : ℝ) ^ 2 + 1 := by
    have h := (abs_le.mp (card_multiples_error hab (Nat.mul_pos hp0 hp0))).2
    push_cast at h
    simp only [sq, pow_two]
    linarith only [h]
  have hl := card_indexed_affine_le (d := fun k ↦ p * (p * k + 1)) (e := fun _ ↦ 0)
    hab hb hp0 (fun i ↦ by
      rw [pow_two, mul_assoc]
      exact Nat.mul_le_mul_left _ (Nat.le_succ _))
  have hr := card_indexed_affine_le (d := fun r ↦ p ^ 2 * r) (e := fun r ↦ p * r)
    hab hb hp0 (fun _ ↦ le_rfl)
  dsimp at hl hr
  have hu : (#(cover p) : ℝ) ≤ #(sq p) + (#(left p) + #(right p)) := by
    norm_cast
    exact (card_union_le ..).trans (by
      have h := card_union_le (sq p) (left p)
      omega)
  apply hu.trans
  change (#(sq p) : ℝ) + (#(left p) + #(right p)) ≤ _
  have hl' : (#(left p) : ℝ) ≤ _ := hl
  have hr' : (#(right p) : ℝ) ≤ _ := hr
  rw [inv_pow]
  simp only [div_eq_mul_inv] at hsq hl' hr' hpS
  linarith only [hsq, hl', hr', hpS]

/-- The sum of the reciprocal squares of integers strictly above a positive cutoff. -/
private lemma sum_inv_sq_le {s : Finset ℕ} {y : ℕ} (hy : 0 < y)
    (hs : ∀ n ∈ s, y < n) : ∑ n ∈ s, (n : ℝ)⁻¹ ^ 2 ≤ (y : ℝ)⁻¹ := by
  let b := max y (s.sup id)
  have hyb : y ≤ b := le_max_left ..
  have htel : ∀ b : ℕ, y ≤ b →
      ∑ n ∈ Ioc y b, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) = (y : ℝ)⁻¹ - (b : ℝ)⁻¹ := by
    intro b hb
    induction b, hb using Nat.le_induction with
    | base => simp
    | succ b hb ih =>
      rw [← insert_Ioc_right_eq_Ioc_add_one hb, sum_insert (by simp), ih]
      push_cast
      ring
  calc
    _ ≤ ∑ n ∈ s, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := by
      refine sum_le_sum fun n hn ↦ ?_
      have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by linarith [hs n hn])
      have h : 0 < (n : ℝ) - 1 := by linarith
      have h' : 0 < (n : ℝ) := by linarith
      field_simp
      linarith
    _ ≤ ∑ n ∈ Ioc y b, (((n : ℝ) - 1)⁻¹ - (n : ℝ)⁻¹) := by
      refine sum_le_sum_of_subset_of_nonneg (fun n hn ↦ mem_Ioc.mpr
        ⟨hs n hn, (le_sup (f := id) hn).trans (le_max_right ..)⟩) ?_
      intro n hn _
      have hn1 : (1 : ℝ) < n := by
        exact_mod_cast (show 1 < n by linarith [(mem_Ioc.mp hn).1])
      exact sub_nonneg.mpr (inv_anti₀ (by linarith) (by linarith))
    _ ≤ _ := by rw [htel b hyb]; exact sub_le_self _ (by positivity)

private lemma primeCounting_upper :
    ∀ᶠ y : ℕ in atTop, (y.primeCounting : ℝ) ≤ 3 * y / Real.log y := by
  have h := tendsto_natCast_atTop_atTop.eventually (Chebyshev.eventually_primeCounting_le one_pos)
  filter_upwards [h, eventually_ge_atTop (2 : ℕ)] with y hy hy2
  simp only [Nat.floor_natCast] at hy
  have hy' : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  refine hy.trans ?_
  gcongr
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

private lemma primeCounting_sparse {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y : ℕ in atTop, (y.primeCounting : ℝ) ≤ δ * y := by
  have hlog : Tendsto (fun y : ℕ ↦ Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [primeCounting_upper, hlog.eventually_ge_atTop (3 / δ)] with y hy hl
  have hpos : 0 < Real.log (y : ℝ) := (by positivity : 0 < 3 / δ).trans_le hl
  apply hy.trans
  rw [div_le_iff₀ hpos]
  have := (div_le_iff₀ hδ).mp hl
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) y) (show 0 ≤ δ * Real.log y - 3 by linarith)]

/-- Prime sparsity gives a reciprocal-square tail of size $o(1/z)$, uniformly over finite sets.
Split the sum at a fixed multiple of the cutoff and bound the remaining terms by all integers. -/
private lemma prime_tail_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z : ℕ in atTop, ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime ∧ z < p) →
      ∑ p ∈ s, (p : ℝ)⁻¹ ^ 2 ≤ δ / z := by
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / δ)
  have hMpos : (0 : ℝ) < M := (by positivity : 0 < 2 / δ).trans hM
  have hMnat : 0 < M := by exact_mod_cast hMpos
  have hT : Tendsto (fun z : ℕ ↦ M * z) atTop atTop :=
    tendsto_atTop_mono (fun z ↦ Nat.le_mul_of_pos_left z hMnat) tendsto_id
  have hδM : 0 < δ / (2 * (M : ℝ)) := by positivity
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    hT.eventually (primeCounting_sparse hδM)] with z hz hP s hs
  have hz' : (0 : ℝ) < z := by exact_mod_cast hz
  let u := s.filter (· ≤ M * z)
  let v := s.filter (fun p ↦ ¬p ≤ M * z)
  have hu : #u ≤ (M * z).primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact card_le_card fun p hp ↦ Nat.mem_primesLE.mpr
      ⟨(mem_filter.mp hp).2, (hs p (mem_filter.mp hp).1).1⟩
  have hv := sum_inv_sq_le (s := v) (Nat.mul_pos hMnat hz)
    (fun p hp ↦ lt_of_not_ge (mem_filter.mp hp).2)
  rw [← sum_filter_add_sum_filter_not s (· ≤ M * z)]
  calc
    _ ≤ (#u : ℝ) * (z : ℝ)⁻¹ ^ 2 + ((M * z : ℕ) : ℝ)⁻¹ := by
      apply add_le_add _ hv
      rw [← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun p hp ↦ ?_
      gcongr
      exact_mod_cast (hs p (mem_filter.mp hp).1).2.le
    _ ≤ (δ / (2 * (M : ℝ)) * (M * z)) * (z : ℝ)⁻¹ ^ 2 + ((M : ℝ) * z)⁻¹ := by
      rw [Nat.cast_mul]
      gcongr
      exact (Nat.cast_le.mpr hu).trans (by simpa using hP)
    _ ≤ δ / z := by
      have h' := (div_lt_iff₀ hδ).mp hM
      field_simp
      nlinarith

private lemma sieveWeight_mul_sigma {z : ℕ} :
    (1 / 4 : ℝ) ≤ sieveWeight z.primesLE *
      ((ArithmeticFunction.sigma 1 (primorial z) : ℕ) / (primorial z : ℝ)) := by
  have hsq := squarefree_primorial z
  have hprod :
      ((ArithmeticFunction.sigma 1 (primorial z) : ℕ) / (primorial z : ℝ)) =
        ∏ p ∈ z.primesLE, (1 + (p : ℝ)⁻¹) := by
    rw [ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
      (primorial_ne_zero z), primeFactors_primorial, primorial_eq_prod_primesLE,
      Nat.cast_prod, Nat.cast_prod, ← prod_div_distrib]
    refine prod_congr rfl fun p hp ↦ ?_
    have hp' := Nat.prime_of_mem_primesLE hp
    have hd : p ∣ primorial z := Nat.dvd_of_mem_primeFactors (by
      rw [primeFactors_primorial]; exact hp)
    rw [← primorial_eq_prod_primesLE, Nat.factorization_eq_one_of_squarefree hsq hp' hd]
    simp [sum_range_succ, add_div, div_self (by exact_mod_cast hp'.ne_zero : (p : ℝ) ≠ 0),
      add_comm, one_div]
  rw [hprod, sieveWeight, ← prod_mul_distrib]
  let s := z.primesLE
  have htel : ∀ t : Finset ℕ, (∀ p ∈ t, 2 ≤ p) →
      1 - ∑ p ∈ t, (p : ℝ)⁻¹ ^ 2 ≤ ∏ p ∈ t, ((1 - (p : ℝ)⁻¹) * (1 + (p : ℝ)⁻¹)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert p t hp ih =>
      intro h
      have hs : ∀ q ∈ t, 2 ≤ q := fun q hq ↦ h q (mem_insert_of_mem hq)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast h p (mem_insert_self ..)
      have hpi : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
      have hpi' : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hc : 0 ≤ 1 - (p : ℝ)⁻¹ ^ 2 := by nlinarith
      rw [sum_insert hp, prod_insert hp]
      have hi := mul_le_mul_of_nonneg_left (ih hs) hc
      have hn : 0 ≤ ∑ q ∈ t, (q : ℝ)⁻¹ ^ 2 := sum_nonneg fun _ _ ↦ by positivity
      nlinarith [mul_nonneg (sq_nonneg (p : ℝ)⁻¹) hn]
  have hsum : ∑ p ∈ s, (p : ℝ)⁻¹ ^ 2 ≤ 3 / 4 := by
    have hbound := sum_inv_sq_le (s := s.erase 2) (y := 2) (by decide)
      (fun p hp ↦ lt_of_le_of_ne (Nat.two_le_of_mem_primesLE (mem_erase.mp hp).2)
        (Ne.symm (mem_erase.mp hp).1))
    by_cases h : 2 ∈ s
    · rw [← sum_erase_add _ _ h]
      norm_num at hbound ⊢
      linarith
    · rw [erase_eq_of_notMem h] at hbound
      exact hbound.trans (by norm_num)
  exact (by linarith only [hsum] : (1 / 4 : ℝ) ≤ 1 - ∑ p ∈ s, (p : ℝ)⁻¹ ^ 2).trans
    (htel s fun p hp ↦ Nat.two_le_of_mem_primesLE hp)

/-- Apply Gronwall's bound to primorials to bound the inverse sieve weight. -/
private lemma inv_sieveWeight_le_log :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ z : ℕ in atTop, (sieveWeight z.primesLE)⁻¹ ≤ C * Real.log z := by
  let F (n : ℕ) := ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
    ((n : ℝ) * Real.log (Real.log n))
  let G := Real.exp Real.eulerMascheroniConstant + 1
  have hG : 0 < G := by dsimp [G]; positivity
  have hlim : limsup F atTop = Real.exp Real.eulerMascheroniConstant :=
    MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted.gronwall_sigma_limsup
  have hbd : ∃ B : ℝ, ∀ᶠ n in atTop, F n ≤ B := by
    by_contra! h
    have he : {B : ℝ | ∀ᶠ n in atTop, F n ≤ B} = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun B hB ↦ h B (hB.mono fun _ hle ↦ not_lt_of_ge hle)
    rw [limsup, limsSup] at hlim
    simp only [eventually_map] at hlim
    rw [he, Real.sInf_empty] at hlim
    exact (Real.exp_ne_zero _ hlim.symm).elim
  have he := eventually_lt_of_limsup_lt (show limsup F atTop < G by rw [hlim]; dsimp [G]; linarith)
    (let ⟨_, h⟩ := hbd; isBoundedUnder_of_eventually_le h)
  have hprimorial : Tendsto primorial atTop atTop := by
    refine tendsto_atTop.2 fun n ↦ ?_
    obtain ⟨p, hnp, hp⟩ := Nat.exists_infinite_primes n
    filter_upwards [eventually_ge_atTop p] with z hz
    exact hnp.trans (Nat.le_of_dvd (primorial_pos z) (Nat.dvd_of_mem_primeFactors (by
      rw [primeFactors_primorial]; exact Nat.mem_primesLE.mpr ⟨hz, hp⟩)))
  refine ⟨8 * G, by positivity, ?_⟩
  filter_upwards [hprimorial.eventually he, hprimorial.eventually_ge_atTop 4,
    eventually_ge_atTop (2 : ℕ)] with z hF hP hz
  have hP' : (4 : ℝ) ≤ primorial z := by exact_mod_cast hP
  have hz' : (1 : ℝ) < z := by exact_mod_cast (show 1 < z by omega)
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9]
  have hlogP : 1 < Real.log (primorial z : ℝ) := hlog4.trans_le
    (Real.log_le_log (by norm_num) hP')
  have hlog : Real.log (Real.log (primorial z : ℝ)) ≤ 2 * Real.log z := by
    have hθ := Chebyshev.theta_le_log4_mul_x (x := (z : ℝ)) (by positivity)
    rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] at hθ
    have h₁ := Real.log_le_log (by linarith : 0 < Real.log (primorial z : ℝ)) hθ
    rw [Real.log_mul (Real.log_pos (by norm_num)).ne'
      (by positivity : (z : ℝ) ≠ 0)] at h₁
    have h₂ : Real.log (Real.log 4) ≤ Real.log z := by
      apply Real.log_le_log (by linarith)
      have h4' : Real.log 4 ≤ 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact h4'.trans (by exact_mod_cast hz)
    linarith
  have hg : ((ArithmeticFunction.sigma 1 (primorial z) : ℕ) / (primorial z : ℝ)) ≤
      G * (2 * Real.log z) := by
    change F (primorial z) < G at hF
    unfold F at hF
    rw [← div_div] at hF
    exact ((div_lt_iff₀ (Real.log_pos hlogP)).mp hF).le.trans
      (mul_le_mul_of_nonneg_left hlog hG.le)
  have hw := sieveWeight_pos (s := z.primesLE) (fun _ ↦ Nat.prime_of_mem_primesLE)
  apply (inv_le_iff_one_le_mul₀ hw).mpr
  nlinarith only [sieveWeight_mul_sigma (z := z), mul_le_mul_of_nonneg_left hg hw.le]

private lemma sum_inv_prime_le_log {z : ℕ} {C : ℝ}
    (h : (sieveWeight z.primesLE)⁻¹ ≤ C * Real.log z) :
    (∑ p ∈ z.primesLE, (p : ℝ)⁻¹) ≤ Real.log (C * Real.log z) := by
  have hw := sieveWeight_pos (s := z.primesLE) (fun _ ↦ Nat.prime_of_mem_primesLE)
  refine le_trans ?_ (Real.log_le_log (inv_pos.mpr hw) h)
  rw [Real.log_inv, sieveWeight, Real.log_prod]
  · rw [← sum_neg_distrib]
    refine sum_le_sum fun p hp ↦ ?_
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.one_lt_of_mem_primesLE hp)
    linarith [Real.log_le_sub_one_of_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))]
  · intro p hp
    exact (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by
      exact_mod_cast (Nat.one_lt_of_mem_primesLE hp)))).ne'

-- With u = log a, this cutoff keeps the inclusion–exclusion error below √a.
private noncomputable def cutoff (u : ℝ) : ℕ := ⌊u * Real.log u / 32⌋₊

private lemma cutoff_bounds :
    ∀ᶠ u : ℝ in atTop, u ≤ cutoff u ∧ u * Real.log u / 64 ≤ cutoff u ∧
      (cutoff u : ℝ) ≤ u * Real.log u / 32 ∧ (cutoff u : ℝ) ≤ u ^ 2 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 64] with u hu hl
  have hmul : 64 * u ≤ u * Real.log u := by nlinarith
  have hlog := Real.log_le_self (le_trans zero_le_one hu)
  have hfloor := Nat.lt_floor_add_one (u * Real.log u / 32)
  have hf := Nat.floor_le (show 0 ≤ u * Real.log u / 32 by positivity)
  unfold cutoff
  refine ⟨by linarith, by linarith, hf, hf.trans ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hlog (le_trans zero_le_one hu), sq_nonneg u]

private lemma tendsto_cutoff : Tendsto cutoff atTop atTop := by
  refine tendsto_atTop.2 fun n ↦ ?_
  filter_upwards [eventually_ge_atTop (n : ℝ), cutoff_bounds] with u hu hz
  exact_mod_cast hu.trans hz.1

set_option maxHeartbeats 600000 in
-- The proof combines the eventual comparisons for the cutoff, interval, and counting errors.
/-- In an interval of length ε √a log a, the sieve leaves more rough integers than
can be removed by square divisors and the prime-pair obstructions. -/
private lemma eventually_cyclic_mem_Ioc {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ a : ℕ in atTop, ∃ n : ℕ, IsCyclicNumber n ∧ a < n ∧
      (n : ℝ) ≤ a + ε * Real.sqrt a * Real.log a := by
  classical
  obtain ⟨C, hC, hW⟩ := inv_sieveWeight_le_log
  -- The inverse-square tail at this cutoff absorbs the factor of log b.
  let δ := 1 / (3584 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let u (a : ℕ) := Real.log (a : ℝ)
  let z (a : ℕ) := cutoff (u a)
  let b (a : ℕ) := a + ⌊ε * Real.sqrt a * u a⌋₊
  have hu : Tendsto u atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hz : Tendsto z atTop atTop := tendsto_cutoff.comp hu
  have hb : Tendsto b atTop atTop :=
    tendsto_atTop_mono (fun a ↦ Nat.le_add_right _ _) tendsto_id
  have hsqrt : Tendsto (fun a : ℕ ↦ Real.sqrt (a : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlen : ∀ᶠ a : ℕ in atTop, ε * Real.sqrt (a : ℝ) * u a ≤ a := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (inv_pos.mpr hε)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually h, eventually_ge_atTop (1 : ℕ)]
      with a ha ha1
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    rw [← Real.sqrt_eq_rpow, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg haR), abs_of_nonneg (Real.sqrt_nonneg _)] at ha
    have hh : ε * u a ≤ Real.sqrt a := (le_inv_mul_iff₀ hε).mp ha
    have hs := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg a)
    rw [Real.mul_self_sqrt (Nat.cast_nonneg a)] at hs
    nlinarith only [hs]
  have hlong : ∀ᶠ a : ℕ in atTop, 2 ≤ ε * Real.sqrt (a : ℝ) * u a := by
    have h : Tendsto (fun a : ℕ ↦ ε * Real.sqrt (a : ℝ) * u a) atTop atTop :=
      (hsqrt.const_mul_atTop hε).atTop_mul_atTop₀ hu
    exact h.eventually_ge_atTop 2
  have herr := hu.eventually ((Real.isLittleO_pow_log_id_atTop (n := 2)).bound
    (show 0 < ε / (208 * C) by positivity))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hu.eventually_ge_atTop (max 1 (2 * C)),
    (Real.tendsto_log_atTop.comp hu).eventually_ge_atTop 1, hu.eventually cutoff_bounds,
    hz.eventually primeCounting_upper, hz.eventually hW, hb.eventually hW,
    hz.eventually (prime_tail_small hδ), hlen, hlong, herr] with
    a ha hu1 hL hzB hπ hWz hWb ht hlen hlong herr
  let L := Real.log (u a)
  let H := (b a : ℝ) - a
  have hu1' : 1 ≤ u a := (le_max_left ..).trans hu1
  have hu0 : 0 < u a := zero_lt_one.trans_le hu1'
  have hLu : 0 < L := zero_lt_one.trans_le hL
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hza : 0 < (z a : ℝ) := zero_lt_one.trans_le (hu1'.trans hzB.1)
  have hlogz : L ≤ Real.log (z a) := Real.log_le_log (by linarith) hzB.1
  have hlogz' : Real.log (z a) ≤ 2 * L := by
    simpa [Real.log_pow, L] using Real.log_le_log hza hzB.2.2.2
  have hab : a ≤ b a := Nat.le_add_right _ _
  have hbR : 0 < (b a : ℝ) := haR.trans_le (by exact_mod_cast hab)
  have hH : H = (⌊ε * Real.sqrt (a : ℝ) * u a⌋₊ : ℝ) := by
    unfold H b
    push_cast
    ring
  have hlower : ε * Real.sqrt (a : ℝ) * u a / 2 ≤ H := by
    rw [hH]
    linarith [Nat.lt_floor_add_one (ε * Real.sqrt (a : ℝ) * u a)]
  have hHpos : 0 < H := (by positivity : 0 < ε * Real.sqrt (a : ℝ) * u a / 2).trans_le hlower
  have hHle : H ≤ ε * Real.sqrt (a : ℝ) * u a := by
    rw [hH]
    exact Nat.floor_le (by positivity)
  have hb2 : (b a : ℝ) ≤ 2 * a := by dsimp [H] at hHle; linarith
  have hlogb : Real.log (b a : ℝ) ≤ 2 * u a := by
    have h := Real.log_le_log hbR hb2
    rw [Real.log_mul (by norm_num) haR.ne'] at h
    have h2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num :
      (0 : ℝ) < 2)]
    linarith [h, h2, hu1']
  have hsqrtb : Real.sqrt (b a : ℝ) ≤ 2 * Real.sqrt (a : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt haR.le]
  have heIE : (2 : ℝ) ^ #(z a).primesLE ≤ Real.sqrt (a : ℝ) := by
    rw [Nat.primesLE_card_eq_primeCounting, ← Real.log_le_log_iff (by positivity)
      (Real.sqrt_pos.mpr haR), Real.log_pow, Real.log_sqrt haR.le]
    have hc : ((z a).primeCounting : ℝ) ≤ u a / 2 := calc
      _ ≤ 3 * (z a : ℝ) / Real.log (z a) := hπ
      _ ≤ 3 * (u a * L / 32) / L := by
        gcongr
        exact hzB.2.2.1
      _ ≤ _ := by field_simp; linarith
    nlinarith [mul_le_mul_of_nonneg_left (show Real.log (2 : ℝ) ≤ 1 by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)])
      (Nat.cast_nonneg (α := ℝ) (z a).primeCounting)]
  have hweight : 1 / (2 * C * L) ≤ sieveWeight (z a).primesLE := by
    have hw := sieveWeight_pos (s := (z a).primesLE) (fun _ ↦ Nat.prime_of_mem_primesLE)
    rw [div_le_iff₀ (by positivity), mul_comm]
    apply (inv_le_iff_one_le_mul₀ hw).mp
    exact hWz.trans (by nlinarith [mul_le_mul_of_nonneg_left hlogz' hC.le])
  let s := (Nat.primesLE ⌊Real.sqrt (b a : ℝ)⌋₊).filter (z a < ·)
  have hs (p) (hp : p ∈ s) : p.Prime ∧ z a < p :=
    ⟨Nat.prime_of_mem_primesLE (mem_filter.mp hp).1, (mem_filter.mp hp).2⟩
  have hfirst : (3 + 2 * Real.log (b a : ℝ)) * (∑ p ∈ s, (p : ℝ)⁻¹ ^ 2) ≤
      1 / (8 * C * L) := calc
    _ ≤ (7 * u a) * (δ / (u a * L / 64)) := by
      have hlog0 := Real.log_nonneg (show (1 : ℝ) ≤ b a by exact_mod_cast ha.trans hab)
      refine mul_le_mul (by linarith) ((ht s hs).trans ?_) (by positivity) (by positivity)
      exact div_le_div_of_nonneg_left hδ.le (by positivity) hzB.2.1
    _ = _ := by dsimp [δ]; field_simp; ring
  have hsum : ∑ p ∈ s, (p : ℝ)⁻¹ ≤ 2 * L := calc
    _ ≤ ∑ p ∈ (b a).primesLE, (p : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ ↦ by positivity)
      intro p hp
      refine (Nat.primesLE_mono ?_) (mem_filter.mp hp).1
      have h := Nat.floor_le (Real.sqrt_nonneg (b a : ℝ))
      exact_mod_cast h.trans (Real.sqrt_le_self_iff.mpr (Or.inr (by exact_mod_cast ha.trans hab)))
    _ ≤ Real.log (C * Real.log (b a : ℝ)) := sum_inv_prime_le_log hWb
    _ ≤ _ := by
      have hc : 0 < C * Real.log (b a : ℝ) := (inv_pos.mpr
        (sieveWeight_pos (fun _ ↦ Nat.prime_of_mem_primesLE))).trans_le hWb
      have hh : C * Real.log (b a : ℝ) ≤ (u a) ^ 2 := by
        have := (le_max_right (1 : ℝ) (2 * C)).trans hu1
        nlinarith [mul_le_mul_of_nonneg_left hlogb hC.le,
          mul_le_mul_of_nonneg_right this (show 0 ≤ u a by linarith)]
      simpa [Real.log_pow, L] using Real.log_le_log hc hh
  have hsecond : (2 : ℝ) ^ #(z a).primesLE +
      3 * Real.sqrt (b a : ℝ) * (∑ p ∈ s, (p : ℝ)⁻¹) ≤ H / (8 * C * L) := by
    have hsum0 : 0 ≤ ∑ p ∈ s, (p : ℝ)⁻¹ := sum_nonneg fun _ _ ↦ by positivity
    have hm : 3 * Real.sqrt (b a : ℝ) * (∑ p ∈ s, (p : ℝ)⁻¹) ≤
        12 * Real.sqrt (a : ℝ) * L := by
      calc
        _ ≤ 3 * (2 * Real.sqrt (a : ℝ)) * (2 * L) := by gcongr
        _ = _ := by ring
    have herr' : L ^ 2 ≤ ε / (208 * C) * u a := by
      change ‖L ^ 2‖ ≤ ε / (208 * C) * ‖u a‖ at herr
      simpa only [Real.norm_of_nonneg (sq_nonneg L), Real.norm_of_nonneg hu0.le] using herr
    have hscale : (8 * C * L) * (1 + 12 * L) ≤ ε * u a / 2 := by
      have h₁ : L * (1 + 12 * L) ≤ 13 * L ^ 2 := by
        change 1 ≤ L at hL
        nlinarith only [mul_le_mul_of_nonneg_left hL hLu.le]
      have h₂ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 8 * C by positivity)
      have h₃ := (le_div_iff₀ (show 0 < 208 * C by positivity)).mp
        (show L ^ 2 ≤ ε * u a / (208 * C) by simpa [div_mul_eq_mul_div] using herr')
      nlinarith only [h₂, h₃]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ (Real.sqrt (a : ℝ) * (1 + 12 * L)) * (8 * C * L) := by
        gcongr
        nlinarith only [heIE, hm]
      _ ≤ H := by
        calc
          _ = Real.sqrt (a : ℝ) * ((8 * C * L) * (1 + 12 * L)) := by ring
          _ ≤ Real.sqrt (a : ℝ) * (ε * u a / 2) := by gcongr
          _ ≤ H := by nlinarith only [hlower]
  by_contra! he
  have hfilters : {n ∈ Ioc a (b a) | ∀ p ∈ (z a).primesLE, ¬p ∣ n} =
      {n ∈ Ioc a (b a) | (∀ p ∈ (z a).primesLE, ¬p ∣ n) ∧ ¬ IsCyclicNumber n} := by
    ext n
    simp only [mem_filter, mem_Ioc]
    refine ⟨fun ⟨hn, hp⟩ ↦ ⟨hn, hp, fun hc ↦ (he n hc hn.1).not_ge ?_⟩,
      fun ⟨hn, hp, _⟩ ↦ ⟨hn, hp⟩⟩
    have hn' : (n : ℝ) ≤ (b a : ℝ) := by exact_mod_cast hn.2
    dsimp [H] at hHle
    linarith
  have hlo := sieve_lower hab (s := (z a).primesLE) (fun _ ↦ Nat.prime_of_mem_primesLE)
  rw [hfilters] at hlo
  have hhi := bad_upper (z := z a) hab (ha.trans hab)
  change _ ≤ (H * (3 + 2 * Real.log (b a : ℝ))) * _ + 3 * Real.sqrt (b a : ℝ) * _ at hhi
  have hmain := mul_le_mul_of_nonneg_left hfirst hHpos.le
  have hlower' := mul_le_mul_of_nonneg_left hweight hHpos.le
  change H * sieveWeight (z a).primesLE - _ ≤ _ at hlo
  have heq : H * (1 / (2 * C * L)) = 4 * (H / (8 * C * L)) := by ring
  rw [heq] at hlower'
  have heq' : H * (1 / (8 * C * L)) = H / (8 * C * L) := by ring
  rw [heq'] at hmain
  nlinarith only [hlo.trans hhi, hsecond, hmain, hlower',
    div_pos hHpos (show 0 < 8 * C * L by positivity)]

private lemma infinite_cyclic : (Set.ofPred IsCyclicNumber).Infinite :=
  Nat.infinite_setOfPred_prime.mono fun _ hp ↦ prime_cyclic hp

private lemma nth_cyclic_le_nth_prime (n : ℕ) : Nat.nth IsCyclicNumber n ≤ Nat.nth Nat.Prime n := by
  classical
  apply (Nat.gc_count_nth Nat.infinite_setOfPred_prime _ n).mp
  calc
    _ ≤ Nat.count IsCyclicNumber (Nat.nth IsCyclicNumber n) :=
      Nat.count_mono_left (fun _ _ hp ↦ prime_cyclic hp)
    _ = n := Nat.count_nth_of_infinite infinite_cyclic n

end MetaMathlibExt.cyclicNumber_gap_isLittleO_of_riemannHypothesis

namespace MetaMathlibExt

open cyclicNumber_gap_isLittleO_of_riemannHypothesis in
set_option linter.unusedVariables false in
-- Keep the hypothesis of the original statement.
/-- **Gaps between cyclic numbers under the Riemann hypothesis.** Assume the Riemann hypothesis.
Let $c_1 < c_2 < \cdots$ be the cyclic numbers in increasing order and $p_1 < p_2 < \cdots$ the
primes in increasing order. Then the gaps $d_n = c_{n+1} - c_n$ between consecutive cyclic
numbers satisfy $d_n = o(\sqrt{p_n} \log p_n)$ as $n \to \infty$.

Source: John M. Campbell and Joel E. Cohen, *Cyclic Numbers and Gaps*, INTEGERS 25 (2025),
Article A23, Theorem 2 (`integers-2025-A23-thm-2`). -/
public theorem cyclicNumber_gap_isLittleO_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    let c : ℕ → ℝ := fun n => (Nat.nth IsCyclicNumber (n - 1) : ℝ)
    let p : ℕ → ℝ := fun n => (Nat.nth Nat.Prime (n - 1) : ℝ)
    (fun n => c (n + 1) - c n) =o[atTop] (fun n => Real.sqrt (p n) * Real.log (p n)) := by
  dsimp only
  refine isLittleO_iff.2 fun ε hε ↦ ?_
  let c := Nat.nth IsCyclicNumber
  let p := Nat.nth Nat.Prime
  have hc : Tendsto (fun n : ℕ ↦ c (n - 1)) atTop atTop :=
    (Nat.nth_strictMono infinite_cyclic).tendsto_atTop.comp (tendsto_sub_atTop_nat 1)
  filter_upwards [hc.eventually (eventually_cyclic_mem_Ioc hε),
    eventually_ge_atTop (1 : ℕ)] with n ⟨m, hm, hm', hmb⟩ hn
  have hin : c (n - 1 + 1) ≤ m := (Nat.nth_add_one_le_iff infinite_cyclic hm).2 hm'
  have he : n - 1 + 1 = n := by omega
  rw [he] at hin
  have hle : (c (n - 1) : ℝ) ≤ p (n - 1) := by exact_mod_cast nth_cyclic_le_nth_prime (n - 1)
  have hpos : (1 : ℝ) ≤ c (n - 1) := by
    exact_mod_cast (Nat.nth_mem_of_infinite infinite_cyclic (n - 1)).1
  have hnorm : 0 ≤ (c n : ℝ) - c (n - 1) := by
    exact sub_nonneg.mpr (by exact_mod_cast Nat.nth_monotone infinite_cyclic (Nat.sub_le ..))
  change ‖(c (n + 1 - 1) : ℝ) - c (n - 1)‖ ≤ ε * ‖Real.sqrt (p (n - 1)) * Real.log (p (n - 1))‖
  rw [Nat.add_sub_cancel, Real.norm_of_nonneg hnorm, Real.norm_of_nonneg (mul_nonneg
    (Real.sqrt_nonneg _) (Real.log_nonneg (hpos.trans hle)))]
  calc
    _ ≤ ε * Real.sqrt (c (n - 1)) * Real.log (c (n - 1)) := by
      have h : (c n : ℝ) ≤ m := by exact_mod_cast hin
      linarith
    _ ≤ _ := by
      rw [mul_assoc]
      gcongr

end MetaMathlibExt
