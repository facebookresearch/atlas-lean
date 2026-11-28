/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.PrimeInterval.Breusch.Theta

/-!
# Sums of distinct primes congruent to five modulo six

Makowski's theorem gives a representation of each natural number above 161.
We estimate the sum of the available primes using the nonprincipal character modulo three,
then extend an interval of subset sums one prime at a time.

The character `CharModThree.chi` and its multiplicativity, partial-sum and log-weighted
partial-sum lemmas are public for reuse by other estimates over primes modulo three.
-/

namespace MathlibExt.NumberTheory.CharModThree

open Finset

/-- The nonprincipal Dirichlet character modulo three as a real-valued function on the natural
numbers: `chi n` is `1` when `n % 3 = 1`, `-1` when `n % 3 = 2`, and `0` when `3` divides `n`. -/
@[expose] public def chi (n : ℕ) : ℝ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

/-- `chi` is completely multiplicative: `chi (m * n) = chi m * chi n` for all natural numbers
`m` and `n`. -/
public lemma chi_mul (m n : ℕ) : chi (m * n) = chi m * chi n := by
  simp only [chi, Nat.mul_mod m n]
  have hm := Nat.mod_lt m (by decide : 0 < 3)
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  interval_cases m % 3 <;> interval_cases n % 3 <;> norm_num

/-- `chi` is the Legendre symbol modulo three: `chi n = (n / 3)`, the Legendre symbol
`legendreSym 3 n` cast to the reals, for every natural number `n`. -/
public lemma chi_eq_legendreSym (n : ℕ) : chi n = (legendreSym 3 (n : ℤ) : ℝ) := by
  rw [legendreSym.mod 3 (n : ℤ), ← Int.natCast_mod]
  have hn := Nat.mod_lt n (by decide : 0 < 3)
  simp only [chi]
  interval_cases h : n % 3
  · simp [legendreSym.at_zero]
  · simp [legendreSym.at_one]
  · simp only [Nat.cast_ofNat]
    rw [legendreSym.at_two (by decide)]
    norm_num [ZMod.χ₈_nat_eq_if_mod_eight]

/-- For every natural number `n`, the partial sum `∑_{0 < i ≤ n} chi i` equals `1` when
`n % 3 = 1` and `0` otherwise. -/
public lemma sum_chi (n : ℕ) :
    ∑ i ∈ Ioc 0 n, chi i = if n % 3 = 1 then 1 else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _), ih]
    simp only [chi]
    split_ifs <;> first | omega | norm_num

/-- For every natural number `n`, the log-weighted partial sum `∑_{0 < i ≤ n} chi i * log i` is at
most `log n` when `n % 3 = 1` and at most `0` otherwise. -/
public lemma sum_chi_log (n : ℕ) :
    ∑ i ∈ Ioc 0 n, chi i * Real.log i ≤ if n % 3 = 1 then Real.log n else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le _)]
    refine (add_le_add_left ih _).trans ?_
    have hlog : Real.log n ≤ Real.log (n + 1 : ℕ) := by
      rcases n with _ | n
      · simp
      · apply Real.log_le_log (by positivity)
        exact_mod_cast Nat.le_succ _
    simp only [chi]
    split_ifs <;> first | omega | simp_all

end MathlibExt.NumberTheory.CharModThree

namespace MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted

open Finset ArithmeticFunction MathlibExt.NumberTheory.CharModThree

-- Twist the divisor identity for log by χ and reverse the order of summation.
private lemma twist_sum (N : ℕ) :
    ∑ d ∈ Ioc 0 N, chi d * Λ d * (if N / d % 3 = 1 then 1 else 0) ≤ Real.log N := by
  let f : ArithmeticFunction ℝ := ⟨fun d => chi d * Λ d, by simp⟩
  let g : ArithmeticFunction ℝ := ⟨chi, by norm_num [chi]⟩
  have term (n : ℕ) : (f * g) n = chi n * Real.log n := by
    rw [ArithmeticFunction.mul_apply, ← ArithmeticFunction.vonMangoldt_sum,
      ← Nat.sum_divisorsAntidiagonal (fun i _ => Λ i), Finset.mul_sum]
    refine sum_congr rfl fun ⟨a, b⟩ hab => ?_
    change chi a * Λ a * chi b = chi n * Λ a
    rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, chi_mul]
    ring
  have h := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum f g N
  change _ = ∑ d ∈ Ioc 0 N, chi d * Λ d * ∑ i ∈ Ioc 0 (N / d), chi i at h
  simp_rw [term, sum_chi] at h
  rw [← h]
  refine (sum_chi_log N).trans ?_
  split_ifs with hN
  · rfl
  · rcases N with _ | N
    · simp
    · exact Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 N)

private def eligible (p : ℕ) : Prop := p.Prime ∧ p % 6 = 5

private instance decidableEligible (p : ℕ) : Decidable (eligible p) := by
  unfold eligible
  infer_instance

private def primes (n : ℕ) := (Ioc 0 n).filter eligible

private def primeSum (n : ℕ) := ∑ p ∈ primes n, p

-- In (m, 2m] the coefficient given by the partial character sum is one.
-- Elsewhere the primes congruent to one modulo three contribute nonnegatively.
private lemma band_le (m : ℕ) :
    Chebyshev.psi (2 * m : ℕ) - Chebyshev.psi m ≤
      Real.log (2 * m : ℕ) + 2 * ∑ d ∈ Ioc 0 (2 * m), (if d % 3 = 1 then 0 else Λ d) := by
  have point (d : ℕ) (hd : d ∈ Ioc 0 (2 * m)) :
      (if m < d then Λ d else 0) ≤
        chi d * Λ d * (if 2 * m / d % 3 = 1 then 1 else 0) +
        2 * (if d % 3 = 1 then 0 else Λ d) := by
    have hdiv (h : m < d) : 2 * m / d = 1 :=
      Nat.div_eq_of_lt_le (by simpa using (mem_Ioc.mp hd).2) (by omega)
    simp only [chi]
    split_ifs <;> first | omega | simp_all
    all_goals linarith [ArithmeticFunction.vonMangoldt_nonneg (n := d)]
  have hs := Finset.sum_le_sum point
  rw [sum_add_distrib, ← mul_sum] at hs
  suffices h : Chebyshev.psi (2 * m : ℕ) - Chebyshev.psi m =
      ∑ d ∈ Ioc 0 (2 * m), (if m < d then Λ d else 0) by
    rw [h]
    exact hs.trans (add_le_add_left (twist_sum _) _)
  have heq : (Ioc 0 (2 * m)).filter (m < ·) = Ioc m (2 * m) := by ext; simp; omega
  rw [← sum_filter, heq, Chebyshev.psi, Chebyshev.psi]
  simp only [Nat.floor_natCast]
  have h := sum_Ioc_consecutive (f := fun d => Λ d) (Nat.zero_le m) (show m ≤ 2 * m by omega)
  linarith

private noncomputable def otherResidueWeight (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n, if d % 3 = 1 then 0 else Λ d

private lemma otherResidueWeight_mono : Monotone otherResidueWeight := by
  intro m n h
  apply sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right h)
  intro i _ _
  split_ifs <;> positivity

open MathlibExt.NumberTheory.BreuschWanted.Internal in
private lemma log_le_hundredth {p : ℕ} (hp : 1000 ≤ p) : Real.log p ≤ p / 100 := by
  have hx : (1000 : ℝ) ≤ p := by exact_mod_cast hp
  have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < p / 1000 by positivity)
  rw [Real.log_div (by positivity) (by norm_num),
    show (1000 : ℝ) = 10 ^ 3 by norm_num, Real.log_pow] at hh
  linarith [log10_lt]

-- Small factors cost at most ψ(1000), and higher prime powers cost at most ψ(x) − θ(x).
-- Each remaining term is the logarithm of an eligible prime.
private lemma otherResidueWeight_le {x : ℕ} (hx : 1000 ≤ x) :
    otherResidueWeight x ≤
      Chebyshev.psi 1000 + (Chebyshev.psi x - Chebyshev.theta x) + primeSum x / 100 := by
  have hsmall : ((Ioc 0 x).filter (· ≤ 1000)) = Ioc 0 1000 := by ext; simp; omega
  have hpsi : Chebyshev.psi 1000 = ∑ d ∈ Ioc 0 x, (if d ≤ 1000 then Λ d else 0) := by
    rw [← sum_filter, hsmall, Chebyshev.psi]
    norm_num
  rw [hpsi, Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter,
    primeSum, Nat.cast_sum, primes, sum_filter, Finset.sum_div,
    ← sum_add_distrib, ← sum_add_distrib]
  apply sum_le_sum
  intro d hd
  by_cases h : d ≤ 1000
  · simp only [h, ite_true]
    split_ifs <;> linarith [vonMangoldt_nonneg (n := d), Nat.cast_nonneg (α := ℝ) d]
  by_cases hp : d.Prime
  · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    by_cases hr : d % 3 = 1
    · by_cases hg : eligible d <;> simp [hr, h, hp, hg, div_nonneg]
    have h3 : d % 3 ≠ 0 := fun h0 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)
      omega
    have hg : eligible d := ⟨hp, by have := hp.eq_two_or_odd; omega⟩
    simpa [hr, h, hp, hg] using log_le_hundredth (p := d) (by omega)
  · have hg : ¬ eligible d := fun h => hp h.1
    simp only [hp, hg, h, ite_false, not_false_eq_true, ite_true, zero_div, zero_add, add_zero]
    split_ifs <;> simp

-- Four dyadic bands capture enough of the full Chebyshev weight that the primes
-- congruent to five must already sum to more than twice the upper endpoint.
open MathlibExt.NumberTheory.BreuschWanted.Internal in
private lemma twice_le_primeSum {t : ℕ} (ht : 10 ^ 7 ≤ 16 * t) :
    2 * (16 * t) ≤ primeSum (16 * t) := by
  let x := 16 * t
  have hx : (10 ^ 7 : ℝ) ≤ x := by exact_mod_cast ht
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have band (m : ℕ) (hm : 2 * m ≤ x) :
      Chebyshev.psi (2 * m : ℕ) - Chebyshev.psi m ≤ Real.log x + 2 * otherResidueWeight x := by
    refine (band_le m).trans (add_le_add ?_
      (mul_le_mul_of_nonneg_left (otherResidueWeight_mono hm) (by norm_num)))
    rcases m with _ | m
    · simp [Real.log_nonneg hx1]
    · exact Real.log_le_log (by positivity) (by exact_mod_cast hm)
  have hb₁ := band t (by dsimp [x]; omega)
  have hb₂ := band (2 * t) (by dsimp [x]; omega)
  have hb₃ := band (4 * t) (by dsimp [x]; omega)
  have hb₄ := band (8 * t) (by dsimp [x]; omega)
  norm_num [← Nat.mul_assoc] at hb₂ hb₃ hb₄
  have hu := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg t (α := ℝ))
  have hs := Chebyshev.psi_le_const_mul_self (by norm_num : (0 : ℝ) ≤ 1000)
  have hlo := Chebyshev.psi_ge_of_seven_le (n := x) (by dsimp [x]; omega)
  have he := Chebyshev.psi_sub_theta_le hx1
  have hlog := log_le_sqrt06 x hx
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity)
  have herr : Chebyshev.psi x - Chebyshev.theta x ≤ 0.012 * x := by
    nlinarith [mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg x)]
  have hsqrt : Real.sqrt x ≤ x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (Real.one_le_sqrt.mpr hx1)) (Real.sqrt_nonneg x)]
  have hl : Real.log x ≤ 0.006 * x := hlog.trans (by gcongr)
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hw := otherResidueWeight_le (x := x) (by dsimp [x]; omega)
  have hlow : 0.69 * x ≤ Chebyshev.psi x := by
    nlinarith [mul_le_mul_of_nonneg_right log2_gt.le (Nat.cast_nonneg x (α := ℝ))]
  change 2 * x ≤ primeSum x
  have hxt : (x : ℝ) = 16 * t := by simp [x]
  have := mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg t (α := ℝ))
  rw [← hxt] at hb₄
  push_cast at hb₁
  exact_mod_cast (show 2 * (x : ℝ) ≤ primeSum x by linarith)

private lemma primes_mono : Monotone primes := by
  intro m n h
  exact filter_subset_filter _ (Ioc_subset_Ioc_right h)

private lemma primeSum_mono : Monotone primeSum := by
  intro m n h
  exact sum_le_sum_of_subset (primes_mono h)

private lemma add_prime {u p : ℕ} (hu : u < p) (hp : eligible p) :
    primeSum u + p ≤ primeSum p := by
  have hf : p ∉ primes u := by simp [primes]; omega
  have hs : insert p (primes u) ⊆ primes p := by
    apply insert_subset
    · exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.1.pos, le_rfl⟩, hp⟩
    · exact primes_mono hu.le
  simpa [primeSum, sum_insert hf, Nat.add_comm] using (sum_le_sum_of_subset (f := fun i => i) hs)

-- A sparse increasing list suffices to bridge the finite range: before each new prime,
-- the accumulated weight already covers the gap to it.
private def bridge (u w limit : ℕ) : List ℕ → Bool
  | [] => decide (limit + 324 ≤ w)
  | p :: ps => decide (eligible p ∧ u < p ∧ p + 324 ≤ w) && bridge p (w + p) limit ps

private lemma bridge_bound {u w limit : ℕ} {ps : List ℕ} (h : bridge u w limit ps)
    (hw : w ≤ primeSum u) {m : ℕ} (hu : u ≤ m) (hm : m ≤ limit) : m + 324 ≤ primeSum m := by
  induction ps generalizing u w with
  | nil =>
    simp [bridge] at h
    exact (by omega : m + 324 ≤ w) |>.trans (hw.trans (primeSum_mono hu))
  | cons p ps ih =>
    simp only [bridge, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hp, hup, hpw⟩, hps⟩ := h
    rcases le_or_gt p m with hpm | hpm
    · exact ih hps ((Nat.add_le_add_right hw p).trans (add_prime hup hp)) hpm
    · exact (by omega : m + 324 ≤ w) |>.trans (hw.trans (primeSum_mono hu))

set_option maxRecDepth 4096 in
private lemma primeSum_base : primeSum 167 = 1433 := by decide

private lemma primeSum_bound {m : ℕ} (hm : 167 ≤ m) : m + 324 ≤ primeSum m := by
  by_cases h : m ≤ 10000016
  · apply bridge_bound (u := 167) (w := 1433) (limit := 10000016)
      (ps := [1109, 2213, 4421, 8849, 17681, 35381, 70709, 141461, 282917, 565793,
        1131629, 2263229, 4526447, 9052943]) _ primeSum_base.ge hm h
    norm_num [bridge, eligible]
  · have hx : 10 ^ 7 ≤ 16 * (m / 16) := by omega
    exact (by omega : m + 324 ≤ 2 * (16 * (m / 16))) |>.trans
      ((twice_le_primeSum hx).trans (primeSum_mono (by omega)))

-- Bit n records that the list has a subset of sum n.
private def subsetBits : List ℕ → ℕ
  | [] => 1
  | p :: ps =>
    let b := subsetBits ps
    b ||| (b <<< p)

private lemma subsetBits_sound {ps : List ℕ} (hd : ps.Nodup) {n : ℕ}
    (h : (subsetBits ps).testBit n) : ∃ S ⊆ ps.toFinset, ∑ p ∈ S, p = n := by
  induction ps generalizing n with
  | nil =>
    have hn := Nat.testBit_one_eq_true_iff_self_eq_zero.mp h
    exact ⟨∅, empty_subset _, by simp [hn]⟩
  | cons p ps ih =>
    rw [List.nodup_cons] at hd
    simp only [subsetBits, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨S, hS, hs⟩ := ih hd.2 h
      exact ⟨S, hS.trans (by simp), hs⟩
    · by_cases hn : p ≤ n
      · have hb : (subsetBits ps).testBit (n - p) := by simpa [hn] using h
        obtain ⟨S, hS, hs⟩ := ih hd.2 hb
        have hp : p ∉ S := fun h => hd.1 (List.mem_toFinset.mp (hS h))
        refine ⟨insert p S, by simpa using insert_subset_insert p hS, ?_⟩
        rw [sum_insert hp, hs]
        omega
      · simp [hn] at h

private def initialPrimes : List ℕ :=
  [5, 11, 17, 23, 29, 41, 47, 53, 59, 71, 83, 89, 101, 107, 113, 131, 137, 149, 167]

set_option maxRecDepth 8192 in
private lemma initial_interval {n : ℕ} (lo : 162 ≤ n) (hi : n + 162 ≤ primeSum 167) :
    ∃ S ⊆ primes 167, ∑ p ∈ S, p = n := by
  have bits : ∀ k < 1110, (subsetBits initialPrimes).testBit (162 + k) = true := by decide
  rw [primeSum_base] at hi
  have hb := bits (n - 162) (by omega)
  rw [show 162 + (n - 162) = n by omega] at hb
  obtain ⟨S, hS, he⟩ := subsetBits_sound (ps := initialPrimes) (by decide) hb
  exact ⟨S, hS.trans (by decide : initialPrimes.toFinset ⊆ primes 167), he⟩

-- The old interval and its translate by the new prime cover the enlarged interval:
-- their endpoints meet because primeSum m is at least m + 2 · 162.
private lemma interval {m : ℕ} (hm : 167 ≤ m) (n : ℕ) (lo : 162 ≤ n)
    (hi : n + 162 ≤ primeSum m) : ∃ S ⊆ primes m, ∑ p ∈ S, p = n := by
  induction m, hm using Nat.le_induction generalizing n with
  | base => exact initial_interval lo hi
  | succ m hm ih =>
    have hf : m + 1 ∉ primes m := by simp [primes]
    have hsucc : primes (m + 1) =
        if eligible (m + 1) then insert (m + 1) (primes m) else primes m := by
      ext p
      simp only [primes, mem_filter, mem_Ioc]
      split_ifs <;> simp_all [primes] <;> grind
    by_cases hn : n + 162 ≤ primeSum m
    · obtain ⟨S, hS, he⟩ := ih _ lo hn
      exact ⟨S, hS.trans (primes_mono (Nat.le_succ _)), he⟩
    by_cases hp : eligible (m + 1)
    · have hmass : primeSum (m + 1) = m + 1 + primeSum m := by simp [primeSum, hsucc, hp, hf]
      rw [hmass] at hi
      have hgap := primeSum_bound hm
      obtain ⟨S, hS, he⟩ := ih (n - (m + 1)) (by omega) (by omega)
      refine ⟨insert (m + 1) S, by simpa [hsucc, hp] using insert_subset_insert (m + 1) hS, ?_⟩
      rw [sum_insert (fun h => hf (hS h)), he]
      omega
    · have hmass : primeSum (m + 1) = primeSum m := by simp [primeSum, hsucc, hp]
      omega

/-- **Makowski's theorem on sums of distinct primes of the form $6k - 1$.** Every natural number
$n > 161$ is the sum of the elements of some finite set of primes $p$ with $p \equiv 5 \pmod 6$;
that is, $n$ is a sum of distinct primes of the form $6k - 1$.

Source: Elchin Hasanalizade, "Sums of Distinct
Eisenstein Primes", Lemma 3 (citing Makowski). -/
public theorem eq_sum_distinct_primes_modEq_five (n : ℕ)
    (hn : 161 < n) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ p % 6 = 5) ∧
      (∑ p ∈ S, p) = n := by
  let m := max n 167
  have hm : 167 ≤ m := le_max_right _ _
  obtain ⟨S, hS, hs⟩ := interval hm n (by omega) (by
    have := primeSum_bound hm
    have : n ≤ m := le_max_left _ _
    omega)
  exact ⟨S, fun p hp => (mem_filter.mp (hS hp)).2, hs⟩

end MathlibExt.NumberTheory.DistinctEisensteinPrimesWanted
