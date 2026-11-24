/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# The Pollack–Pomerance sieve bound

The count of integers avoiding a set of prime factors has a uniform upper bound in terms of
the sum of the reciprocals of the excluded primes up to the counting limit.
Chebyshev’s estimate reduces the count to a harmonic sum. A finite Euler product at an
exponent just above one bounds this sum uniformly over the excluded primes.
-/

namespace MetaMathlibExt

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

namespace card_free_of_prime_set_le_exp_neg_sum_inv

open Classical in
private noncomputable def sifted (P : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Ioc 0 N).filter (fun n ↦ ∀ p ∈ P, ¬p ∣ n)

/-- Weighting by the logarithm reduces the count to a harmonic sum over the same integers. -/
private theorem count_le_harmonic (P : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ((sifted P ⌊x⌋₊).card : ℝ) * (1 + log x) ≤
      (log 4 + 5) * x * ∑ n ∈ sifted P ⌊x⌋₊, (n : ℝ)⁻¹ := by
  classical
  let N := ⌊x⌋₊
  let S := sifted P N
  let f : ArithmeticFunction ℝ :=
    ⟨fun n ↦ if n ≠ 0 ∧ ∀ p ∈ P, ¬p ∣ n then 1 else 0, by simp⟩
  have hf (n : ℕ) : f n = if n ≠ 0 ∧ ∀ p ∈ P, ¬p ∣ n then 1 else 0 := rfl
  have hconv : ∑ n ∈ S, log n ≤ ∑ n ∈ Ioc 0 N, (f * Λ) n := by
    unfold S sifted
    rw [sum_filter]
    apply sum_le_sum
    intro n hn
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b ↦ f a * Λ b)]
    split_ifs with h
    · rw [← ArithmeticFunction.vonMangoldt_sum]
      apply sum_le_sum
      intro d hd
      have hdiv := Nat.dvd_of_mem_divisors hd
      have hquot := Nat.div_dvd_of_dvd hdiv
      have hpos := Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)
      rw [hf, ite_eq_left ⟨hpos.ne', fun p hp hpd ↦ h p hp (hpd.trans hquot)⟩, one_mul]
    · apply sum_nonneg
      intro d _
      rw [hf]
      split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg]
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum] at hconv
  have hlog : ∑ n ∈ S, log n ≤ (log 4 + 4) * x * ∑ n ∈ S, (n : ℝ)⁻¹ := by
    apply hconv.trans
    rw [mul_sum]
    unfold S sifted
    rw [sum_filter]
    apply sum_le_sum
    intro n hn
    have hn0 := (mem_Ioc.mp hn).1
    rw [hf, if_congr (and_iff_right hn0.ne') rfl rfl]
    split_ifs
    · rw [one_mul]
      have h := Chebyshev.psi_le_const_mul_self (x := x / n) (by positivity)
      rw [Chebyshev.psi, Nat.floor_div_natCast] at h
      simpa [N, div_eq_mul_inv, mul_assoc] using h
    · simp
  have hpoint (n : ℕ) (hn : n ∈ S) : 1 + log x ≤ log n + x * (n : ℝ)⁻¹ := by
    have hpos : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).1
    have h := Real.log_le_sub_one_of_pos (x := x / n) (by positivity)
    rw [Real.log_div (by linarith) hpos.ne', div_eq_mul_inv] at h
    linarith
  have h := sum_le_sum hpoint
  rw [sum_const, nsmul_eq_mul, sum_add_distrib, ← mul_sum] at h
  change (S.card : ℝ) * _ ≤ _ * _ * ∑ n ∈ S, _
  linarith only [h, hlog]

/-- In the factorization of the integers up to `N`, a prime `p ≤ N` occurs at least
`⌊N / p⌋ ≥ N / (2p)` times. -/
private theorem prime_log_moment {N : ℕ} (hN : 0 < N) {Q : Finset ℕ}
    (hQ : ∀ p ∈ Q, p.Prime ∧ p ≤ N) :
    ∑ p ∈ Q, log p / p ≤ 2 * log N := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  apply le_of_mul_le_mul_left (a := (N : ℝ)) _ hN'
  calc
    (N : ℝ) * ∑ p ∈ Q, log p / p ≤ 2 * ∑ p ∈ Q, Λ p * (N / p : ℕ) := by
      rw [mul_sum, mul_sum]
      apply sum_le_sum
      intro p hp
      obtain ⟨hpr, hpN⟩ := hQ p hp
      have h1 : 1 ≤ (N / p : ℕ) := Nat.div_pos hpN hpr.pos
      have hfloor := Nat.lt_floor_add_one ((N : ℝ) / p)
      rw [Nat.floor_div_eq_div] at hfloor
      have h1' : (1 : ℝ) ≤ (N / p : ℕ) := by exact_mod_cast h1
      rw [ArithmeticFunction.vonMangoldt_apply_prime hpr]
      have := mul_le_mul_of_nonneg_left (show (N : ℝ) / p ≤ 2 * (N / p : ℕ) by linarith)
        (log_nonneg (x := (p : ℝ)) (by exact_mod_cast hpr.one_le))
      simpa only [div_eq_mul_inv, mul_left_comm, mul_assoc, mul_comm] using this
    _ ≤ 2 * ∑ d ∈ Ioc 0 N, Λ d * (N / d : ℕ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun p hp ↦ mem_Ioc.mpr ⟨(hQ p hp).1.pos, (hQ p hp).2⟩
      · exact fun d _ _ ↦ mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    _ = 2 * ∑ n ∈ Ioc 0 N, log n := by
      rw [← ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum]
      simp
    _ ≤ 2 * ∑ _n ∈ Ioc 0 N, log N := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum fun n hn ↦ log_le_log (Nat.cast_pos.mpr (mem_Ioc.mp hn).1)
        (Nat.cast_le.mpr (mem_Ioc.mp hn).2)
    _ = N * (2 * log N) := by simp [mul_left_comm]

/-- The integral test bounds the total mass available in the shifted Euler product. -/
private theorem zeta_bound {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, (n : ℝ) ^ (-s) ≤ 1 + (s - 1)⁻¹ := by
  have hs' : -s < -1 := by linarith
  have ha : AntitoneOn (fun t : ℝ ↦ t ^ (-s)) (Set.Ici (1 : ℝ)) := by
    intro a ha b _ hab
    exact rpow_le_rpow_of_nonpos (by linarith [Set.mem_Ici.mp ha]) hab (by linarith)
  have h := AntitoneOn.tsum_comp_add_le_integral (f := fun t : ℝ ↦ t ^ (-s)) 1
    (by simpa using ha)
    (by simpa using integrableOn_Ioi_rpow_of_lt hs' zero_lt_one)
    (fun t ht ↦ rpow_nonneg ((Nat.cast_nonneg 1).trans (Set.mem_Ioi.mp ht).le) _)
  simp only [Nat.cast_one, integral_Ioi_rpow_of_lt hs' zero_lt_one, one_rpow] at h
  have hsum := (Real.summable_nat_rpow.mpr hs').sum_add_tsum_nat_add 2
  rw [← hsum, sum_range_succ, sum_range_succ]
  simp only [sum_range_zero, Nat.cast_zero, zero_rpow (by linarith : -s ≠ 0),
    Nat.cast_one, one_rpow, zero_add]
  rw [show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg, one_div] at h
  exact add_le_add_right h 1

open Classical in
/-- Removing the Euler factors indexed by `P` bounds the shifted mass of the sifted set. -/
private theorem shifted_sum_le (P : Set ℕ) (N : ℕ) {s : ℝ} (hs : 1 < s) :
    ∑ n ∈ sifted P N, (n : ℝ) ^ (-s) ≤
      (1 + (s - 1)⁻¹) * exp (-(∑ p ∈ N.primesLE with p ∈ P, (p : ℝ) ^ (-s))) := by
  classical
  let w : ℕ →* ℝ :=
    { toFun := fun n ↦ (n : ℝ) ^ (-s)
      map_one' := by simp
      map_mul' := fun a b ↦ by simp [mul_rpow] }
  have hw (n : ℕ) : 0 ≤ w n := rpow_nonneg (Nat.cast_nonneg _) _
  have hwSum : Summable w := Real.summable_nat_rpow.mpr (by linarith)
  have hwlt {p : ℕ} (hp : p.Prime) : w p < 1 :=
    (le_abs_self _).trans_lt (Real.norm_eq_abs _ ▸ hwSum.norm_lt_one hp.one_lt)
  let S := sifted P N
  let A := N.primesLE
  let B := A.filter (· ∉ P)
  let Q := A.filter (· ∈ P)
  let g (p : ℕ) := 1 - w p
  have hmem {n : ℕ} (hn : n ∈ S) : n ∈ Nat.factoredNumbers B := by
    obtain ⟨hnI, hnP⟩ := mem_filter.mp hn
    rw [Nat.mem_factoredNumbers_iff_forall_le]
    refine ⟨(mem_Ioc.mp hnI).1.ne', fun p hpn hp hdiv ↦ ?_⟩
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpn.trans (mem_Ioc.mp hnI).2, hp⟩,
      fun hpP ↦ hnP p hpP hdiv⟩
  have hprod (T : Finset ℕ) (hT : T ⊆ A) :
      ∏ p ∈ T, (g p)⁻¹ = ∑' m : Nat.factoredNumbers T, w m := by
    have heq := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hwSum T
    rwa [filter_true_of_mem (fun p hp ↦ (Nat.mem_primesLE.mp (hT hp)).2)] at heq
  have hB : ∑ n ∈ S, w n ≤ ∏ p ∈ B, (g p)⁻¹ := by
    rw [hprod B (filter_subset ..), _root_.tsum_subtype]
    have h := (hwSum.indicator (Nat.factoredNumbers B)).sum_le_tsum S
      (fun n _ ↦ Set.indicator_nonneg (fun n _ ↦ hw n) _)
    exact (sum_congr rfl fun n hn ↦ (Set.indicator_of_mem (hmem hn) _).symm).le.trans h
  have hA : ∏ p ∈ A, (g p)⁻¹ ≤ 1 + (s - 1)⁻¹ := by
    rw [hprod A (by rfl)]
    exact (hwSum.tsum_subtype_le w _ hw).trans (zeta_bound hs)
  have hg {p : ℕ} (hp : p ∈ Q) : 0 < g p :=
    sub_pos.mpr (hwlt (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2)
  have hsplit : (∏ p ∈ B, (g p)⁻¹) = (∏ p ∈ A, (g p)⁻¹) * ∏ p ∈ Q, g p := by
    rw [← prod_filter_mul_prod_filter_not A (· ∈ P), mul_comm (∏ p ∈ Q, (g p)⁻¹),
      mul_assoc, ← prod_mul_distrib]
    rw [prod_eq_one (fun p hp ↦ inv_mul_cancel₀ (hg hp).ne'), mul_one]
  have hexp : (∏ p ∈ Q, g p) ≤ exp (-(∑ p ∈ Q, w p)) := by
    rw [← sum_neg_distrib, exp_sum]
    apply prod_le_prod₀ (fun p hp ↦ (hg hp).le)
    intro p _
    dsimp only [g]
    linarith only [add_one_le_exp (-w p)]
  have hspos : 0 < s - 1 := sub_pos.mpr hs
  exact hB.trans (hsplit.le.trans (mul_le_mul hA hexp (prod_nonneg fun p hp ↦ (hg hp).le)
    (by positivity)))

open Classical in
/-- Moving the exponent from `1` to `1 + 1 / (1 + log x)` costs a bounded amount
in the sum over excluded primes, uniformly in the choice of those primes. -/
private theorem harmonic_bound (P : Set ℕ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ sifted P ⌊x⌋₊, (n : ℝ)⁻¹ ≤
      (2 * exp 3) * (1 + log x) *
        exp (-(∑ p ∈ (⌊x⌋₊).primesLE with p ∈ P, (1 : ℝ) / p)) := by
  classical
  let N := ⌊x⌋₊
  let Q := N.primesLE.filter (· ∈ P)
  let L := 1 + log x
  let t := L⁻¹
  have hL : 1 ≤ L := by dsimp [L]; linarith [log_nonneg hx]
  have hLpos : 0 < L := by linarith
  have ht : 0 < t := inv_pos.mpr hLpos
  have htL : t * L = 1 := inv_mul_cancel₀ hLpos.ne'
  have hQ (p : ℕ) (hp : p ∈ Q) : p.Prime ∧ p ≤ N :=
    (Nat.mem_primesLE.mp (mem_filter.mp hp).1).symm
  have hw {n : ℕ} (hn : 0 < n) :
      (n : ℝ) ^ (-(1 + t)) = (n : ℝ)⁻¹ * exp (-(t * log n)) := by
    have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [neg_add, rpow_add hn', rpow_neg_one, rpow_def_of_pos hn']
    congr 2
    ring
  have hshift : ∑ n ∈ sifted P N, (n : ℝ)⁻¹ ≤
      exp 1 * ∑ n ∈ sifted P N, (n : ℝ) ^ (-(1 + t)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    obtain ⟨hn0, hnN⟩ := mem_Ioc.mp (mem_filter.mp hn).1
    have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr hnN).trans (Nat.floor_le (by linarith))
    have hlog : log (n : ℝ) ≤ L := by
      dsimp [L]
      linarith [log_le_log (Nat.cast_pos.mpr hn0) hnx]
    have hsmall := (mul_le_mul_of_nonneg_left hlog ht.le).trans_eq htL
    rw [hw hn0, mul_left_comm, ← exp_add]
    exact le_mul_of_one_le_right (by positivity) (one_le_exp (by linarith))
  have hcost : (∑ p ∈ Q, (1 : ℝ) / p) - (∑ p ∈ Q, (p : ℝ) ^ (-(1 + t))) ≤ 2 := by
    calc
      _ = ∑ p ∈ Q, ((1 : ℝ) / p - (p : ℝ) ^ (-(1 + t))) := by rw [sum_sub_distrib]
      _ ≤ t * ∑ p ∈ Q, log p / p := by
        rw [mul_sum]
        apply sum_le_sum
        intro p hp
        rw [hw (hQ p hp).1.pos]
        have h := mul_le_mul_of_nonneg_left (add_one_le_exp (-(t * log p)))
          (inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p))
        simp only [div_eq_mul_inv, one_mul]
        linarith only [h]
      _ ≤ t * (2 * log N) :=
        mul_le_mul_of_nonneg_left (prime_log_moment (Nat.floor_pos.mpr hx) hQ) ht.le
      _ ≤ 2 := by
        have hn : 0 < N := Nat.floor_pos.mpr hx
        have hlog : log (N : ℝ) ≤ L := by
          dsimp [L, N]
          linarith [log_le_log (Nat.cast_pos.mpr hn) (Nat.floor_le (by linarith : 0 ≤ x))]
        linarith only [mul_le_mul_of_nonneg_left hlog ht.le, htL]
  have hexp : exp (-(∑ p ∈ Q, (p : ℝ) ^ (-(1 + t)))) ≤
      exp 2 * exp (-(∑ p ∈ Q, (1 : ℝ) / p)) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith only [hcost])
  have hz := shifted_sum_le P N (s := 1 + t) (by linarith)
  rw [add_sub_cancel_left, show t⁻¹ = L from inv_inv _] at hz
  change ∑ n ∈ sifted P N, (n : ℝ)⁻¹ ≤ _ * L * exp (-(∑ p ∈ Q, (1 : ℝ) / p))
  calc
    _ ≤ exp 1 * ((1 + L) * exp (-(∑ p ∈ Q, (p : ℝ) ^ (-(1 + t))))) :=
      hshift.trans (mul_le_mul_of_nonneg_left hz (exp_pos _).le)
    _ ≤ exp 1 * ((2 * L) * (exp 2 * exp (-(∑ p ∈ Q, (1 : ℝ) / p)))) := by
      gcongr
      linarith
    _ = _ := by rw [show (3 : ℝ) = 1 + 2 by norm_num, exp_add]; ring

end card_free_of_prime_set_le_exp_neg_sum_inv

open Classical in
/-- **Pollack–Pomerance sieve bound.** There is an absolute constant $C > 0$ such that for every
set $P$ of primes and every real $x > 1$, the number of integers $n$ with $1 \le n \le x$ that
are divisible by no prime in $P$ is at most $C x \exp(-A_P(x))$, where
$A_P(x) = \sum_{p \in P,\ p \le x} 1/p$.

Source: Anup B. Dixit and Saunak Bhattacharjee, *On the Distribution of φ(σ(n))*,
INTEGERS 24 (2024), Article A65, Lemma 1 (`integers-2024-A65-lem-1`), quoting Pollack and
Pomerance, Lemma 3. -/
public theorem card_free_of_prime_set_le_exp_neg_sum_inv :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Set ℕ), (∀ p ∈ P, p.Prime) → ∀ x : ℝ, 1 < x →
      ((((Finset.Icc 1 ⌊x⌋₊).filter fun n => ∀ p ∈ P, ¬ p ∣ n).card : ℕ) : ℝ) ≤
        C * x * Real.exp (-∑ p ∈ (Finset.Iic ⌊x⌋₊).filter (· ∈ P), (1 : ℝ) / p) := by
  classical
  use (Real.log 4 + 5) * (2 * Real.exp 3)
  refine ⟨by positivity, fun P hP x hx ↦ ?_⟩
  have hcount := card_free_of_prime_set_le_exp_neg_sum_inv.count_le_harmonic P hx.le
  have hsum := card_free_of_prime_set_le_exp_neg_sum_inv.harmonic_bound P hx.le
  have hQ : (⌊x⌋₊).primesLE.filter (· ∈ P) = (Iic ⌊x⌋₊).filter (· ∈ P) := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE, mem_Iic]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hP p h.2⟩, h.2⟩⟩
  rw [hQ] at hsum
  have h := hcount.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have hpos : 0 < 1 + log x := by linarith [log_pos hx]
  have hI : Icc 1 ⌊x⌋₊ = Ioc 0 ⌊x⌋₊ := by ext; simp; omega
  rw [hI]
  apply le_of_mul_le_mul_right (a := 1 + log x) _ hpos
  exact h.trans_eq (by ring)

end MetaMathlibExt
