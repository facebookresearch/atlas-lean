/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The smallest prime divisor of an odd perfect number

We prove Stone's linear upper bound in terms of the number of distinct prime divisors.
-/

namespace MetaMathlibExt

open Finset

namespace oddPerfect_minFac_lt

private lemma prime_mod_three_ne_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    p % 3 ≠ 0 := fun h ↦
  (ne_of_gt hp3) ((hp.dvd_iff_eq (by decide)).mp (Nat.dvd_of_mod_eq_zero h))

-- Each interval of three consecutive integers starting at a multiple of three
-- contains at most one prime greater than three.
private lemma prime_div_three_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp3 : 3 < p) (hpq : p < q) : p / 3 < q / 3 := by
  have hp₂ := hp.eq_two_or_odd.resolve_left (by omega)
  have hq₂ := hq.eq_two_or_odd.resolve_left (by omega)
  have hp₃ := prime_mod_three_ne_zero hp hp3
  have hq₃ := prime_mod_three_ne_zero hq (hp3.trans hpq)
  omega

private lemma prod_one_sub_inv_lt_half {N : ℕ} (hperf : N.Perfect)
    (hprimes : N.primeFactors.Nonempty) :
    ∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ)) < 1 / 2 := by
  have hN : 0 < N := hperf.2
  have hσ : (2 : ℚ) * N =
      ∏ p ∈ N.primeFactors, ∑ j ∈ range (N.factorization p + 1), (p : ℚ) ^ j := by
    have h := (Nat.perfect_iff_sum_divisors_eq_two_mul hN).mp hperf
    rw [← ArithmeticFunction.sigma_one_apply,
      ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hN.ne'] at h
    exact_mod_cast (by simpa only [mul_one] using h.symm)
  have hprod : ∏ p ∈ N.primeFactors, (p : ℚ) ^ N.factorization p = N := by
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hN.ne').symm
  have hfactor (p : ℕ) (hp : p ∈ N.primeFactors) : (1 : ℚ) < p := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hlt : (2 * (N : ℚ)) * (∏ p ∈ N.primeFactors, (1 - 1 / (p : ℚ))) < N := by
    rw [hσ, ← prod_mul_distrib, ← hprod]
    refine prod_lt_prod_of_nonempty₀ ?_ ?_ hprimes
    · intro p hp
      exact mul_pos
        (sum_pos (fun j _ ↦ pow_pos (zero_lt_one.trans (hfactor p hp)) j) nonempty_range_add_one)
        (sub_pos.mpr (by simpa only [one_div] using inv_lt_one_of_one_lt₀ (hfactor p hp)))
    · intro p hp
      have hp0 : (0 : ℚ) < p := zero_lt_one.trans (hfactor p hp)
      rw [show (1 - 1 / (p : ℚ)) = ((p : ℚ) - 1) / p by rw [sub_div, div_self hp0.ne'],
        ← mul_div_assoc, div_lt_iff₀ hp0, geom_sum_mul, pow_succ]
      exact sub_lt_self _ zero_lt_one
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  apply (lt_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mpr
  apply (mul_lt_mul_iff_right₀ hNq).mp
  simpa only [mul_left_comm, mul_comm, mul_assoc, one_mul, mul_one] using hlt

private lemma ratio_le_cube {a q : ℚ} (ha : 3 < a) (hq : 1 < q) (hle : a ≤ q + 1) :
    (a - 3) / a ≤ (1 - 1 / q) ^ 3 := by
  have ha0 : 0 < a := by linarith
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hq1 : 0 < q + 1 := by positivity
  calc
    (a - 3) / a = 1 - 3 / a := by rw [sub_div, div_self ha0.ne']
    _ ≤ 1 - 3 / (q + 1) := by
      gcongr
    _ ≤ (1 - 1 / q) ^ 3 := by
      field_simp
      nlinarith

private lemma prod_linear_ratios (a : ℚ) (ha : 3 < a) (m : ℕ) :
    (∏ i : Fin m, (a - 3 + 3 * (i : ℕ)) / (a + 3 * (i : ℕ))) =
      (a - 3) / (a - 3 + 3 * m) := by
  induction m with
  | zero =>
    simp [div_self (sub_pos.mpr ha).ne']
  | succ m ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_succ]
    have hm : (0 : ℚ) ≤ (m : ℚ) := by positivity
    have h1 : 0 < a - 3 + 3 * (m : ℚ) := by linarith
    have h2 : 0 < a + 3 * (m : ℚ) := by linarith
    rw [show a - 3 + 3 * ((m : ℚ) + 1) = a + 3 * m by ring]
    field_simp

end oddPerfect_minFac_lt

open oddPerfect_minFac_lt in
/-- **A linear bound on the smallest prime divisor of an odd perfect number.** If $N$ is an odd
perfect number with $m$ distinct prime divisors, then the smallest prime divisor $p_1$ of $N$
satisfies $p_1 < 3m/7 + 3$.

Source: Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24
(2024), Article A114, Lemma 6 (`integers-2024-A114-lem-6`). -/
public theorem oddPerfect_minFac_lt (N : ℕ) (hodd : Odd N) (hperf : N.Perfect) :
    (N.minFac : ℚ) < 3 * N.primeFactors.card / 7 + 3 := by
  let p := N.minFac
  have hN1 : N ≠ 1 := fun h ↦ by simp [h, Nat.Perfect] at hperf
  have hp : p.Prime := Nat.minFac_prime hN1
  have hpN : p ∣ N := Nat.minFac_dvd _
  have hp2 : p ≠ 2 := fun h ↦ hodd.not_two_dvd_nat (h ▸ hpN)
  have hpge : 3 ≤ p := by have := hp.two_le; omega
  have hprimes : N.primeFactors.Nonempty :=
    ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpN, hperf.2.ne'⟩⟩
  change (p : ℚ) < 3 * N.primeFactors.card / 7 + 3
  by_cases hp3 : p = 3
  · rw [hp3]
    have hm : (0 : ℚ) < N.primeFactors.card := by exact_mod_cast hprimes.card_pos
    exact lt_add_of_pos_left _ (div_pos (mul_pos (by norm_num) hm) (by norm_num))
  have hpgt : 3 < p := lt_of_le_of_ne hpge (Ne.symm hp3)
  let q := N.primeFactors.orderEmbOfFin rfl
  have hqmem (i : Fin N.primeFactors.card) : q i ∈ N.primeFactors :=
    N.primeFactors.orderEmbOfFin_mem rfl i
  have hqprime (i : Fin N.primeFactors.card) : (q i).Prime :=
    Nat.prime_of_mem_primeFactors (hqmem i)
  have hmin (i : Fin N.primeFactors.card) : p ≤ q i :=
    Nat.minFac_le_of_dvd (hqprime i).two_le (Nat.dvd_of_mem_primeFactors (hqmem i))
  -- The quotients by three increase strictly along the ordered prime factors.
  have hgap (j : ℕ) (hj : j < N.primeFactors.card) : p / 3 + j ≤ q ⟨j, hj⟩ / 3 := by
    induction j with
    | zero => simpa only [Nat.add_zero] using Nat.div_le_div_right (hmin ⟨0, hj⟩)
    | succ j ih =>
      let i : Fin N.primeFactors.card := ⟨j, by omega⟩
      have hlt : q i < q ⟨j + 1, hj⟩ := q.strictMono (by change j < j + 1; omega)
      have hstep := prime_div_three_lt (hqprime i) (hqprime ⟨j + 1, hj⟩)
        (hpgt.trans_le (hmin i)) hlt
      have hprev : p / 3 + j ≤ q i / 3 := ih i.isLt
      omega
  have hposition (i : Fin N.primeFactors.card) : p + 3 * (i : ℕ) ≤ q i + 1 := by
    have hmod := prime_mod_three_ne_zero (hqprime i) (hpgt.trans_le (hmin i))
    have hrank : p / 3 + (i : ℕ) ≤ q i / 3 := hgap i.val i.isLt
    omega
  have hpq : (3 : ℚ) < p := by exact_mod_cast hpgt
  have hf (i : Fin N.primeFactors.card) : (1 : ℚ) < q i := by
    exact_mod_cast (hqprime i).one_lt
  -- Compare the cubes of the prime factors' reciprocal terms with a telescoping product.
  have hterm (i : Fin N.primeFactors.card) :
      ((p : ℚ) - 3 + 3 * (i : ℕ)) / ((p : ℚ) + 3 * (i : ℕ)) ≤
        (1 - 1 / (q i : ℚ)) ^ 3 := by
    rw [show (p : ℚ) - 3 + 3 * (i : ℕ) = (p : ℚ) + 3 * (i : ℕ) - 3 by ring]
    apply ratio_le_cube (hpq.trans_le (le_add_of_nonneg_right (by positivity))) (hf i)
    exact_mod_cast hposition i
  have htel := prod_le_prod₀ (s := univ) (f := fun i : Fin N.primeFactors.card ↦
    ((p : ℚ) - 3 + 3 * (i : ℕ)) / ((p : ℚ) + 3 * (i : ℕ)))
    (fun i _ ↦ div_nonneg (add_nonneg (sub_nonneg.mpr hpq.le) (by positivity)) (by positivity))
    (fun i _ ↦ hterm i)
  have hmap : (∏ i, (1 - 1 / (q i : ℚ))) = ∏ r ∈ N.primeFactors, (1 - 1 / (r : ℚ)) := by
    calc
      (∏ i, (1 - 1 / (q i : ℚ))) =
          ∏ r ∈ univ.map q.toEmbedding, (1 - 1 / (r : ℚ)) :=
        (prod_map univ q.toEmbedding (fun r : ℕ ↦ (1 - 1 / (r : ℚ)))).symm
      _ = _ := congrArg (fun s : Finset ℕ ↦ ∏ r ∈ s, (1 - 1 / (r : ℚ)))
        (N.primeFactors.map_orderEmbOfFin_univ rfl)
  have hhalf := prod_one_sub_inv_lt_half hperf hprimes
  have hnonneg : 0 ≤ ∏ i, (1 - 1 / (q i : ℚ)) :=
    prod_nonneg fun i _ ↦ sub_nonneg.mpr
      (by simpa only [one_div] using inv_le_one_of_one_le₀ (hf i).le)
  have hbound : ((p : ℚ) - 3) / ((p : ℚ) - 3 + 3 * N.primeFactors.card) < 1 / 8 := by
    rw [prod_linear_ratios _ hpq, prod_pow] at htel
    have hcubed := pow_lt_pow_left₀ (hmap ▸ hhalf) hnonneg (by decide : 3 ≠ 0)
    exact htel.trans_lt (by norm_num at hcubed ⊢; exact hcubed)
  have hdenom : (0 : ℚ) < (p : ℚ) - 3 + 3 * N.primeFactors.card :=
    add_pos_of_pos_of_nonneg (sub_pos.mpr hpq) (by positivity)
  have hle := (div_lt_iff₀ hdenom).mp hbound
  linarith

end MetaMathlibExt
