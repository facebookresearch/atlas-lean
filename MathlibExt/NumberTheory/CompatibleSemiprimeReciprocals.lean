/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.CollatzArithmeticDerivative
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Group
import MathlibExt.NumberTheory.CollatzArithmeticDerivativeBounds

/-! # Summability of reciprocals of compatible semiprimes

For a fixed smaller prime factor `q`, a divisor of `15 * q^2 + 1` determines the semiprime.
A divisor-count bound of order `m^(1/3)` and the estimate `1/(p*q) ≤ 1/q^2` then give a
convergent `4/3`-power series bound after summing over `q`.
-/

open scoped BigOperators

namespace MetaMathlibExt

private abbrev Compatible := {n : ℕ //
  ∃ p q r s, IsCompatibleSemiprimePair p q r s ∧ n = p * q}

private abbrev FactorData := Σ q : ℕ, {d : ℕ // d ∈ (15 * q ^ 2 + 1).divisors}

private def numberFromFactor (x : FactorData) : ℕ :=
  let q := x.1
  let d := x.2.1
  let e := (15 * q ^ 2 + 1) / (2 * d)
  (11 * q + 2 * d + 2 * e) * q

-- After ordering the two primes of the input, one factor of 15q² + 1 determines the input.
private theorem exists_factorData (n : Compatible) :
    ∃ x : FactorData, numberFromFactor x = n.1 ∧ 2 ≤ x.1 ∧ x.1 ^ 2 ≤ n.1 := by
  obtain ⟨p, q, r, s, h, hn⟩ := n.2
  have hne : p ≠ q := by
    intro he
    rcases h.mod_three.2.2.1 with hh | hh <;> omega
  have ordered : ∃ p q, IsCompatibleSemiprimePair p q r s ∧ q < p ∧ n.1 = p * q := by
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · obtain ⟨hp, hq, hr, hs, hsum, hprod⟩ := h
      exact ⟨q, p, ⟨hq, hp, hr, hs, by simpa only [Nat.add_comm p q] using hsum,
        by simpa only [Nat.mul_comm p q] using hprod⟩,
        hpq, by simpa only [Nat.mul_comm p q] using hn⟩
    · exact ⟨p, q, h, hqp, hn⟩
  clear hne h hn p q
  obtain ⟨p, q, h, hqp, hn⟩ := ordered
  obtain ⟨_, _, hr, hs, _, _⟩ := h.bounds hqp
  let d := r - 3 * q
  let e := s - 3 * q
  have hd : 0 < d := by dsimp [d]; omega
  have hrd : r = 3 * q + d := by dsimp [d]; omega
  have hse : s = 3 * q + e := by dsimp [e]; omega
  obtain ⟨_, hq, _, _, hsum, hprod⟩ := h
  have hp : p = 11 * q + 2 * d + 2 * e := by omega
  have hprod' : 2 * ((r : ℤ) * s) = 3 * ((p : ℤ) * q) + 1 := by exact_mod_cast hprod
  have hrd' : (r : ℤ) = 3 * q + d := by exact_mod_cast hrd
  have hse' : (s : ℤ) = 3 * q + e := by exact_mod_cast hse
  have hp' : (p : ℤ) = 11 * q + 2 * d + 2 * e := by exact_mod_cast hp
  have hfac : 2 * (d * e) = 15 * q ^ 2 + 1 := by
    have hfac' : (2 : ℤ) * ((d : ℤ) * e) = 15 * (q : ℤ) ^ 2 + 1 := by
      rw [hrd', hse', hp'] at hprod'
      linear_combination hprod'
    exact_mod_cast hfac'
  have hmem : d ∈ (15 * q ^ 2 + 1).divisors := Nat.mem_divisors.mpr
    ⟨⟨2 * e, by rw [← hfac]; ac_rfl⟩, by omega⟩
  refine ⟨⟨q, ⟨d, hmem⟩⟩, ?_, hq.two_le, ?_⟩
  · have heq : (15 * q ^ 2 + 1) / (2 * d) = e := by
      rw [← hfac, ← Nat.mul_assoc]
      exact Nat.mul_div_cancel_left e (by omega)
    simp only [numberFromFactor, heq, ← hp, hn]
  · rw [hn, pow_two]
    exact Nat.mul_le_mul_right q hqp.le

private noncomputable def factorData (n : Compatible) : FactorData :=
  (exists_factorData n).choose

private theorem factorData_spec (n : Compatible) :
    numberFromFactor (factorData n) = n.1 ∧ 2 ≤ (factorData n).1 ∧ (factorData n).1 ^ 2 ≤ n.1 :=
  (exists_factorData n).choose_spec

private theorem factorData_injective : Function.Injective factorData := by
  intro n m h
  apply Subtype.ext
  rw [← (factorData_spec n).1, h, (factorData_spec m).1]

private theorem card_divisors_le_const_rpow (m : ℕ) (hm : m ≠ 0) :
    (m.divisors.card : ℝ) ≤ (4 : ℝ)^8 * (m : ℝ)^(1/3 : ℝ) := by
  have hsmall (a : ℕ) : (a + 1)^3 ≤ 64 * 2^a := by
    induction a with
    | zero => decide
    | succ a ih =>
      by_cases ha : 3 ≤ a
      · have hstep : (a + 2)^3 ≤ 2 * (a + 1)^3 := by
          obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
          nlinarith only [Nat.zero_le b, Nat.zero_le (b^2), Nat.zero_le (b^3)]
        calc
          (a + 2)^3 ≤ 2 * (a + 1)^3 := hstep
          _ ≤ 2 * (64 * 2^a) := Nat.mul_le_mul_left _ ih
          _ = 64 * 2^(a + 1) := by rw [pow_succ]; ac_rfl
      · interval_cases a <;> decide
  have hsucc (a : ℕ) : a + 1 ≤ 2^a := by
    induction a with
    | zero => decide
    | succ a ih => rw [pow_succ]; omega
  have hlarge (a : ℕ) : (a + 1)^3 ≤ 8^a := by
    calc
      _ ≤ (2^a)^3 := Nat.pow_le_pow_left (hsucc a) _
      _ = 8^a := by rw [← pow_mul, Nat.mul_comm a 3, pow_mul]; rfl
  let small := m.primeFactors.filter (· < 8)
  have hcard : small.card ≤ 8 := by
    simpa using (Finset.card_le_card (show small ⊆ Finset.range 8 from
      fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2))
  have hcube : m.divisors.card ^ 3 ≤ (64 : ℕ)^8 * m := by
    calc
      _ = ∏ p ∈ m.primeFactors, (m.factorization p + 1)^3 := by
        rw [Nat.card_divisors hm, Finset.prod_pow]
      _ ≤ ∏ p ∈ m.primeFactors, (if p < 8 then 64 else 1) * p ^ m.factorization p := by
        refine Finset.prod_le_prod (fun p hp => ?_)
        have hp₂ : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
        split_ifs with h
        · exact (hsmall _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp₂ _))
        · rw [one_mul]
          exact (hlarge _).trans (Nat.pow_le_pow_left (by omega) _)
      _ = (64 : ℕ)^small.card * m := by
        rw [Finset.prod_mul_distrib, ← Nat.prod_primeFactors_pow_factorization hm,
          ← Finset.prod_filter (fun p : ℕ => p < 8) (fun _ => (64 : ℕ)), Finset.prod_const]
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hcard)
  change m.divisors.card ^ 3 ≤ ((4 : ℕ)^8)^3 * m at hcube
  have hreal : (m.divisors.card : ℝ)^3 ≤ ((4 : ℝ)^8)^3 * (m : ℝ) := by
    exact_mod_cast hcube
  have h := Real.rpow_le_rpow (by positivity) hreal (by positivity : 0 ≤ ((3 : ℕ) : ℝ)⁻¹)
  rw [Real.mul_rpow (by positivity) (by positivity),
    Real.pow_rpow_inv_natCast (by positivity) (by decide : (3 : ℕ) ≠ 0),
    Real.pow_rpow_inv_natCast (by positivity) (by decide : (3 : ℕ) ≠ 0)] at h
  simpa only [Nat.cast_ofNat, one_div] using h

private lemma summable_divisor_majorant (C : ℝ) (hC : 0 ≤ C) :
    Summable (fun q : ℕ => C * (15 * (q : ℝ) ^ 2 + 1) ^ ((1 : ℝ) / 3) /
      (q : ℝ) ^ 2) := by
  have hs : Summable (fun q : ℕ => (q : ℝ) ^ (-(4 : ℝ) / 3)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  refine (hs.mul_left (C * (16 : ℝ) ^ ((1 : ℝ) / 3))).of_nonneg_of_le
    (fun _ => by positivity) ?_
  intro q
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · simp
  have hx : (0 : ℝ) < q := by exact_mod_cast hq
  have hx1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hsquare : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hr : (15 * (q : ℝ) ^ 2 + 1) ^ ((1 : ℝ) / 3) ≤
      (16 * (q : ℝ) ^ 2) ^ ((1 : ℝ) / 3) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  calc
    _ ≤ C * (16 * (q : ℝ) ^ 2) ^ ((1 : ℝ) / 3) / (q : ℝ) ^ 2 := by gcongr
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (sq_nonneg (q : ℝ))]
      rw [← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul hx.le]
      rw [div_eq_mul_inv, ← Real.rpow_neg hx.le]
      simp only [mul_assoc]
      rw [← Real.rpow_add hx]
      congr 2
      norm_num

private lemma summable_divisor_sigma (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ q : ℕ, 2 ≤ q → ((15 * q ^ 2 + 1 : ℕ).divisors.card : ℝ) ≤
      C * (15 * (q : ℝ) ^ 2 + 1) ^ ((1 : ℝ) / 3)) :
    Summable (fun z : Σ q : ℕ, ↥((15 * q ^ 2 + 1 : ℕ).divisors) =>
      (1 : ℝ) / (z.1 : ℝ) ^ 2) := by
  refine (summable_sigma_of_nonneg (fun _ => by positivity)).2
    ⟨fun _ => Summable.of_finite, ?_⟩
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    nsmul_eq_mul, mul_one_div]
  apply (summable_nat_add_iff 2).1
  exact ((summable_nat_add_iff 2).2 (summable_divisor_majorant C hC)).of_nonneg_of_le
    (fun _ => by positivity)
    (fun q => div_le_div_of_nonneg_right (hc (q + 2) (by omega)) (sq_nonneg _))

/-- **Reciprocals of compatible semiprimes have a finite sum.** Call a natural number $n$ a
compatible semiprime if $n = pq$ for primes $p, q$ for which there are primes $r, s$ with
$2(r + s) = p + q$ and $2rs = 3pq + 1$. The sum of $1/n$ over all compatible semiprimes $n$
converges.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8,
Theorem 14 (`jis-2025-25.1.8-thm-14`). -/
public theorem summable_inv_compatibleSemiprimes :
    Summable (Set.indicator {n : ℕ | ∃ p q r s, IsCompatibleSemiprimePair p q r s ∧ n = p * q}
      fun n => (1 : ℝ) / n) := by
  apply summable_subtype_iff_indicator.mp
  have hσ : Summable (fun z : FactorData => (1 : ℝ) / (z.1 : ℝ) ^ 2) := by
    apply summable_divisor_sigma ((4 : ℝ) ^ 8) (by positivity)
    intro q _
    have h := card_divisors_le_const_rpow (15 * q ^ 2 + 1) (by omega)
    push_cast at h
    exact h
  change Summable (fun n : Compatible => (1 : ℝ) / (n.1 : ℝ))
  refine (hσ.comp_injective factorData_injective).of_nonneg_of_le
    (fun n => div_nonneg (by norm_num) (Nat.cast_nonneg n.1)) ?_
  intro n
  have hq : (0 : ℝ) < (factorData n).1 := by
    exact_mod_cast (show 0 < (factorData n).1 by have := (factorData_spec n).2.1; omega)
  have hqn : ((factorData n).1 : ℝ) ^ 2 ≤ (n.1 : ℝ) := by
    exact_mod_cast (factorData_spec n).2.2
  exact one_div_le_one_div_of_le (sq_pos_of_pos hq) hqn

end MetaMathlibExt
