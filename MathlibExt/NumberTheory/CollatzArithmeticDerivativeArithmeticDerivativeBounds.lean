/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.IsPrimePow
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.ArithmeticDerivative
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Bounds for the arithmetic derivative

`arithmeticDerivative_bounds` bounds the arithmetic derivative using the number of prime
factors with multiplicity and the least prime factor. Equality in either bound characterizes
prime powers.

Source: Zachary P. Bradshaw, "On a Family of Solutions to Arithmetic Differential
Equations Involving the Collatz Map", *Journal of Integer Sequences* 28 (2025), Article 25.1.8
(<https://cs.uwaterloo.ca/journals/JIS/VOL28/Bradshaw/bradshaw3.html>).
-/

namespace MetaMathlibExt

private theorem sum_factorization_real (n : ℕ) :
    ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) = n.primeFactorsList.length := by
  have h : ∑ q ∈ n.primeFactors, n.factorization q = n.primeFactorsList.length :=
    Multiset.toFinsupp_sum_eq (n.primeFactorsList : Multiset ℕ)
  exact_mod_cast h

private theorem derivative_sum_real (n : ℕ) :
    (arithmeticDerivative n : ℝ) =
      ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * ((n : ℝ) / q) := by
  unfold arithmeticDerivative
  push_cast
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hq) (by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hq).ne_zero)]

private theorem log_factorization (n : ℕ) :
    Real.log n = ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * Real.log q := by
  exact Real.log_nat_eq_sum_factorization n

private theorem primePow_iff_factors (n : ℕ) (hn : 2 ≤ n) :
    IsPrimePow n ↔ ∀ q ∈ n.primeFactors, q = n.minFac := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  rw [isPrimePow_iff_unique_prime_dvd]
  constructor
  · rintro ⟨p, _, h⟩ q hq
    exact (h q ⟨Nat.prime_of_mem_primeFactors hq, Nat.dvd_of_mem_primeFactors hq⟩).trans
      (h n.minFac ⟨hp, Nat.minFac_dvd n⟩).symm
  · intro h
    refine ⟨n.minFac, ⟨hp, Nat.minFac_dvd n⟩, ?_⟩
    intro q hq
    exact h q (Nat.mem_primeFactors.mpr ⟨hq.1, hq.2, by omega⟩)

private theorem multiplicity_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < (n.primeFactorsList.length : ℝ) := by
  exact_mod_cast List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil n).mpr hn)

private theorem weighted_product (n : ℕ) (hn : 2 ≤ n) :
    ∏ q ∈ n.primeFactors,
        ((n : ℝ) / q) ^ ((n.factorization q : ℝ) / n.primeFactorsList.length) =
      (n : ℝ) ^ (((n.primeFactorsList.length : ℝ) - 1) / n.primeFactorsList.length) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hom := multiplicity_pos n hn
  have hw : ∑ q ∈ n.primeFactors,
      (n.factorization q : ℝ) / n.primeFactorsList.length = 1 := by
    rw [← Finset.sum_div, sum_factorization_real n, div_self hom.ne']
  have hp : ∏ q ∈ n.primeFactors, (q : ℝ) ^ (n.factorization q : ℝ) = n := by
    simp_rw [Real.rpow_natCast]
    exact_mod_cast (Nat.prod_factorization_pow_eq_self hn0)
  have hd : ∏ q ∈ n.primeFactors,
      (q : ℝ) ^ ((n.factorization q : ℝ) / n.primeFactorsList.length) =
        (n : ℝ) ^ (n.primeFactorsList.length : ℝ)⁻¹ := by
    simp_rw [div_eq_mul_inv]
    simp_rw [Real.rpow_mul (Nat.cast_nonneg _)]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) _, hp]
  simp_rw [Real.div_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg _)]
  rw [Finset.prod_div_distrib, ← Real.rpow_sum_of_nonneg hnpos.le
    (fun _ _ => div_nonneg (Nat.cast_nonneg _) hom.le), hw, Real.rpow_one, hd]
  conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
  rw [← Real.rpow_sub hnpos]
  congr 1
  field_simp

private theorem lower_bound (n : ℕ) (hn : 2 ≤ n) :
    let om : ℝ := n.primeFactorsList.length
    let lower : ℝ := om * (n : ℝ) ^ ((om - 1) / om)
    lower ≤ arithmeticDerivative n ∧
      (lower = arithmeticDerivative n ↔ IsPrimePow n) := by
  dsimp only
  let om : ℝ := n.primeFactorsList.length
  let w := fun q => (n.factorization q : ℝ) / om
  let z := fun q : ℕ => (n : ℝ) / q
  have hom : 0 < om := multiplicity_pos n hn
  have hc : ∀ q ∈ n.primeFactors, 0 < (n.factorization q : ℝ) := by
    intro q hq
    exact_mod_cast (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd
      (by omega : n ≠ 0) (Nat.dvd_of_mem_primeFactors hq)
  have hw : ∀ q ∈ n.primeFactors, 0 < w q := fun q hq => div_pos (hc q hq) hom
  have hsum : ∑ q ∈ n.primeFactors, w q = 1 := by
    change (∑ q ∈ n.primeFactors, (n.factorization q : ℝ) / om) = 1
    rw [← Finset.sum_div, sum_factorization_real n]
    exact div_self hom.ne'
  have hz : ∀ q ∈ n.primeFactors, 0 ≤ z q :=
    fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hprod : ∏ q ∈ n.primeFactors, z q ^ w q = (n : ℝ) ^ ((om - 1) / om) :=
    weighted_product n hn
  have hmean : ∑ q ∈ n.primeFactors, w q * z q = (arithmeticDerivative n : ℝ) / om := by
    rw [derivative_sum_real]
    simp_rw [w, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  have hle := Real.geom_mean_le_arith_mean_weighted n.primeFactors w z
    (fun q hq => (hw q hq).le) hsum hz
  rw [hprod, hmean, le_div_iff₀ hom] at hle
  refine ⟨by simpa [mul_comm, om] using hle, ?_⟩
  have heq := Real.geom_mean_eq_arith_mean_weighted_iff_of_pos n.primeFactors w z
    hw hsum hz
  rw [hprod, hmean, eq_div_iff hom.ne'] at heq
  rw [mul_comm] at heq
  change om * (n : ℝ) ^ ((om - 1) / om) = _ ↔ _
  rw [heq, primePow_iff_factors n hn]
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hm : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, Nat.minFac_dvd n, by omega⟩
  constructor
  · intro h q hq
    have hzq := h q hq n.minFac hm
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hqpos : 0 < (q : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
    have hppos : 0 < (n.minFac : ℝ) := by exact_mod_cast hp.pos
    dsimp [z] at hzq
    have he := (div_eq_div_iff hqpos.ne' hppos.ne').mp hzq
    have heq : (q : ℝ) = n.minFac := by nlinarith
    exact_mod_cast heq
  · intro h q hq r hr
    dsimp [z]
    rw [h q hq, h r hr]

private theorem upper_bound (n : ℕ) (hn : 2 ≤ n) :
    let p : ℝ := n.minFac
    let upper : ℝ := n * Real.logb p n / p
    (arithmeticDerivative n : ℝ) ≤ upper ∧
      ((arithmeticDerivative n : ℝ) = upper ↔ IsPrimePow n) := by
  dsimp only
  let om : ℝ := n.primeFactorsList.length
  let p : ℝ := n.minFac
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hp1 : 1 < p := by
    change 1 < (n.minFac : ℝ)
    exact_mod_cast hp.one_lt
  have hppos : 0 < p := lt_trans zero_lt_one hp1
  have hpq : ∀ q ∈ n.primeFactors, p ≤ (q : ℝ) := by
    intro q hq
    change (n.minFac : ℝ) ≤ q
    exact_mod_cast Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hq).two_le
      (Nat.dvd_of_mem_primeFactors hq)
  have hterm : ∀ q ∈ n.primeFactors,
      (n.factorization q : ℝ) * ((n : ℝ) / q) ≤
        (n.factorization q : ℝ) * ((n : ℝ) / p) := by
    intro q hq
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left hnpos.le hppos (hpq q hq)) (Nat.cast_nonneg _)
  have hsum : ∑ q ∈ n.primeFactors,
      (n.factorization q : ℝ) * ((n : ℝ) / p) = om * n / p := by
    rw [← Finset.sum_mul, sum_factorization_real n]
    change om * ((n : ℝ) / p) = om * n / p
    ring
  have hmid : (arithmeticDerivative n : ℝ) ≤ om * n / p := by
    rw [derivative_sum_real, ← hsum]
    exact Finset.sum_le_sum hterm
  have hlog : om * Real.log p ≤ Real.log n := by
    rw [log_factorization n]
    calc
      om * Real.log p = ∑ q ∈ n.primeFactors,
          (n.factorization q : ℝ) * Real.log p := by
        rw [← Finset.sum_mul, sum_factorization_real n]
      _ ≤ ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * Real.log q := by
        exact Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left
          (Real.log_le_log hppos (hpq q hq)) (Nat.cast_nonneg _)
  have hlogb : om ≤ Real.logb p n := by
    rw [Real.logb, le_div_iff₀ (Real.log_pos hp1)]
    exact hlog
  have hupper : om * n / p ≤ (n : ℝ) * Real.logb p n / p := by
    apply div_le_div_of_nonneg_right _ hppos.le
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hlogb hnpos.le
  refine ⟨hmid.trans hupper, ?_⟩
  change (arithmeticDerivative n : ℝ) = (n : ℝ) * Real.logb p n / p ↔ IsPrimePow n
  rw [primePow_iff_factors n hn]
  constructor
  · intro he q hq
    have heq : (arithmeticDerivative n : ℝ) = om * n / p :=
      le_antisymm hmid (by rw [he]; exact hupper)
    have hall : ∀ q ∈ n.primeFactors,
        (n.factorization q : ℝ) * ((n : ℝ) / q) =
          (n.factorization q : ℝ) * ((n : ℝ) / p) := by
      apply (Finset.sum_eq_sum_iff_of_le hterm).mp
      rw [← derivative_sum_real, hsum, heq]
    have hc : 0 < (n.factorization q : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hq).factorization_pos_of_dvd
        (by omega : n ≠ 0) (Nat.dvd_of_mem_primeFactors hq)
    have hz := mul_left_cancel₀ hc.ne' (hall q hq)
    have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le hppos (hpq q hq)
    have he' := (div_eq_div_iff hqpos.ne' hppos.ne').mp hz
    have he'' : (q : ℝ) = p := by nlinarith
    change (q : ℝ) = (n.minFac : ℝ) at he''
    exact_mod_cast he''
  · intro hall
    have hd : (arithmeticDerivative n : ℝ) = om * n / p := by
      rw [derivative_sum_real, ← hsum]
      exact Finset.sum_congr rfl fun q hq => by rw [hall q hq]
    have hl : Real.log n = om * Real.log p := by
      rw [log_factorization n]
      calc
        ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * Real.log q =
            ∑ q ∈ n.primeFactors, (n.factorization q : ℝ) * Real.log p := by
          exact Finset.sum_congr rfl fun q hq => by rw [hall q hq]
        _ = om * Real.log p := by rw [← Finset.sum_mul, sum_factorization_real n]
    have hb : Real.logb p n = om := by
      rw [Real.logb, hl, mul_div_cancel_right₀ _ (Real.log_pos hp1).ne']
    rw [hd, hb, mul_comm om]

@[expose] public section

/-- **Bounds for the arithmetic derivative.** Let $n \ge 2$ be a natural number, let $p$ be the
least prime factor of $n$, and let $\Omega(n)$ be the number of prime factors of $n$ counted with
multiplicity. Then the arithmetic derivative $D(n)$ satisfies
$$\Omega(n) \, n^{(\Omega(n) - 1)/\Omega(n)} \le D(n) \le \frac{n \log_p n}{p},$$
and each of the two inequalities is an equality if and only if $n$ is a prime power.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Lemma 1
(`jis-2025-25.1.8-lem-1`). -/
public theorem arithmeticDerivative_bounds (n : ℕ) (hn : 2 ≤ n) :
    let om : ℝ := n.primeFactorsList.length
    let p : ℝ := n.minFac
    let lower : ℝ := om * (n : ℝ) ^ ((om - 1) / om)
    let upper : ℝ := n * Real.logb p n / p
    lower ≤ arithmeticDerivative n ∧ (arithmeticDerivative n : ℝ) ≤ upper ∧
      (lower = arithmeticDerivative n ↔ IsPrimePow n) ∧
      ((arithmeticDerivative n : ℝ) = upper ↔ IsPrimePow n)
    := by
  obtain ⟨hl, hel⟩ := lower_bound n hn
  obtain ⟨hu, heu⟩ := upper_bound n hn
  exact ⟨hl, hu, hel, heu⟩

end

end MetaMathlibExt
