/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

/-! # Multiplicativity of formal binomial powers -/

namespace PowerSeries

variable {K : Type*} [Field K] [CharZero K]

private noncomputable def substCoeffPolynomial (A : PowerSeries K) (n : ℕ) :
    Polynomial K :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((k.factorial : K)⁻¹ * coeff n (A ^ k)) * descPochhammer K k

private theorem eval_substCoeffPolynomial (A : PowerSeries K) (hA : constantCoeff A = 0)
    (n : ℕ) (x : K) :
    (substCoeffPolynomial A n).eval x = coeff n ((binomialSeries K x).subst A) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hA),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp only [substCoeffPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, binomialSeries_coeff, smul_eq_mul, mul_one]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hp : (descPochhammer K k).eval x = (descPochhammer ℤ k).smeval x := by
      rw [← descPochhammer_map (Int.castRingHom K), Polynomial.eval_map,
        ← Polynomial.eval₂_smulOneHom_eq_smeval ℤ,
        show Int.castRingHom K = RingHom.smulOneHom from Subsingleton.elim _ _]
    rw [hp, Ring.choose_eq_smul, smul_eq_mul]
    ring
  · intro k hk
    by_contra hkr
    have hnk : n < k := by simpa [Finset.mem_range] using hkr
    apply hk
    change coeff k (binomialSeries K x) • coeff n (A ^ k) = 0
    rw [coeff_of_lt_order n ((by exact_mod_cast hnk : (n : ℕ∞) < k).trans_le
        (le_order_pow_of_constantCoeff_eq_zero k hA)), smul_zero]

/-- **Multiplicativity of formal binomial powers.** Let $K$ be a field of characteristic zero,
let $A,B\in K[[X]]$ have zero constant term, and let $x\in K$. The formal binomial power of
$(1+A)(1+B)$ with exponent $x$ is the product of the formal binomial powers of $1+A$ and
$1+B$ with exponent $x$. Each power $(1+U)^x$ is defined by substituting $U$ into the
binomial series $\sum_{n\ge 0} \binom{x}{n}X^n$. -/
public theorem binomialSeries_subst_mul (A B : PowerSeries K)
    (hA : constantCoeff A = 0) (hB : constantCoeff B = 0) (x : K) :
    (binomialSeries K x).subst A * (binomialSeries K x).subst B =
      (binomialSeries K x).subst (A + B + A * B) := by
  have hAB : constantCoeff (A + B + A * B) = 0 := by simp [hA, hB]
  have natSubst (D : PowerSeries K) (hD : constantCoeff D = 0) (m : ℕ) :
      (binomialSeries K (m : K)).subst D = (1 + D) ^ m := by
    have h := HasSubst.of_constantCoeff_zero' hD
    rw [binomialSeries_nat, subst_pow h, ← coe_substAlgHom h, map_add, map_one,
      substAlgHom_X h]
  -- At each degree the two coefficients are polynomials in the exponent.
  ext n
  let P : Polynomial K := ∑ ij ∈ Finset.antidiagonal n,
    substCoeffPolynomial A ij.1 * substCoeffPolynomial B ij.2
  let Q := substCoeffPolynomial (A + B + A * B) n
  have evalP (z : K) : P.eval z =
      coeff n ((binomialSeries K z).subst A * (binomialSeries K z).subst B) := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, coeff_mul,
      eval_substCoeffPolynomial A hA, eval_substCoeffPolynomial B hB]
  have evalQ (z : K) : Q.eval z =
      coeff n ((binomialSeries K z).subst (A + B + A * B)) :=
    eval_substCoeffPolynomial _ hAB n z
  have hpq : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono ?_
    rintro _ ⟨m, rfl⟩
    change P.eval (m : K) = Q.eval (m : K)
    rw [evalP, evalQ, natSubst A hA, natSubst B hB, natSubst _ hAB, ← mul_pow]
    congr 2
    ring
  rw [← evalP, ← evalQ, hpq]

end PowerSeries
