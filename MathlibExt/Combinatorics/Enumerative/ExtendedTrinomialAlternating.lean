/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring

/-!
# Alternating convolution of extended trinomial coefficients
-/

open PowerSeries

namespace MetaMathlibExt

private noncomputable def substCoeffPolynomial (A : PowerSeries ℂ) (n : ℕ) :
    Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((k.factorial : ℂ)⁻¹ * coeff n (A ^ k)) * descPochhammer ℂ k

private theorem eval_substCoeffPolynomial (A : PowerSeries ℂ) (hA : constantCoeff A = 0)
    (n : ℕ) (x : ℂ) :
    (substCoeffPolynomial A n).eval x = coeff n ((binomialSeries ℂ x).subst A) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hA),
    finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1))]
  · simp only [substCoeffPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, binomialSeries_coeff, smul_eq_mul, mul_one]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hp : (descPochhammer ℂ k).eval x = (descPochhammer ℤ k).smeval x := by
      rw [← descPochhammer_map (Int.castRingHom ℂ), Polynomial.eval_map,
        ← Polynomial.eval₂_smulOneHom_eq_smeval ℤ,
        show Int.castRingHom ℂ = RingHom.smulOneHom from Subsingleton.elim _ _]
    rw [hp, Ring.choose_eq_smul, smul_eq_mul]
    ring
  · intro k hk
    by_contra hkr
    have hnk : n < k := by simpa [Finset.mem_range] using hkr
    apply hk
    change coeff k (binomialSeries ℂ x) • coeff n (A ^ k) = 0
    rw [coeff_of_lt_order n ((by exact_mod_cast hnk : (n : ℕ∞) < k).trans_le
        (le_order_pow_of_constantCoeff_eq_zero k hA)), smul_zero]

private theorem binomialSeries_subst_mul (A B : PowerSeries ℂ)
    (hA : constantCoeff A = 0) (hB : constantCoeff B = 0) (x : ℂ) :
    (binomialSeries ℂ x).subst A * (binomialSeries ℂ x).subst B =
      (binomialSeries ℂ x).subst (A + B + A * B) := by
  have hAB : constantCoeff (A + B + A * B) = 0 := by simp [hA, hB]
  have natSubst (D : PowerSeries ℂ) (hD : constantCoeff D = 0) (m : ℕ) :
      (binomialSeries ℂ (m : ℂ)).subst D = (1 + D) ^ m := by
    have h := HasSubst.of_constantCoeff_zero' hD
    rw [binomialSeries_nat, subst_pow h, ← coe_substAlgHom h, map_add, map_one,
      substAlgHom_X h]
  -- At each degree the two coefficients are polynomials in the exponent.
  ext n
  let P : Polynomial ℂ := ∑ ij ∈ Finset.antidiagonal n,
    substCoeffPolynomial A ij.1 * substCoeffPolynomial B ij.2
  let Q := substCoeffPolynomial (A + B + A * B) n
  have evalP (z : ℂ) : P.eval z =
      coeff n ((binomialSeries ℂ z).subst A * (binomialSeries ℂ z).subst B) := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, coeff_mul,
      eval_substCoeffPolynomial A hA, eval_substCoeffPolynomial B hB]
  have evalQ (z : ℂ) : Q.eval z =
      coeff n ((binomialSeries ℂ z).subst (A + B + A * B)) :=
    eval_substCoeffPolynomial _ hAB n z
  have hpq : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono ?_
    rintro _ ⟨m, rfl⟩
    change P.eval (m : ℂ) = Q.eval (m : ℂ)
    rw [evalP, evalQ, natSubst A hA, natSubst B hB, natSubst _ hAB, ← mul_pow]
    congr 2
    ring
  rw [← evalP, ← evalQ, hpq]

private theorem coeff_mul_eq_sum_range_right (f g : PowerSeries ℂ) (n : ℕ) :
    coeff n (f * g) = ∑ k ∈ Finset.range (n + 1), coeff (n - k) f * coeff k g := by
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

private theorem coeff_mul_subst_X_sq (f g : PowerSeries ℂ) (n : ℕ) :
    coeff n (f * g.subst (X ^ 2 : PowerSeries ℂ)) =
      ∑ k ∈ Finset.range (n / 2 + 1), coeff (n - 2 * k) f * coeff k g := by
  simp only [coeff_mul_eq_sum_range_right, coeff_subst_X_pow (by decide : (2 : ℕ) ≠ 0),
    Algebra.algebraMap_self, RingHom.id_apply, mul_ite, mul_zero, ← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun k ↦ 2 * k) (fun j ↦ j / 2) ?_ ?_ ?_ ?_ ?_
  · simp only [Finset.mem_range, Finset.mem_filter]
    intro k hk
    exact ⟨by omega, dvd_mul_right 2 k⟩
  · simp only [Finset.mem_range, Finset.mem_filter]
    omega
  · intro k _
    omega
  · intro j hj
    simp only [Finset.mem_range, Finset.mem_filter] at hj
    omega
  · intro k _
    rw [show 2 * k / 2 = k by omega]

/-- **An alternating convolution of extended trinomial coefficients.** For complex $u$ and
$j \in \mathbb{N}$ write $\binom{u}{j}_2$ for the coefficient of $t^j$ in
$(1 + t + t^2)^u = \sum_{i \ge 0} \binom{u}{i}(t + t^2)^i$ (Comtet's extension), where
$\binom{u}{i}$ is the generalized binomial coefficient. Then for every complex $x$ and every
$n \in \mathbb{N}$,

$$\sum_{k=0}^{n} \binom{2n - x}{n - k}_2 \binom{x}{k}_2 (-1)^k =
\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{2n - 2x}{n - 2k}_2 \binom{x}{k}_2.$$

Source: Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of
Integer Sequences 28 (2025), Article 25.3.5, Theorem 23 (`jis-2025-25.3.5-thm-23`). -/
public theorem sum_extended_trinomial_alternating_eq (x : ℂ) (n : ℕ) :
    let E : ℂ → ℕ → ℂ := fun u j =>
      coeff j ((PowerSeries.binomialSeries ℂ u).subst (X + X ^ 2 : PowerSeries ℂ))
    ∑ k ∈ Finset.range (n + 1), E (2 * n - x) (n - k) * E x k * (-1) ^ k =
      ∑ k ∈ Finset.range (n / 2 + 1), E (2 * n - 2 * x) (n - 2 * k) * E x k := by
  let T : PowerSeries ℂ := X + X ^ 2
  let P (u : ℂ) : PowerSeries ℂ := (binomialSeries ℂ u).subst T
  have hT : HasSubst T := HasSubst.of_constantCoeff_zero' (by simp [T])
  have hN : HasSubst (-X : PowerSeries ℂ) := HasSubst.of_constantCoeff_zero' (by simp)
  have hS : HasSubst (X ^ 2 : PowerSeries ℂ) := HasSubst.X_pow (by decide)
  have substT {D : PowerSeries ℂ} (hD : HasSubst D) : T.subst D = D + D ^ 2 := by
    change (X + X ^ 2 : PowerSeries ℂ).subst D = _
    rw [← coe_substAlgHom hD, map_add, map_pow, substAlgHom_X hD]
  have hneg : rescale (-1) (P x) = (binomialSeries ℂ x).subst (-X + X ^ 2 : PowerSeries ℂ) := by
    dsimp only [P]
    rw [rescale_eq_subst, neg_one_smul, subst_comp_subst_apply hT hN, substT hN, neg_sq]
  have hsq : (P x).subst (X ^ 2 : PowerSeries ℂ) =
      (binomialSeries ℂ x).subst (X ^ 2 + X ^ 4 : PowerSeries ℂ) := by
    dsimp only [P]
    rw [subst_comp_subst_apply hT hS, substT hS, ← pow_mul]
  have hprod : P x * rescale (-1) (P x) = (P x).subst (X ^ 2 : PowerSeries ℂ) := by
    rw [hneg, hsq]
    dsimp only [P]
    rw [binomialSeries_subst_mul T (-X + X ^ 2) (by simp [T]) (by simp) x]
    congr 1
    dsimp only [T]
    ring
  have hadd : P (2 * n - 2 * x) * P x = P (2 * n - x) := by
    have he : 2 * (n : ℂ) - 2 * x + x = 2 * n - x := by ring
    dsimp only [P]
    rw [← subst_mul hT, ← binomialSeries_add, he]
  change ∑ k ∈ Finset.range (n + 1), coeff (n - k) (P (2 * n - x)) * coeff k (P x) * (-1) ^ k =
    ∑ k ∈ Finset.range (n / 2 + 1), coeff (n - 2 * k) (P (2 * n - 2 * x)) * coeff k (P x)
  calc
    _ = coeff n (P (2 * n - x) * rescale (-1) (P x)) := by
      rw [coeff_mul_eq_sum_range_right]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [coeff_rescale, mul_comm ((-1 : ℂ) ^ k), mul_assoc]
    _ = coeff n (P (2 * n - 2 * x) * (P x).subst (X ^ 2 : PowerSeries ℂ)) := by
      rw [← hadd, mul_assoc, hprod]
    _ = _ := coeff_mul_subst_X_sq _ _ _

end MetaMathlibExt
