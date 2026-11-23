/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.Valuation.Integers

/-!
# Denominators of the Hurwitz-type numbers of Sl

The differential equations for Sl and Cl give coefficient recurrences over the rationals.
Through degree `n < ℓ`, each integration step divides by a unit in the valuation ring at `ℓ`.
The inverse of the shifted series `Sl(u)/u` has constant coefficient one, so its recurrence
introduces no further denominators.

## Reference

Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with Bernoulli-Hurwitz
Numbers by Elliptic Gauss Sums in Eisenstein Integers Case*, introduction, statement of
Theorem 2.5.
[arXiv:2204.04425](https://arxiv.org/abs/2204.04425)
-/

namespace MetaMathlibExt

open PowerSeries Finset.HasAntidiagonal

namespace sl_hurwitz_numbers_den_coprime

private lemma coeff_sq_mem (A : Subring ℚ) (F : PowerSeries ℚ) (n : ℕ)
    (h : ∀ i ≤ n, coeff i F ∈ A) : coeff n (F ^ 2) ∈ A := by
  rw [pow_two, coeff_mul]
  exact A.sum_mem fun x hx =>
    A.mul_mem (h _ (antidiagonal.fst_le hx)) (h _ (antidiagonal.snd_le hx))

private lemma coeff_mem_below_prime (S C : PowerSeries ℚ) (hS : derivative S = C ^ 2)
    (hC : derivative C = -(S ^ 2)) (hS0 : constantCoeff S = 0) (hC0 : constantCoeff C = 1)
    (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) (hn : n < ℓ) :
    coeff n S ∈ (Rat.padicValuation ℓ).integer ∧ coeff n C ∈ (Rat.padicValuation ℓ).integer := by
  let A := (Rat.padicValuation ℓ).integer
  change coeff n S ∈ A ∧ coeff n C ∈ A
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [coeff_zero_eq_constantCoeff_apply, hS0, hC0]
    | succ n =>
      have hstep (F : PowerSeries ℚ) (hF : coeff n (derivative F) ∈ A) : coeff (n + 1) F ∈ A := by
        have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
        have hinv : ((n + 1 : ℕ) : ℚ)⁻¹ ∈ A := by
          apply Rat.padicValuation_le_one_iff.mpr
          rw [Rat.den_inv_of_ne_zero hne, Rat.num_natCast, Int.natAbs_natCast]
          exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n) hn
        have h := A.mul_mem hF hinv
        simpa only [coeff_derivative, ← Nat.cast_add_one, mul_assoc, mul_inv_cancel₀ hne,
          mul_one] using h
      constructor
      · apply hstep
        rw [hS]
        exact coeff_sq_mem A C n fun i hi => (ih i (by omega) (by omega)).2
      · apply hstep
        rw [hC, map_neg]
        exact A.neg_mem (coeff_sq_mem A S n fun i hi => (ih i (by omega) (by omega)).1)

private lemma coeff_inv_mem (A : Subring ℚ) (F : PowerSeries ℚ) (hF : constantCoeff F = 1)
    (n : ℕ) (h : ∀ i ≤ n, coeff i F ∈ A) : coeff n F⁻¹ ∈ A := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [coeff_inv, hF]
    split
    · simp
    · simp only [inv_one, neg_one_mul]
      apply A.neg_mem
      refine A.sum_mem fun x hx => ?_
      split_ifs with hlt
      · exact A.mul_mem (h _ (antidiagonal.fst_le hx)) (ih _ hlt fun i hi => h i (hi.trans hlt.le))
      · exact A.zero_mem

end sl_hurwitz_numbers_den_coprime

open sl_hurwitz_numbers_den_coprime

/-- At the index `2 * (ℓ - 1) / 3`, the reduced denominator of the Sl coefficient is prime to
`ℓ` when `ℓ ≡ 7 [MOD 9]`. For `ℓ ≡ 4 [MOD 9]` the same holds for the Laurent coefficient of
`1/Sl`, obtained by inverting the unit series `Sl(u)/u` and shifting the index by one.

Source: Akihiro Goto, *Congruence Relations Connecting Tate-Shafarevich Groups with
Bernoulli-Hurwitz Numbers by Elliptic Gauss Sums in the Eisenstein Integers Case*, INTEGERS 26
(2026), Article A112, Theorem 3 (`integers-2026-A112-thm-3`), first sentence. -/
public theorem sl_hurwitz_numbers_den_coprime (S C : PowerSeries ℚ)
    (hS : PowerSeries.derivative (R := ℚ) S = C ^ 2)
    (hC : PowerSeries.derivative (R := ℚ) C = -(S ^ 2))
    (hS0 : PowerSeries.constantCoeff S = 0) (hC0 : PowerSeries.constantCoeff C = 1)
    (ℓ : ℕ) (hℓ : ℓ.Prime) :
    (ℓ % 9 = 7 → ¬ ℓ ∣ (PowerSeries.coeff (2 * (ℓ - 1) / 3) S).den) ∧
    (ℓ % 9 = 4 → ¬ ℓ ∣ (PowerSeries.coeff (2 * (ℓ - 1) / 3 + 1)
      (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) S)⁻¹).den) := by
  let : Fact ℓ.Prime := ⟨hℓ⟩
  have hcoeff := coeff_mem_below_prime S C hS hC hS0 hC0 ℓ
  constructor
  · intro h7
    exact Rat.padicValuation_le_one_iff.mp (hcoeff _ (by omega)).1
  · intro h4
    have hne : ℓ ≠ 4 := fun e => (by decide : ¬ Nat.Prime 4) (e ▸ hℓ)
    have hbound : 2 * (ℓ - 1) / 3 + 2 < ℓ := by omega
    apply Rat.padicValuation_le_one_iff.mp
    apply coeff_inv_mem (Rat.padicValuation ℓ).integer
    · rw [constantCoeff_mk]
      have h := congrArg (coeff (R := ℚ) 0) hS
      rw [coeff_derivative, coeff_zero_eq_constantCoeff_apply, map_pow, hC0] at h
      simpa using h
    · intro i hi
      rw [coeff_mk]
      exact (hcoeff _ (by omega)).1

end MetaMathlibExt
