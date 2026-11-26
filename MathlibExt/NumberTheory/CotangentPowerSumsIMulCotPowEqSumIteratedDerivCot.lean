/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import MathlibExt.NumberTheory.CotangentPowerSums
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Nat.Choose.Sum

/-!
# Cotangent powers through cotangent derivatives

We prove that `(i cot x)^r` equals `((-1)^r + 1)/2` plus a linear combination of the
derivatives `i^j cot^{(j-1)}(x)` weighted by Girstmair's cotangent power coefficients.

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Proposition 1 (`integers-2025-A63-prop-1`).
-/

namespace MetaMathlibExt

namespace cotPowerDeriv

open Finset Polynomial

/-- The polynomial expressing the `m`-th cotangent derivative as a polynomial in `cot x`. -/
private noncomputable def cotDerivPoly : ℕ → ℝ[X]
  | 0 => X
  | m + 1 => (cotDerivPoly m).derivative * (-(1 + X ^ 2))

private theorem hasDerivAt_cot {x : ℝ} (hx : Real.sin x ≠ 0) :
    HasDerivAt Real.cot (-(1 + Real.cot x ^ 2)) x := by
  rw [show Real.cot = fun y => Real.cos y / Real.sin y from
    funext Real.cot_eq_cos_div_sin]
  convert (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx using 1
  field_simp
  ring

open scoped Topology in
private theorem iteratedDeriv_cot (m : ℕ) (x : ℝ) (hx : Real.sin x ≠ 0) :
    iteratedDeriv m Real.cot x = (cotDerivPoly m).eval (Real.cot x) := by
  induction m generalizing x with
  | zero => simp [cotDerivPoly]
  | succ m ih =>
    have heq : iteratedDeriv m Real.cot =ᶠ[𝓝 x]
        fun y => (cotDerivPoly m).eval (Real.cot y) := by
      filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hx] with y hy
      exact ih y hy
    have h := ((cotDerivPoly m).hasDerivAt (Real.cot x)).comp x (hasDerivAt_cot hx)
    have hfun : (fun x => (cotDerivPoly m).eval x) ∘ Real.cot =
        fun y => (cotDerivPoly m).eval (Real.cot y) := rfl
    rw [hfun] at h
    rw [iteratedDeriv_succ, heq.deriv_eq, h.deriv, cotDerivPoly, eval_mul, eval_neg, eval_add,
      eval_one, eval_pow, eval_X]

private theorem map_neg_one_add_X_sq :
    (-(1 + X ^ 2) : ℝ[X]).map Complex.ofRealHom = -(1 + X ^ 2) := by
  simp

private theorem map_cotDerivPoly_succ (m : ℕ) :
    (cotDerivPoly (m + 1)).map Complex.ofRealHom =
      ((cotDerivPoly m).map Complex.ofRealHom).derivative * (-(1 + X ^ 2)) := by
  rw [cotDerivPoly, Polynomial.map_mul, ← derivative_map, map_neg_one_add_X_sq]

private theorem eval_map_cotDerivPoly (m : ℕ) (u : ℝ) :
    ((cotDerivPoly m).map Complex.ofRealHom).eval (u : ℂ)
      = (((cotDerivPoly m).eval u : ℝ) : ℂ) := by
  have h := Polynomial.eval_map_apply Complex.ofRealHom (p := cotDerivPoly m) (x := u)
  exact h

/-- The Stirling-number sum in `cotangentPowerCoeff`, without the sign prefactor. -/
private def stirlingSum (r j : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc j r,
    (-2) ^ (k - j) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) * (Nat.stirlingFirst k j : ℚ)

private theorem cotangentPowerCoeff_eq (r j : ℕ) :
    cotangentPowerCoeff r j = (-1) ^ (r - 1) * stirlingSum r j :=
  rfl

private theorem stirlingSum_eq_zero_of_gt {r j : ℕ} (h : r < j) : stirlingSum r j = 0 := by
  rw [stirlingSum, Icc_eq_empty (by omega : ¬ j ≤ r), sum_empty]

private theorem cotangentPowerCoeff_eq_zero_of_gt {r j : ℕ} (h : r < j) :
    cotangentPowerCoeff r j = 0 := by
  rw [cotangentPowerCoeff_eq, stirlingSum_eq_zero_of_gt h, mul_zero]

private theorem mul_choose_succ (r k : ℕ) (hr : 1 ≤ r) :
    r * (r + 1).choose k
      = r * (r - 1).choose k + 2 * k * r.choose k + (k - 1) * r.choose (k - 1) := by
  obtain ⟨r', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  cases k with
  | zero => simp [Nat.choose_zero_right]
  | succ t =>
    cases t with
    | zero =>
      simp only [Nat.zero_add, Nat.choose_one_right]
      ring
    | succ s =>
      simp only [Nat.add_sub_cancel]
      have hP1 := Nat.choose_succ_succ' (r' + 1) (s + 1)
      have hP2 := Nat.choose_succ_succ' r' s
      have hP3 := Nat.choose_succ_succ' r' (s + 1)
      have hA1 := Nat.add_one_mul_choose_eq r' (s + 1)
      have hA2 := Nat.add_one_mul_choose_eq r' s
      linear_combination (r' + 1) * hP1 + (r' + 1) * hP2 + (r' + 1) * hP3 + 2 * hA1 + hA2

private theorem stirlingSum_succ (r j : ℕ) (hr : 1 ≤ r) (hj : 2 ≤ j) :
    stirlingSum (r + 1) j = stirlingSum (r - 1) j + stirlingSum r (j - 1) / r := by
  by_cases hle : j ≤ r + 1
  · have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
    have hsplit : ∀ k ∈ Finset.Icc (j - 1) r,
        (-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            (Nat.stirlingFirst k (j - 1) : ℚ)
          = ((-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
              (Nat.stirlingFirst (k + 1) j : ℚ))
            - ((-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
              ((k : ℚ) * (Nat.stirlingFirst k j : ℚ))) := by
      intro k hk
      have hSS := Nat.stirlingFirst_succ_succ k (j - 1)
      rw [show (j - 1) + 1 = j by omega] at hSS
      have hSSQ : (Nat.stirlingFirst (k + 1) j : ℚ)
          = (k : ℚ) * (Nat.stirlingFirst k j : ℚ)
            + (Nat.stirlingFirst k (j - 1) : ℚ) := by
        exact_mod_cast hSS
      have hStQ : (Nat.stirlingFirst k (j - 1) : ℚ)
          = (Nat.stirlingFirst (k + 1) j : ℚ)
            - (k : ℚ) * (Nat.stirlingFirst k j : ℚ) := by
        linear_combination -hSSQ
      rw [hStQ]
      ring
    have hA : (∑ k ∈ Finset.Icc (j - 1) r,
          (-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            (Nat.stirlingFirst (k + 1) j : ℚ))
        = ∑ k ∈ Finset.Icc j (r + 1),
          (-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
            (((k - 1 : ℕ) : ℚ) * (r.choose (k - 1) : ℚ)) *
            (Nat.stirlingFirst k j : ℚ) := by
      apply Finset.sum_bij (fun k _ => k + 1)
      · intro k hk
        simp only [Finset.mem_Icc] at hk ⊢
        omega
      · intro a _ b _ hab
        exact Nat.add_right_cancel hab
      · intro b hb
        simp only [Finset.mem_Icc] at hb
        refine ⟨b - 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        rw [Nat.add_sub_cancel, show (k + 1) - j = k - (j - 1) by omega]
        obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
        have ht0 : ((t.factorial : ℕ) : ℚ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        have ht1 : ((t + 1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp [ht0, ht1]
    have hIcc : Finset.Icc (j - 1) r = insert (j - 1) (Finset.Icc j r) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hBdrop : (∑ k ∈ Finset.Icc (j - 1) r,
          (-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            ((k : ℚ) * (Nat.stirlingFirst k j : ℚ)))
        = ∑ k ∈ Finset.Icc j r,
          (-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            ((k : ℚ) * (Nat.stirlingFirst k j : ℚ)) := by
      rw [hIcc, sum_insert (by rw [Finset.mem_Icc]; omega)]
      have h0 : (-2 : ℚ) ^ ((j - 1) - (j - 1)) / (((j - 1) - 1).factorial : ℚ) *
          (r.choose (j - 1) : ℚ) *
          (((j - 1 : ℕ) : ℚ) * (Nat.stirlingFirst (j - 1) j : ℚ)) = 0 := by
        simp [Nat.stirlingFirst_eq_zero_of_lt (by omega : j - 1 < j)]
      rw [h0, zero_add]
    have hBneg : ∀ k ∈ Finset.Icc j r,
        (-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            ((k : ℚ) * (Nat.stirlingFirst k j : ℚ))
          = -((-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
            (2 * (k : ℚ) * (r.choose k : ℚ)) * (Nat.stirlingFirst k j : ℚ)) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      rw [show k - (j - 1) = (k - j) + 1 by omega, pow_succ]
      ring
    have hBsum : (∑ k ∈ Finset.Icc j r,
          (-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
            ((k : ℚ) * (Nat.stirlingFirst k j : ℚ)))
        = -(∑ k ∈ Finset.Icc j r,
          (-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
            (2 * (k : ℚ) * (r.choose k : ℚ)) * (Nat.stirlingFirst k j : ℚ)) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl (fun k hk => hBneg k hk)
    have hVextend : (∑ k ∈ Finset.Icc j r,
          (-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
            (2 * (k : ℚ) * (r.choose k : ℚ)) * (Nat.stirlingFirst k j : ℚ))
        = ∑ k ∈ Finset.Icc j (r + 1),
          (-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
            (2 * (k : ℚ) * (r.choose k : ℚ)) * (Nat.stirlingFirst k j : ℚ) := by
      apply sum_subset (Icc_subset_Icc_right (by omega : r ≤ r + 1))
      intro k hk hkn
      simp only [Finset.mem_Icc] at hk hkn
      have h0 : r.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega : r < k)
      simp [h0]
    have hPrev : (r : ℚ) * stirlingSum (r - 1) j
        = ∑ k ∈ Finset.Icc j (r + 1),
          (r : ℚ) * ((-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
            ((r - 1).choose k : ℚ) * (Nat.stirlingFirst k j : ℚ)) := by
      rw [stirlingSum, mul_sum]
      apply sum_subset (Icc_subset_Icc_right (by omega : r - 1 ≤ r + 1))
      intro k hk hkn
      simp only [Finset.mem_Icc] at hk hkn
      have h0 : (r - 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega : r - 1 < k)
      simp [h0]
    have hSsplit : stirlingSum r (j - 1)
        = (∑ k ∈ Finset.Icc j (r + 1),
            (-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
              (((k - 1 : ℕ) : ℚ) * (r.choose (k - 1) : ℚ)) *
              (Nat.stirlingFirst k j : ℚ))
          + (∑ k ∈ Finset.Icc j (r + 1),
            (-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
              (2 * (k : ℚ) * (r.choose k : ℚ)) * (Nat.stirlingFirst k j : ℚ)) := by
      have e1 : stirlingSum r (j - 1)
          = ∑ k ∈ Finset.Icc (j - 1) r,
            ((-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
                (Nat.stirlingFirst (k + 1) j : ℚ)
              - ((-2 : ℚ) ^ (k - (j - 1)) / ((k - 1).factorial : ℚ) * (r.choose k : ℚ) *
                ((k : ℚ) * (Nat.stirlingFirst k j : ℚ)))) := by
        rw [stirlingSum]
        exact sum_congr rfl (fun k hk => hsplit k hk)
      rw [e1, sum_sub_distrib, hA, hBdrop, hBsum, hVextend, sub_neg_eq_add]
    have hmul : (r : ℚ) * stirlingSum (r + 1) j
        = (r : ℚ) * stirlingSum (r - 1) j + stirlingSum r (j - 1) := by
      rw [stirlingSum, mul_sum, hPrev, hSsplit, ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      have hbin : (r : ℚ) * ((r + 1).choose k : ℚ)
          = (r : ℚ) * ((r - 1).choose k : ℚ)
            + 2 * (k : ℚ) * (r.choose k : ℚ)
            + ((k - 1 : ℕ) : ℚ) * (r.choose (k - 1) : ℚ) := by
        exact_mod_cast mul_choose_succ r k hr
      linear_combination ((-2 : ℚ) ^ (k - j) / ((k - 1).factorial : ℚ) *
        (Nat.stirlingFirst k j : ℚ)) * hbin
    refine mul_left_cancel₀ hr0 ?_
    rw [hmul]
    field_simp [hr0]
  · simp only [stirlingSum, Icc_eq_empty hle, Icc_eq_empty (by omega : ¬ j ≤ r - 1),
      Icc_eq_empty (by omega : ¬ j - 1 ≤ r), sum_empty, add_zero, zero_div]

private theorem cotangentPowerCoeff_succ (r j : ℕ) (hr : 1 ≤ r) (hj : 2 ≤ j)
    (hle : j ≤ r + 1) :
    cotangentPowerCoeff (r + 1) j
      = cotangentPowerCoeff (r - 1) j - cotangentPowerCoeff r (j - 1) / r := by
  have hE := stirlingSum_succ r j hr hj
  rw [cotangentPowerCoeff_eq, cotangentPowerCoeff_eq, cotangentPowerCoeff_eq,
    Nat.add_sub_cancel]
  have hpow1 : (-1 : ℚ) ^ (r - 1) = -(-1 : ℚ) ^ r := by
    conv_rhs => rw [show r = (r - 1) + 1 by omega, pow_add, pow_one]
    ring
  rw [hpow1]
  rcases eq_or_ne r 1 with rfl | hr2
  · rw [show (1 : ℕ) - 1 - 1 = 0 by decide, pow_zero, hE]
    have h0 : stirlingSum (1 - 1) j = 0 := stirlingSum_eq_zero_of_gt (by omega : 1 - 1 < j)
    rw [h0]
    ring
  · have hr2' : 2 ≤ r := by omega
    have hpow2 : (-1 : ℚ) ^ (r - 1 - 1) = (-1 : ℚ) ^ r := by
      conv_rhs => rw [show r = (r - 1 - 1) + 2 by omega, pow_add]
      norm_num
    rw [hpow2]
    linear_combination (-1 : ℚ) ^ r * hE

private theorem stirlingSum_one (m : ℕ) : stirlingSum m 1 = (1 - (-1 : ℚ) ^ m) / 2 := by
  cases m with
  | zero =>
    rw [stirlingSum, Icc_eq_empty (by decide : ¬ (1 : ℕ) ≤ 0), sum_empty]
    norm_num
  | succ n =>
    have hterm : ∀ k ∈ Finset.Icc 1 (n + 1),
        (-2 : ℚ) ^ (k - 1) / ((k - 1).factorial : ℚ) * ((n + 1).choose k : ℚ) *
            (Nat.stirlingFirst k 1 : ℚ)
          = (-2 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rw [Nat.stirlingFirst_one_right]
      have ht0 : ((t.factorial : ℕ) : ℚ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      field_simp [ht0]
    have hsum : stirlingSum (n + 1) 1
        = ∑ k ∈ Finset.Icc 1 (n + 1),
          (-2 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ) := by
      rw [stirlingSum]
      exact sum_congr rfl (fun k hk => hterm k hk)
    have h2 : ∀ k ∈ Finset.Icc 1 (n + 1),
        (-2 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ)
          = (-1 / 2 : ℚ) * ((-2 : ℚ) ^ k * ((n + 1).choose k : ℚ)) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rw [pow_succ']
      ring
    have hrange : Finset.range (n + 1 + 1)
        = insert 0 (Finset.Icc 1 (n + 1)) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have e2 : (∑ k ∈ Finset.Icc 1 (n + 1),
          (-2 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ))
        = (-1 / 2 : ℚ) * (∑ k ∈ Finset.Icc 1 (n + 1),
          (-2 : ℚ) ^ k * ((n + 1).choose k : ℚ)) := by
      have hcongr : (∑ k ∈ Finset.Icc 1 (n + 1),
            (-2 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ))
          = ∑ k ∈ Finset.Icc 1 (n + 1),
            (-1 / 2 : ℚ) * ((-2 : ℚ) ^ k * ((n + 1).choose k : ℚ)) :=
        sum_congr rfl (fun k hk => h2 k hk)
      rw [hcongr, ← mul_sum]
    have e3 : (∑ k ∈ Finset.Icc 1 (n + 1),
          (-2 : ℚ) ^ k * ((n + 1).choose k : ℚ))
        = (-1 : ℚ) ^ (n + 1) - 1 := by
      have hadd := add_pow (-2 : ℚ) 1 (n + 1)
      rw [show (-2 : ℚ) + 1 = -1 by norm_num, hrange,
        sum_insert (by simp : (0 : ℕ) ∉ Finset.Icc 1 (n + 1))] at hadd
      have hf0 : (-2 : ℚ) ^ (0 : ℕ) * (1 : ℚ) ^ ((n + 1) - 0) *
          ((n + 1).choose 0 : ℚ) = 1 := by simp
      rw [hf0] at hadd
      have hcongr2 : (∑ k ∈ Finset.Icc 1 (n + 1),
            (-2 : ℚ) ^ k * (1 : ℚ) ^ ((n + 1) - k) * ((n + 1).choose k : ℚ))
          = ∑ k ∈ Finset.Icc 1 (n + 1),
            (-2 : ℚ) ^ k * ((n + 1).choose k : ℚ) := by
        apply sum_congr rfl
        intro k hk
        simp
      rw [hcongr2] at hadd
      linear_combination -hadd
    have hbin : (∑ k ∈ Finset.Icc 1 (n + 1),
          (-2 : ℚ) ^ (k - 1) * ((n + 1).choose k : ℚ))
        = (1 - (-1 : ℚ) ^ (n + 1)) / 2 := by
      rw [e2, e3]
      ring
    rw [hsum, hbin]

private theorem cotangentPowerCoeff_one (m : ℕ) :
    cotangentPowerCoeff m 1 = if Odd m then 1 else 0 := by
  rw [cotangentPowerCoeff_eq, stirlingSum_one]
  by_cases hm : Odd m
  · simp only [hm, ite_true]
    obtain ⟨t, rfl⟩ := hm
    rw [show 2 * t + 1 - 1 = 2 * t by omega]
    have h1 : (-1 : ℚ) ^ (2 * t + 1) = -1 := Odd.neg_one_pow ⟨t, rfl⟩
    have h2 : (-1 : ℚ) ^ (2 * t) = 1 := Even.neg_one_pow ⟨t, by ring⟩
    rw [h1, h2]
    norm_num
  · simp only [hm, ite_false]
    have hme : Even m := Nat.not_odd_iff_even.mp hm
    have h1 : (-1 : ℚ) ^ m = 1 := Even.neg_one_pow hme
    rw [h1]
    norm_num

private theorem cotangentPowerCoeff_succ_one (r : ℕ) (hr : 1 ≤ r) :
    cotangentPowerCoeff (r + 1) 1 = cotangentPowerCoeff (r - 1) 1 := by
  have hpar : Odd (r + 1) ↔ Odd (r - 1) := by
    rw [Nat.odd_iff, Nat.odd_iff]
    omega
  simp [cotangentPowerCoeff_one, hpar]

/-- The polynomial identity underlying the cotangent power expansion. -/
private def polyEq (n : ℕ) : Prop :=
  (C Complex.I * X : ℂ[X]) ^ n = C (((-1 : ℂ) ^ n + 1) / 2) +
    ∑ j ∈ Finset.Icc 1 n, C (cotangentPowerCoeff n j : ℂ) * C Complex.I ^ j *
      (cotDerivPoly (j - 1)).map Complex.ofRealHom

private theorem polyEq_zero : polyEq 0 := by
  simp only [polyEq, pow_zero, show Finset.Icc 1 0 = ∅ by decide, sum_empty, add_zero]
  norm_num [map_one]

private theorem polyEq_one : polyEq 1 := by
  simp only [polyEq, pow_one, Finset.Icc_self, sum_singleton]
  rw [cotangentPowerCoeff_one_one]
  simp [cotDerivPoly]

private theorem derivative_term (c : ℚ) (j : ℕ) (Q : ℝ[X]) :
    (C (c : ℂ) * C Complex.I ^ j * Q.map Complex.ofRealHom : ℂ[X]).derivative
      = C (c : ℂ) * C Complex.I ^ j * (Q.map Complex.ofRealHom).derivative := by
  rw [mul_assoc, derivative_C_mul, ← map_pow, derivative_C_mul, map_pow, ← mul_assoc]

private theorem neg_one_add_mul_derivative_map (m : ℕ) :
    (-(1 + X ^ 2) : ℂ[X]) * ((cotDerivPoly m).map Complex.ofRealHom).derivative
      = (cotDerivPoly (m + 1)).map Complex.ofRealHom := by
  rw [map_cotDerivPoly_succ]
  ring

private theorem poly_step (r : ℕ) (hr : 1 ≤ r) :
    polyEq (r - 1) → polyEq r → polyEq (r + 1) := by
  intro ih1 ih2
  simp only [polyEq] at ih1 ih2 ⊢
  have hI2 : (C Complex.I : ℂ[X]) ^ 2 = -1 := by
    rw [← map_pow, pow_two, Complex.I_mul_I, map_neg, map_one]
  have hY2 : (C Complex.I * X : ℂ[X]) ^ 2 = -(X ^ 2) := by
    rw [mul_pow, hI2]
    ring
  have hYpow : (C Complex.I * X : ℂ[X]) ^ (r + 1)
      = (C Complex.I * X : ℂ[X]) ^ (r - 1) * (C Complex.I * X : ℂ[X]) ^ 2 := by
    rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
  have hDY : (C Complex.I * X : ℂ[X]).derivative = C Complex.I :=
    derivative_C_mul_X _
  have hkey : C (r : ℂ) * C Complex.I * (C Complex.I * X : ℂ[X]) ^ (r + 1)
      = C (r : ℂ) * C Complex.I * (C Complex.I * X : ℂ[X]) ^ (r - 1)
        + (-(1 + X ^ 2)) * ((C Complex.I * X : ℂ[X]) ^ r).derivative := by
    rw [hYpow, hY2, derivative_pow, hDY]
    ring
  have hne : C (r : ℂ) * C Complex.I ≠ 0 := by
    apply mul_ne_zero
    · rw [C_ne_zero]
      exact_mod_cast (by omega : r ≠ 0)
    · rw [C_ne_zero]
      exact Complex.I_ne_zero
  have hterm : ∀ j ∈ Finset.Icc 1 r,
      (-(1 + X ^ 2) : ℂ[X]) *
          (C ((cotangentPowerCoeff r j : ℚ) : ℂ) * C Complex.I ^ j *
            (cotDerivPoly (j - 1)).map Complex.ofRealHom).derivative
        = C ((cotangentPowerCoeff r j : ℚ) : ℂ) * C Complex.I ^ j *
          (cotDerivPoly j).map Complex.ofRealHom := by
    intro j hjj
    simp only [Finset.mem_Icc] at hjj
    have hQ : (cotDerivPoly j).map Complex.ofRealHom
        = (-(1 + X ^ 2) : ℂ[X]) *
          ((cotDerivPoly (j - 1)).map Complex.ofRealHom).derivative := by
      have h := neg_one_add_mul_derivative_map (j - 1)
      rw [show (j - 1) + 1 = j by omega] at h
      exact h.symm
    rw [derivative_term, hQ]
    ring
  have hre : (∑ j ∈ Finset.Icc 1 r,
        C ((cotangentPowerCoeff r j : ℚ) : ℂ) * C Complex.I ^ j *
          (cotDerivPoly j).map Complex.ofRealHom)
      = ∑ j ∈ Finset.Icc 2 (r + 1),
        C ((cotangentPowerCoeff r (j - 1) : ℚ) : ℂ) * C Complex.I ^ (j - 1) *
          (cotDerivPoly (j - 1)).map Complex.ofRealHom := by
    apply Finset.sum_bij (fun j _ => j + 1)
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro a _ b _ hab
      exact Nat.add_right_cancel hab
    · intro b hb
      simp only [Finset.mem_Icc] at hb
      refine ⟨b - 1, by simp only [Finset.mem_Icc]; omega, by omega⟩
    · intro k hk
      rw [Nat.add_sub_cancel]
  have hsecond : (∑ j ∈ Finset.Icc 1 r, (-(1 + X ^ 2) : ℂ[X]) *
        (C ((cotangentPowerCoeff r j : ℚ) : ℂ) * C Complex.I ^ j *
          (cotDerivPoly (j - 1)).map Complex.ofRealHom).derivative)
      = ∑ j ∈ Finset.Icc 2 (r + 1),
        C ((cotangentPowerCoeff r (j - 1) : ℚ) : ℂ) * C Complex.I ^ (j - 1) *
          (cotDerivPoly (j - 1)).map Complex.ofRealHom := by
    rw [← hre]
    exact sum_congr rfl (fun j hjj => hterm j hjj)
  have ha : ((-1 : ℂ) ^ (r - 1) + 1) / 2 = ((-1 : ℂ) ^ (r + 1) + 1) / 2 := by
    have hpow : (-1 : ℂ) ^ (r + 1) = (-1 : ℂ) ^ (r - 1) := by
      conv_lhs => rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
      norm_num
    rw [hpow]
  have hS1 : C (r : ℂ) * C Complex.I *
        (∑ j ∈ Finset.Icc 1 (r - 1), C ((cotangentPowerCoeff (r - 1) j : ℚ) : ℂ) *
          C Complex.I ^ j * (cotDerivPoly (j - 1)).map Complex.ofRealHom)
      = ∑ j ∈ Finset.Icc 1 (r + 1), C (r : ℂ) * C Complex.I *
        (C ((cotangentPowerCoeff (r - 1) j : ℚ) : ℂ) * C Complex.I ^ j *
          (cotDerivPoly (j - 1)).map Complex.ofRealHom) := by
    rw [mul_sum]
    apply sum_subset (Icc_subset_Icc_right (by omega : r - 1 ≤ r + 1))
    intro j hjj hjnc
    simp only [Finset.mem_Icc] at hjj hjnc
    have h0 : cotangentPowerCoeff (r - 1) j = 0 :=
      cotangentPowerCoeff_eq_zero_of_gt (by omega : r - 1 < j)
    simp [h0]
  have hS2 : (∑ j ∈ Finset.Icc 2 (r + 1),
        C ((cotangentPowerCoeff r (j - 1) : ℚ) : ℂ) * C Complex.I ^ (j - 1) *
          (cotDerivPoly (j - 1)).map Complex.ofRealHom)
      = ∑ j ∈ Finset.Icc 1 (r + 1),
        (if j = 1 then (0 : ℂ[X]) else C ((cotangentPowerCoeff r (j - 1) : ℚ) : ℂ) *
          C Complex.I ^ (j - 1) * (cotDerivPoly (j - 1)).map Complex.ofRealHom) := by
    have hIcc : Finset.Icc 1 (r + 1) = insert 1 (Finset.Icc 2 (r + 1)) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, sum_insert (by simp : (1 : ℕ) ∉ Finset.Icc 2 (r + 1))]
    simp only [ite_true, zero_add]
    apply sum_congr rfl
    intro j hjj
    simp only [Finset.mem_Icc] at hjj
    simp [show j ≠ 1 by omega]
  have hmain : C (r : ℂ) * C Complex.I * (C Complex.I * X : ℂ[X]) ^ (r + 1)
      = C (r : ℂ) * C Complex.I *
        (C (((-1 : ℂ) ^ (r + 1) + 1) / 2) +
          ∑ j ∈ Finset.Icc 1 (r + 1), C (cotangentPowerCoeff (r + 1) j : ℂ) *
            C Complex.I ^ j * (cotDerivPoly (j - 1)).map Complex.ofRealHom) := by
    rw [hkey, ih1, ih2, derivative_add, derivative_C, zero_add, derivative_sum, mul_sum,
      hsecond, mul_add, mul_add, ha, add_assoc]
    congr 1
    rw [hS1, hS2, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hjj
    simp only [Finset.mem_Icc] at hjj
    by_cases hj1 : j = 1
    · subst hj1
      simp only [ite_true, add_zero]
      rw [← cotangentPowerCoeff_succ_one r hr]
    · have hj2 : 2 ≤ j := by omega
      simp only [hj1, ite_false]
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      have hcrec : cotangentPowerCoeff (r + 1) (t + 1)
          = cotangentPowerCoeff (r - 1) (t + 1) - cotangentPowerCoeff r t / r :=
        cotangentPowerCoeff_succ r (t + 1) hr (by omega) (by omega)
      have hr0 : (r : ℚ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
      have hc : (r : ℚ) * cotangentPowerCoeff (r + 1) (t + 1)
          = (r : ℚ) * cotangentPowerCoeff (r - 1) (t + 1) - cotangentPowerCoeff r t := by
        field_simp [hr0] at hcrec ⊢
        linear_combination hcrec
      have hC0 : C (r : ℂ) * C (cotangentPowerCoeff (r + 1) (t + 1) : ℂ)
          - C (r : ℂ) * C (cotangentPowerCoeff (r - 1) (t + 1) : ℂ)
          + C (cotangentPowerCoeff r t : ℂ) = 0 := by
        have h0 : (r : ℂ) * (cotangentPowerCoeff (r + 1) (t + 1) : ℂ)
            - (r : ℂ) * (cotangentPowerCoeff (r - 1) (t + 1) : ℂ)
            + (cotangentPowerCoeff r t : ℂ) = 0 := by
          have hcC' : (r : ℂ) * (cotangentPowerCoeff (r + 1) (t + 1) : ℂ)
              = (r : ℂ) * (cotangentPowerCoeff (r - 1) (t + 1) : ℂ)
                - (cotangentPowerCoeff r t : ℂ) := by
            exact_mod_cast hc
          linear_combination hcC'
        have hC := congrArg (C : ℂ → ℂ[X]) h0
        simp only [map_sub, map_add, map_zero] at hC
        simpa [map_mul] using hC
      rw [pow_succ']
      linear_combination ((C (r : ℂ) * C (cotangentPowerCoeff (r - 1) (t + 1) : ℂ)
          - C (r : ℂ) * C (cotangentPowerCoeff (r + 1) (t + 1) : ℂ)) *
          ((C Complex.I : ℂ[X]) ^ t * (cotDerivPoly t).map Complex.ofRealHom)) * hI2 +
        (((C Complex.I : ℂ[X]) ^ t * (cotDerivPoly t).map Complex.ofRealHom)) * hC0
  exact mul_left_cancel₀ hne hmain

private theorem poly_id (n : ℕ) : polyEq n := by
  induction n using Nat.twoStepInduction with
  | zero => exact polyEq_zero
  | one => exact polyEq_one
  | more n ih0 ih1 =>
    have ih0' : polyEq ((n + 1) - 1) := by
      rw [Nat.add_sub_cancel]
      exact ih0
    have h := poly_step (n + 1) (by omega) ih0' ih1
    rw [show n + 1 + 1 = n + 2 by omega] at h
    exact h

end cotPowerDeriv

open Polynomial cotPowerDeriv in
/-- **Cotangent powers through cotangent derivatives.** Let $c_{r,j}$ be Girstmair's cotangent
power coefficients and $\cot^{(m)}$ the $m$-th derivative of the real cotangent function. For
every natural number $r \ge 1$ and every real number $x$ with $\sin x \ne 0$,
$$(i \cot x)^r = \frac{(-1)^r + 1}{2} + \sum_{j=1}^{r} c_{r,j} \, i^j \cot^{(j-1)}(x).$$

Source: Kurt Girstmair, *Cotangent Power Sums and Character Coordinates*, INTEGERS 25 (2025),
Article A63, Proposition 1 (`integers-2025-A63-prop-1`). -/
public theorem I_mul_cot_pow_eq_sum_iteratedDeriv_cot (r : ℕ) (hr : 1 ≤ r) (x : ℝ)
    (hx : Real.sin x ≠ 0) :
    (Complex.I * Real.cot x) ^ r = ((-1) ^ r + 1) / 2 +
      ∑ j ∈ Finset.Icc 1 r, (cotangentPowerCoeff r j : ℂ) * Complex.I ^ j *
        ((iteratedDeriv (j - 1) Real.cot x : ℝ) : ℂ) := by
  have _ := hr
  have hpoly := poly_id r
  simp only [polyEq] at hpoly
  have heval :=
    congrArg (fun p : ℂ[X] => p.eval ((Real.cot x : ℝ) : ℂ)) hpoly
  simp only [eval_pow, eval_mul, eval_add, eval_finsetSum, eval_C, eval_X] at heval
  have hbridge : ∀ j : ℕ, ((cotDerivPoly (j - 1)).map Complex.ofRealHom).eval
      ((Real.cot x : ℝ) : ℂ) = ((iteratedDeriv (j - 1) Real.cot x : ℝ) : ℂ) := by
    intro j
    rw [eval_map_cotDerivPoly, iteratedDeriv_cot _ _ hx]
  simp only [hbridge] at heval
  exact heval

end MetaMathlibExt
