/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import MathlibExt.NumberTheory.Recurrences.KJacobsthal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.LucasBinetFormula

/-!
# Integral representations of even- and odd-indexed k-Jacobsthal numbers

We prove the integral representations of the even- and odd-indexed $k$-Jacobsthal numbers
over $[-1, 1]$, evaluating the integrals with the Binet formula for the Lucas sequences with
parameters $(k, -2)$.
-/

namespace MetaMathlibExt

local notation "Δ[" k "]" => Real.sqrt ((k : ℝ) ^ 2 + 8)

-- The primitive is `(A + B * x) ^ (m + 1) / (B * (m + 1))`.
private theorem lucasU_kJacobsthal_even_odd_eq_integral.integral_even (A B : ℝ)
    (hB : B ≠ 0) (m : ℕ) :
    (∫ x in (-1 : ℝ)..1, (A + B * x) ^ m) =
      ((A + B) ^ (m + 1) - (A - B) ^ (m + 1)) / (B * (m + 1 : ℝ)) := by
  let F := fun x : ℝ => (A + B * x) ^ (m + 1) / (B * (m + 1 : ℝ))
  have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
  calc
    _ = F 1 - F (-1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        have hlin (u v : ℝ) : HasDerivAt (fun y => u + v * y) v x := by
          simpa using ((hasDerivAt_id x).const_mul v).const_add u
        have hder := (hlin A B).fun_pow (m + 1)
        have hder2 := hder.div_const (B * (m + 1 : ℝ))
        convert hder2 using 1
        simp only [Nat.add_sub_cancel]
        field_simp
        push_cast
        ring
      · apply Continuous.intervalIntegrable
        fun_prop
    _ = _ := by
      simp only [F, mul_one, mul_neg]
      rw [show A + -B = A - B by ring]
      ring

-- The primitive is `(p + x) * (A + B * x) ^ (m + 1)`.
private theorem lucasU_kJacobsthal_even_odd_eq_integral.integral_odd (A B p : ℝ)
    (m : ℕ) :
    (∫ x in (-1 : ℝ)..1, (A + (m + 1 : ℝ) * B * p + (m + 2 : ℝ) * B * x) *
        (A + B * x) ^ m) =
      (p + 1) * (A + B) ^ (m + 1) - (p - 1) * (A - B) ^ (m + 1) := by
  let F := fun x : ℝ => (p + 1 * x) * (A + B * x) ^ (m + 1)
  calc
    _ = F 1 - F (-1) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x _
        have hlin (u v : ℝ) : HasDerivAt (fun y => u + v * y) v x := by
          simpa using ((hasDerivAt_id x).const_mul v).const_add u
        have hder := ((hlin p 1).fun_mul ((hlin A B).fun_pow (m + 1)))
        convert hder using 1
        simp only [Nat.add_sub_cancel, pow_succ]
        push_cast
        ring
      · apply Continuous.intervalIntegrable
        fun_prop
    _ = _ := by
      simp only [F, mul_one, mul_neg]
      rw [show A + -B = A - B by ring]
      ring_nf

/-- **Integral representation of even- and odd-indexed k-Jacobsthal numbers.** Let $k$ and $n$
be natural numbers, let $J_{k,n} = U_n(k, -2)$ be the $k$-Jacobsthal numbers and let
$\Delta_k = \sqrt{k^2 + 8}$. Then
$$J_{k,2n} = \frac{kn}{2^n} \int_{-1}^{1} (k^2 + 4 + k \Delta_k x)^{n-1} \, dx$$
and
$$J_{k,2n+1} = \frac{1}{2^{n+1}} \int_{-1}^{1} (nk^2 + k^2 + 4 + k(n+1) \Delta_k x)
(k^2 + 4 + k \Delta_k x)^{n-1} \, dx.$$
Here $n - 1$ is an integer exponent, so for $n = 0$ the power is a reciprocal.

Source: Weerayuth Nilsrakoo and Achariya Nilsrakoo, *An Integral Representation of k-Jacobsthal and
k-Jacobsthal-Lucas Numbers*, INTEGERS 25 (2025), Article A74,
Theorem 2 (`integers-2025-A74-thm-2`). -/
public theorem lucasU_kJacobsthal_even_odd_eq_integral (k n : ℕ) :
    (lucasU (kJacobsthalParams k) (2 * n) : ℝ) =
        k * n / 2 ^ n * ∫ x in (-1 : ℝ)..1, ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1) ∧
      (lucasU (kJacobsthalParams k) (2 * n + 1) : ℝ) =
        1 / 2 ^ (n + 1) * ∫ x in (-1 : ℝ)..1,
          (n * (k : ℝ) ^ 2 + k ^ 2 + 4 + k * (n + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ ((n : ℤ) - 1) := by
  have hΔsq : Δ[k] ^ 2 = (k : ℝ) ^ 2 + 8 := Real.sq_sqrt (by positivity)
  have hΔpos : 0 < Δ[k] := Real.sqrt_pos.2 (by positivity)
  have hΔne : Δ[k] ≠ 0 := hΔpos.ne'
  set α : ℝ := ((k : ℝ) + Δ[k]) / 2 with hαdef
  set β : ℝ := ((k : ℝ) - Δ[k]) / 2 with hβdef
  have hsum : α + β = ((kJacobsthalParams k).p : ℝ) := by
    rw [hαdef, hβdef]; simp [kJacobsthalParams]; ring
  have hprod : α * β = ((kJacobsthalParams k).q : ℝ) := by
    rw [hαdef, hβdef]; simp [kJacobsthalParams]
    nlinarith [hΔsq]
  have hsub : α - β = Δ[k] := by rw [hαdef, hβdef]; ring
  have hne : α ≠ β := by
    intro h; rw [h, sub_self] at hsub; exact hΔne hsub.symm
  have hbinet := (lucas_binet_formulas_of_field (kJacobsthalParams k) α β hsum hprod).1 hne
  have hAplus : (k : ℝ) ^ 2 + 4 + (k : ℝ) * Δ[k] = 2 * α ^ 2 := by
    rw [hαdef]; nlinarith [hΔsq]
  have hAminus : (k : ℝ) ^ 2 + 4 - (k : ℝ) * Δ[k] = 2 * β ^ 2 := by
    rw [hβdef]; nlinarith [hΔsq]
  have hp1 : (k : ℝ) / Δ[k] + 1 = 2 * α / Δ[k] := by
    rw [hαdef]; field_simp
  have hpm1 : (k : ℝ) / Δ[k] - 1 = 2 * β / Δ[k] := by
    rw [hβdef]; field_simp
  constructor
  · cases n with
    | zero => simp [lucasU]
    | succ m =>
      by_cases hk0 : k = 0
      · subst hk0
        have hzero : ∀ m : ℕ, lucasU (kJacobsthalParams 0) (2 * m) = 0 := by
          intro m
          induction m with
          | zero => simp [lucasU]
          | succ m ih =>
            have h2 : 2 * (m + 1) = 2 * m + 2 := by ring
            rw [h2, lucasU_add_two, ih]
            simp [kJacobsthalParams]
        rw [hzero (m + 1)]
        simp
      · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
        have hB : (k : ℝ) * Δ[k] ≠ 0 := mul_ne_zero hkpos.ne' hΔne
        have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        have hexp : (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) := by push_cast; ring
        simp only [hexp, zpow_natCast]
        rw [lucasU_kJacobsthal_even_odd_eq_integral.integral_even
          ((k : ℝ) ^ 2 + 4) ((k : ℝ) * Δ[k]) hB m, (hbinet (2 * (m + 1))).1, hsub]
        push_cast
        rw [hAplus, hAminus]
        field_simp
        ring_nf
  · cases n with
    | zero =>
      have hlt : (k : ℝ) * Δ[k] < (k : ℝ) ^ 2 + 4 := by
        by_cases hk0 : k = 0
        · subst hk0; simp
        · have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk0
          have h1 : Δ[k] < ((k : ℝ) ^ 2 + 4) / (k : ℝ) := by
            rw [Real.sqrt_lt' (by positivity)]
            rw [div_pow]
            rw [lt_div_iff₀ (by positivity : (0:ℝ) < (k:ℝ) ^ 2)]
            nlinarith [hΔsq]
          calc (k : ℝ) * Δ[k] < (k : ℝ) * (((k : ℝ) ^ 2 + 4) / (k : ℝ)) :=
                mul_lt_mul_of_pos_left h1 hkpos
            _ = (k : ℝ) ^ 2 + 4 := by field_simp
      have hpos : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, 0 < (k : ℝ) ^ 2 + 4 + (k : ℝ) * Δ[k] * x := by
        intro x hx
        rw [Set.mem_uIcc] at hx
        have hxabs : |x| ≤ 1 := by
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact abs_le.mpr ⟨by linarith, by linarith⟩
        have hle : |(k : ℝ) * Δ[k] * x| ≤ (k : ℝ) * Δ[k] := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ) * Δ[k])]
          calc (k : ℝ) * Δ[k] * |x| ≤ (k : ℝ) * Δ[k] * 1 := by
                apply mul_le_mul_of_nonneg_left hxabs (by positivity)
            _ = (k : ℝ) * Δ[k] := mul_one _
        have hge : -((k : ℝ) * Δ[k]) ≤ (k : ℝ) * Δ[k] * x := by
          have := neg_abs_le ((k : ℝ) * Δ[k] * x)
          linarith [hle]
        nlinarith [hlt]
      have hcongr : ∀ x ∈ Set.uIcc (-1 : ℝ) 1,
          ((0 : ℕ) * (k : ℝ) ^ 2 + k ^ 2 + 4 + k * ((0 : ℕ) + 1) * Δ[k] * x) *
            ((k : ℝ) ^ 2 + 4 + k * Δ[k] * x) ^ (((0 : ℕ) : ℤ) - 1) = 1 := by
        intro x hx
        have hne' : (k : ℝ) ^ 2 + 4 + (k : ℝ) * Δ[k] * x ≠ 0 := (hpos x hx).ne'
        have heq : (0 : ℕ) * (k : ℝ) ^ 2 + k ^ 2 + 4 + k * ((0 : ℕ) + 1) * Δ[k] * x =
            (k : ℝ) ^ 2 + 4 + (k : ℝ) * Δ[k] * x := by push_cast; ring
        rw [heq]
        simp only [Nat.cast_zero, zero_sub, zpow_neg_one]
        exact mul_inv_cancel₀ hne'
      rw [show ((lucasU (kJacobsthalParams k) (2 * 0 + 1) : ℤ) : ℝ) = 1 by simp [lucasU]]
      rw [intervalIntegral.integral_congr hcongr]
      norm_num [intervalIntegral.integral_const]
    | succ m =>
      have hexp : (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) := by push_cast; ring
      have hfun : (fun x : ℝ => (↑(m + 1) * (k : ℝ) ^ 2 + (k : ℝ) ^ 2 + 4 +
              (k : ℝ) * (↑(m + 1) + 1) * Δ[k] * x) *
          ((k : ℝ) ^ 2 + 4 + (k : ℝ) * Δ[k] * x) ^ (((m + 1 : ℕ) : ℤ) - 1)) =
          (fun x : ℝ => ((k : ℝ) ^ 2 + 4 + (↑m + 1) * ((k : ℝ) * Δ[k]) * ((k : ℝ) / Δ[k]) +
              (↑m + 2) * ((k : ℝ) * Δ[k]) * x) * ((k : ℝ) ^ 2 + 4 + (k : ℝ) * Δ[k] * x) ^ m) := by
        funext x
        rw [hexp, zpow_natCast]
        congr 1
        field_simp
        push_cast
        ring
      rw [hfun, lucasU_kJacobsthal_even_odd_eq_integral.integral_odd
        ((k : ℝ) ^ 2 + 4) ((k : ℝ) * Δ[k]) ((k : ℝ) / Δ[k]) m,
        (hbinet (2 * (m + 1) + 1)).1, hsub, hAplus, hAminus, hp1, hpm1]
      field_simp
      ring_nf

end MetaMathlibExt

