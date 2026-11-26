/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DiophantineApproximation.DistRoundPowFourierExpansion
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

open Filter

-- The mean value: for `k = 2` the zeroth Fourier coefficient is `1 / 12`.
example : (∫ u in (0 : ℝ)..1, ((|u - round u| ^ 2 : ℝ) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((0 : ℤ) : ℂ) * (u : ℂ)))) = (1 / 12 : ℂ) := by
  have h0 := (MetaMathlibExt.dist_round_pow_fourier_expansion 2 (by norm_num)).1
  have hreal : (1 : ℝ) / (2 ^ 2 * (((2 : ℕ) : ℝ) + 1)) = 1 / 12 := by norm_num
  have hval : ((1 / (2 ^ 2 * (((2 : ℕ) : ℝ) + 1)) : ℝ) : ℂ) = (1 / 12 : ℂ) := by
    rw [hreal]
    norm_num
  rw [hval] at h0
  exact h0

-- The coefficient bound is available with the statement exactly as written.
example : (let g : ℝ → ℝ := fun u => |u - round u| ^ 1
    let c : ℤ → ℂ := fun m => ∫ u in (0 : ℝ)..1,
      (g u : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (u : ℂ)))
    ∃ C : ℝ, ∀ m : ℤ, m ≠ 0 → ‖c m‖ ≤ C / (m : ℝ) ^ 2) :=
  (MetaMathlibExt.dist_round_pow_fourier_expansion 1 (by norm_num)).2.1

/-- `∫ x e^{cx}` by its antiderivative `e^{cx} (x / c - 1 / c ^ 2)`. -/
private lemma integral_ofReal_mul_exp {c : ℂ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ x in a..b, (x : ℂ) * Complex.exp (c * x) =
      Complex.exp (c * b) * (b / c - 1 / c ^ 2) - Complex.exp (c * a) * (a / c - 1 / c ^ 2) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Complex.exp (c * x) * (x / c - 1 / c ^ 2)) (fun x _ => ?_)
    ((by fun_prop : Continuous fun x : ℝ => (x : ℂ) * Complex.exp (c * x)).intervalIntegrable _ _)
  have hE : HasDerivAt (fun y : ℝ => Complex.exp (c * y)) (Complex.exp (c * x) * c) x := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul c).cexp.comp_ofReal
  have hL : HasDerivAt (fun y : ℝ => (y : ℂ) / c - 1 / c ^ 2) (1 / c) x := by
    simpa using ((hasDerivAt_id x).ofReal_comp.div_const c).sub_const (1 / c ^ 2)
  convert hE.mul hL using 1
  field_simp
  ring

-- A concrete coefficient: for `k = 1` the coefficient at `m = 1` is `-1 / π ^ 2`, which checks
-- the `2π` frequency normalization of the coefficients in the statement.
example : (∫ u in (0 : ℝ)..1, ((|u - round u| ^ 1 : ℝ) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (u : ℂ)))) =
    -(1 / (Real.pi : ℂ) ^ 2) := by
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = -(2 * Real.pi * Complex.I) := ⟨_, rfl⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc : c ≠ 0 := by simp [hcdef, Real.pi_ne_zero, Complex.I_ne_zero]
  have hexp : ∀ u : ℝ, Complex.exp (-(2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (u : ℂ))) =
      Complex.exp (c * u) := by
    intro u
    rw [hcdef]
    push_cast
    ring_nf
  have hd : Continuous fun u : ℝ => |u - round u| := by
    have h : (fun u : ℝ => |u - round u|) = (fun t : ℝ => min t (1 - t)) ∘ Int.fract := by
      funext u
      simp only [Function.comp_apply, abs_sub_round_eq_min]
    rw [h]
    exact ContinuousOn.comp_fract''
      (by fun_prop : Continuous fun t : ℝ => min t (1 - t)).continuousOn (by simp)
  have hf : Continuous fun u : ℝ => ((|u - round u| ^ 1 : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (u : ℂ))) := by
    fun_prop
  have hg1 : ∀ x ∈ Set.uIcc (0 : ℝ) (1 / 2), |x - round x| = x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rw [abs_sub_round_eq_min, Int.fract_eq_self.mpr ⟨hx.1, by linarith [hx.2]⟩]
    exact min_eq_left (by linarith [hx.2])
  have hg2 : ∀ x ∈ Set.uIcc (1 / 2 : ℝ) 1, |x - round x| = 1 - x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    rcases hx.2.lt_or_eq with hlt | rfl
    · rw [abs_sub_round_eq_min, Int.fract_eq_self.mpr ⟨by linarith [hx.1], hlt⟩]
      exact min_eq_right (by linarith [hx.1])
    · simp
  have hE : Continuous fun u : ℝ => Complex.exp (c * u) := by fun_prop
  have hXE : Continuous fun u : ℝ => (u : ℂ) * Complex.exp (c * u) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  have h1 : (∫ u in (0 : ℝ)..(1 / 2), ((|u - round u| ^ 1 : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (u : ℂ)))) =
      ∫ u in (0 : ℝ)..(1 / 2), (u : ℂ) * Complex.exp (c * u) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    simp only [pow_one, hg1 x hx, hexp]
  have h2 : (∫ u in (1 / 2 : ℝ)..1, ((|u - round u| ^ 1 : ℝ) : ℂ) *
      Complex.exp (-(2 * Real.pi * Complex.I * ((1 : ℤ) : ℂ) * (u : ℂ)))) =
      (∫ u in (1 / 2 : ℝ)..1, Complex.exp (c * u)) -
        ∫ u in (1 / 2 : ℝ)..1, (u : ℂ) * Complex.exp (c * u) := by
    rw [← intervalIntegral.integral_sub (hE.intervalIntegrable _ _) (hXE.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr fun x hx => ?_
    simp only [pow_one, hg2 x hx, hexp]
    push_cast
    ring
  rw [h1, h2, integral_ofReal_mul_exp hc, integral_ofReal_mul_exp hc, integral_exp_mul_complex hc]
  have eh : Complex.exp (c * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [hcdef, show -(2 * (Real.pi : ℂ) * Complex.I) * ((1 / 2 : ℝ) : ℂ) =
      -((Real.pi : ℂ) * Complex.I) by push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have e1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
    rw [hcdef, Complex.ofReal_one, mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one]
  have e0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by simp
  have hc2 : c ^ 2 = -(4 * (Real.pi : ℂ) ^ 2) := by
    rw [hcdef]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [eh, e1, e0]
  calc _ = 4 / c ^ 2 := by
        push_cast
        field_simp
        ring
    _ = -(1 / (Real.pi : ℂ) ^ 2) := by
        rw [hc2]
        field_simp
