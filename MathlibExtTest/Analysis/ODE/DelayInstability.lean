/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.DelayInstability
import MathlibExt.Biology.Dynamics.DelayedLogistic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Tests for linearized instability of delay differential equations.

* Characteristic roots with a genuine delay, checked from the definitions of `pointDelay` and
  the exponential segments: `r = 1` for `x'(t) = e x(t - 1)`, and the complex root
  `κ = 1 + i` for `x'(t) = κ e^κ x(t - 1)`.
* Real coefficients, genuine delay, complex unstable root: for Hutchinson's linearization
  `u'(t) = -r u(t - τ)` beyond the critical delay, the root with positive real part from
  `DelayedLogistic.exists_charFun_eq_zero_re_pos` is a characteristic root of the
  point-delay functional.
* Boundary of the hypothesis `Re κ > 0`: `κ = i` is a characteristic root of
  `x'(t) = -x(t - π/2)` (Hutchinson's equation on its stability boundary `bτ = π/2`), and the
  corresponding time-`T` eigenvalue `e^{iT}` has modulus `1`, so no instability theorem
  applies.
* Boundary of `exists_pos_root_of_add_pos`: for `a = -1`, `b = 1` (`a + b = 0`), `τ = 1`, the
  equation `r = a + b e^{-τr}` has no root `r > 0`.
* Non-vacuity of the instability theorems on the delay phase space `C([-1, 0], ℝ)` and
  `C([-1, 0], ℂ)`: for `x'(t) = x(t)` with history interval `[-1, 0]`, the time-`1` solution map
  is `ψ ↦ (θ ↦ e^{1+θ} ψ(0))`. This is proved from the definition of `IsTimeMap` by uniqueness
  for `x' = x` on `[0, ∞)`, and all hypotheses of `exists_escape_of_realCharRoot` and
  `exists_escape_of_charRoot` hold with the characteristic root `1`, `p = 2`, `μ = e`, zero
  remainder and the flow sampled at integer times.
* `exists_timeMap_eigen_of_add_pos` applied to `x'(t) = x(t - 1)`. -/

namespace MathlibExtTest.Analysis.ODE.DelayInstability

open Set MathlibExt.Analysis.ODE.DelayInstability

/-! ### Characteristic roots with a genuine delay -/

/-- `r = 1` is a characteristic root of `x'(t) = e x(t - 1)`: `0 + e · e^{-1} = 1`. -/
example : pointDelay zero_le_one (0 : ℝ →L[ℝ] ℝ) (Real.exp 1 • ContinuousLinearMap.id ℝ ℝ)
    (realExpSegment 1 1 1) = (1 : ℝ) • (1 : ℝ) := by
  rw [pointDelay_apply]
  simp only [realExpSegment_apply, zero_apply, zero_add,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one]
  rw [← Real.exp_add]
  norm_num

/-- `κ = 1 + i` is a characteristic root of `x'(t) = κ e^κ x(t - 1)`. -/
example : pointDelay zero_le_one (0 : ℂ →L[ℂ] ℂ)
    (((1 + Complex.I) * Complex.exp (1 + Complex.I)) • ContinuousLinearMap.id ℂ ℂ)
    (expSegment 1 (1 + Complex.I) 1) = (1 + Complex.I) • (1 : ℂ) := by
  rw [pointDelay_apply]
  simp only [expSegment_apply, zero_apply, zero_add,
    smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one, Complex.ofReal_neg, Complex.ofReal_one]
  rw [mul_assoc, ← Complex.exp_add]
  ring_nf
  simp
  ring

open MathlibExt.Biology.Dynamics.DelayedLogistic in
/-- Hutchinson's linearization `u'(t) = -r u(t - τ)` with `τ > π / (2r)`: a root of
`DelayedLogistic.charFun` with positive real part is a characteristic root of
`pointDelay hτ 0 (-r)`, i.e. it supplies the spectral hypothesis of
`exists_escape_of_charRoot`. -/
theorem hutchinson_unstable_charRoot {r τ : ℝ} (hr : 0 < r) (hτc : criticalDelay r < τ)
    (hτ : 0 ≤ τ) : ∃ κ : ℂ, 0 < κ.re ∧
      pointDelay hτ (0 : ℂ →L[ℂ] ℂ) (-(r : ℂ) • ContinuousLinearMap.id ℂ ℂ)
        (expSegment τ κ 1) = κ • (1 : ℂ) := by
  obtain ⟨z, hz, hre, -⟩ := exists_charFun_eq_zero_re_pos hr hτc
  refine ⟨z, hre, ?_⟩
  rw [pointDelay_expSegment, show -(τ : ℂ) * z = -(z * τ) by ring]
  simp only [charFun] at hz
  simp only [zero_apply, zero_add, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    mul_one]
  linear_combination -hz

/-! ### Boundary: a characteristic root on the imaginary axis -/

/-- `κ = i` is a characteristic root of `x'(t) = -x(t - π/2)`. -/
theorem hutchinson_boundary_root :
    pointDelay (by positivity : (0 : ℝ) ≤ Real.pi / 2) (0 : ℂ →L[ℂ] ℂ)
      (-ContinuousLinearMap.id ℂ ℂ) (expSegment (Real.pi / 2) Complex.I 1) =
      Complex.I • (1 : ℂ) := by
  rw [pointDelay_apply]
  simp only [expSegment_apply, zero_apply, zero_add,
    neg_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
  rw [Complex.ofReal_neg, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- The boundary root violates `0 < Re κ`, and its time-`T` eigenvalue lies on the unit
circle. -/
example (T : ℝ) : ¬ 0 < Complex.I.re ∧ ‖Complex.exp (T * Complex.I)‖ = 1 := by
  refine ⟨by simp, ?_⟩
  rw [norm_exp_mul]
  simp

/-! ### Boundary: `a + b = 0` -/

/-- With `a = -1`, `b = 1`, `τ = 1` the scalar characteristic equation has no positive root. -/
example : ¬ ∃ r > 0, r = -1 + 1 * Real.exp (-1 * r) := by
  rintro ⟨r, hr, hroot⟩
  have : Real.exp (-1 * r) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

/-! ### Non-vacuity: `x'(t) = x(t)` on the history space `C([-1, 0], ·)` -/

/-- The right endpoint `0` of `[-1, 0]`. -/
def z0 : Icc (-1 : ℝ) 0 := ⟨0, right_mem_Icc.2 (by norm_num)⟩

/-- Uniqueness for `x' = x` on `[0, ∞)`: `x(s) = eˢ x(0)` for `s ≥ 0`. -/
theorem eq_exp_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {x : C(ℝ, F)}
    (hx : ∀ t, 0 ≤ t → HasDerivAt x (x t) t) {s : ℝ} (hs : 0 ≤ s) :
    x s = Real.exp s • x 0 := by
  have hy : ∀ t, 0 ≤ t → HasDerivAt (fun t => Real.exp (-t) • x t) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
      simpa using (hasDerivAt_neg t).exp
    convert h1.smul (hx t ht) using 1
    simp [neg_smul]
  have hconst := constant_of_has_deriv_right_zero (f := fun t => Real.exp (-t) • x t)
    (a := 0) (b := s) (by fun_prop) (fun t ht => (hy t ht.1).hasDerivWithinAt) s ⟨hs, le_rfl⟩
  simp only [neg_zero, Real.exp_zero, one_smul] at hconst
  rw [← hconst, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- The time-`1` map of `x'(t) = x(t)` on `C([-1, 0], ℝ)`: `ψ ↦ ψ(0) e^{1+θ}`. -/
noncomputable def Lr : C(Icc (-1 : ℝ) 0, ℝ) →L[ℝ] C(Icc (-1 : ℝ) 0, ℝ) :=
  (ContinuousMap.evalCLM (R := ℝ) z0).smulRight (Real.exp 1 • realExpSegment 1 1 (1 : ℝ))

theorem Lr_apply (ψ : C(Icc (-1 : ℝ) 0, ℝ)) (θ : Icc (-1 : ℝ) 0) :
    Lr ψ θ = ψ z0 * (Real.exp 1 * Real.exp θ) := by
  simp [Lr]

theorem isTimeMap_Lr :
    IsTimeMap 1 (pointDelay zero_le_one (ContinuousLinearMap.id ℝ ℝ) 0) 1 Lr := by
  intro x hx
  have hx' : ∀ t, 0 ≤ t → HasDerivAt x (x t) t := fun t ht => by
    simpa [pointDelay_apply] using hx t ht
  ext θ
  rw [Lr_apply, segment_apply, segment_apply, eq_exp_smul hx' (s := 1 + θ) (by linarith [θ.2.1]),
    smul_eq_mul, ← Real.exp_add]
  simp [z0, mul_comm]

theorem norm_Lr_le : ‖Lr‖ ≤ Real.exp 1 := by
  have he : ‖ContinuousMap.evalCLM (R := ℝ) (M := ℝ) z0‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
      simpa using f.norm_coe_le_norm z0
  have hg : ‖Real.exp 1 • realExpSegment 1 1 (1 : ℝ)‖ ≤ Real.exp 1 := by
    refine (ContinuousMap.norm_le _ (Real.exp_pos 1).le).2 fun θ => ?_
    simp only [ContinuousMap.smul_apply, realExpSegment_apply, smul_eq_mul, mul_one,
      Real.norm_eq_abs, abs_mul, Real.abs_exp]
    exact mul_le_of_le_one_right (Real.exp_pos 1).le (Real.exp_le_one_iff.2 θ.2.2)
  rw [Lr, ContinuousLinearMap.norm_smulRight_apply]
  calc _ ≤ 1 * Real.exp 1 := mul_le_mul he hg (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_Lr_pow_le (n : ℕ) : ‖Lr ^ n‖ ≤ 1 * Real.exp 1 ^ n := by
  rw [one_mul]
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  · exact (norm_pow_le' Lr hn).trans (by gcongr; exact norm_Lr_le)

/-- The flow of the linear equation sampled at integer times, `Φ t = L^⌊t⌋`. -/
theorem iterate_floor_step {X : Type*} (L : X → X) (n : ℕ) (x : X) :
    L^[⌊((n : ℝ) + 1) * 1⌋₊] x = L^[⌊(1 : ℝ)⌋₊] (L^[⌊(n : ℝ) * 1⌋₊] x) := by
  rw [mul_one, mul_one, show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
    Nat.floor_natCast, Nat.floor_natCast, Nat.floor_one, Function.iterate_one,
    Function.iterate_succ_apply']

/-- All hypotheses of `exists_escape_of_realCharRoot` hold for `x'(t) = x(t)` on
`C([-1, 0], ℝ)` with the characteristic root `r = 1`. -/
theorem escape_real_instance : ∃ ε > 0, ∀ δ > 0, ∃ x : C(Icc (-1 : ℝ) 0, ℝ), ‖x - 0‖ < δ ∧
    ∃ t : ℝ, 0 ≤ t ∧ ε ≤ ‖Lr^[⌊t⌋₊] x - 0‖ :=
  exists_escape_of_realCharRoot (Λ := pointDelay zero_le_one (ContinuousLinearMap.id ℝ ℝ) 0)
    (L := Lr) (u₀ := 0) (Φ := fun t x => Lr^[⌊t⌋₊] x) (T := 1) (ρ := 1) (C := 0) (p := 2) (M := 1)
    (μ := Real.exp 1) (r := 1) (v := (1 : ℝ)) zero_le_one one_pos one_pos le_rfl one_lt_two
    (fun x => by simp) (fun n x _ => iterate_floor_step Lr n x) (fun y _ => by simp)
    isTimeMap_Lr one_ne_zero (by simp [pointDelay_apply]) one_pos (Real.exp_pos 1).le
    (by rw [Real.exp_lt_exp]; norm_num) norm_Lr_pow_le

/-- The time-`1` map of `x'(t) = x(t)` on `C([-1, 0], ℂ)`. -/
noncomputable def Lc : C(Icc (-1 : ℝ) 0, ℂ) →L[ℂ] C(Icc (-1 : ℝ) 0, ℂ) :=
  (ContinuousMap.evalCLM (R := ℂ) z0).smulRight (Complex.exp 1 • expSegment 1 1 (1 : ℂ))

theorem Lc_apply (ψ : C(Icc (-1 : ℝ) 0, ℂ)) (θ : Icc (-1 : ℝ) 0) :
    Lc ψ θ = ψ z0 * (Complex.exp 1 * Complex.exp θ) := by
  simp [Lc]

theorem isTimeMap_Lc :
    IsTimeMap 1 (pointDelay zero_le_one (ContinuousLinearMap.id ℂ ℂ) 0) 1 Lc := by
  intro x hx
  have hx' : ∀ t, 0 ≤ t → HasDerivAt x (x t) t := fun t ht => by
    simpa [pointDelay_apply] using hx t ht
  ext θ
  rw [Lc_apply, segment_apply, segment_apply, eq_exp_smul hx' (s := 1 + θ) (by linarith [θ.2.1]),
    Complex.real_smul, ← Complex.exp_add, Complex.ofReal_exp]
  simp [z0, mul_comm]

theorem norm_Lc_le : ‖Lc‖ ≤ Real.exp 1 := by
  have he : ‖ContinuousMap.evalCLM (R := ℂ) (M := ℂ) z0‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
      simpa using f.norm_coe_le_norm z0
  have hg : ‖Complex.exp 1 • expSegment 1 1 (1 : ℂ)‖ ≤ Real.exp 1 := by
    refine (ContinuousMap.norm_le _ (Real.exp_pos 1).le).2 fun θ => ?_
    simp only [ContinuousMap.smul_apply, expSegment_apply, smul_eq_mul, mul_one, norm_mul,
      Complex.norm_exp, Complex.one_re, Complex.ofReal_re]
    exact mul_le_of_le_one_right (Real.exp_pos 1).le (Real.exp_le_one_iff.2 θ.2.2)
  rw [Lc, ContinuousLinearMap.norm_smulRight_apply]
  calc _ ≤ 1 * Real.exp 1 := mul_le_mul he hg (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem norm_Lc_pow_le (n : ℕ) : ‖Lc ^ n‖ ≤ 1 * Real.exp 1 ^ n := by
  rw [one_mul]
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [pow_zero, pow_zero]; exact ContinuousLinearMap.norm_id_le
  · exact (norm_pow_le' Lc hn).trans (by gcongr; exact norm_Lc_le)

/-- All hypotheses of `exists_escape_of_charRoot` hold for `x'(t) = x(t)` on
`C([-1, 0], ℂ)` with the characteristic root `κ = 1`. -/
theorem escape_complex_instance : ∃ ε > 0, ∀ δ > 0, ∃ x : C(Icc (-1 : ℝ) 0, ℂ), ‖x - 0‖ < δ ∧
    ∃ t : ℝ, 0 ≤ t ∧ ε ≤ ‖Lc^[⌊t⌋₊] x - 0‖ :=
  exists_escape_of_charRoot (Λ := pointDelay zero_le_one (ContinuousLinearMap.id ℂ ℂ) 0)
    (L := Lc) (u₀ := 0) (Φ := fun t x => Lc^[⌊t⌋₊] x) (T := 1) (ρ := 1) (C := 0) (p := 2) (M := 1)
    (μ := Real.exp 1) (κ := 1) (v := (1 : ℂ)) zero_le_one one_pos one_pos le_rfl one_lt_two
    (fun x => by simp) (fun n x _ => iterate_floor_step Lc n x) (fun y _ => by simp)
    isTimeMap_Lc one_ne_zero (by simp [pointDelay_apply]) (by simp) (Real.exp_pos 1).le
    (by rw [Complex.one_re, Real.exp_lt_exp]; norm_num) norm_Lc_pow_le

/-! ### Scalar equation with `a + b > 0` -/

/-- `x'(t) = x(t - 1)` (`a = 0`, `b = 1`): some `r > 0` gives an eigenvalue `e^{Tr} > 1` of
every time-`T` map with `T > 0`. -/
example : ∃ r > 0, ∀ (T : ℝ) (L : C(Icc (-1 : ℝ) 0, ℝ) → C(Icc (-1 : ℝ) 0, ℝ)),
    IsTimeMap 1 (pointDelay zero_le_one ((0 : ℝ) • ContinuousLinearMap.id ℝ ℝ)
      ((1 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) T L →
      L (realExpSegment 1 r 1) = Real.exp (T * r) • realExpSegment 1 r 1 :=
  exists_timeMap_eigen_of_add_pos zero_le_one (by norm_num)

end MathlibExtTest.Analysis.ODE.DelayInstability
