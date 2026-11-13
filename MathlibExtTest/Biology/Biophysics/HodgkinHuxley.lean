/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.HodgkinHuxley
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Tests for the Hodgkin–Huxley equations: the squid-axon resting state computed from the rate
functions (steady states, leak reversal potential, equilibrium), a voltage-clamp solution whose
gating variable stays in `[0, 1]` by direct computation, and a depolarized initial state that
stays in the trapping box `[-12, 115] × [0, 1]³`. -/

open Real Set

namespace MathlibExtTest.Biology.Biophysics.HodgkinHuxley

open MathlibExt.Biology.Biophysics.HodgkinHuxley

/-! ### Numerical enclosures of `e`, `e^{5/2}`, `e³` -/

private theorem e_bounds : 27182818 / 10000000 < exp 1 ∧ exp 1 < 27182819 / 10000000 :=
  ⟨lt_trans (by norm_num) exp_one_gt_d9, lt_trans exp_one_lt_d9 (by norm_num)⟩

private theorem y_bounds : 12182 / 1000 < exp (5 / 2) ∧ exp (5 / 2) < 12183 / 1000 := by
  obtain ⟨h1, h2⟩ := e_bounds
  set q := exp (1 / 2) with hq
  have hq2 : q * q = exp 1 := by rw [hq, ← exp_add]; norm_num
  have hqpos : 0 < q := exp_pos _
  have hql : 164872 / 100000 < q := by nlinarith
  have hqu : q < 164873 / 100000 := by nlinarith
  have hy : exp (5 / 2) = exp 1 * exp 1 * q := by rw [hq, ← exp_add, ← exp_add]; norm_num
  have hee : exp 1 * exp 1 < 27182819 / 10000000 * (27182819 / 10000000) :=
    mul_lt_mul'' h2 h2 (exp_pos 1).le (exp_pos 1).le
  have hee' : 27182818 / 10000000 * (27182818 / 10000000) < exp 1 * exp 1 :=
    mul_lt_mul'' h1 h1 (by norm_num) (by norm_num)
  rw [hy]
  constructor <;> nlinarith [mul_pos (exp_pos 1) (exp_pos 1)]

private theorem z_bounds : 2008 / 100 < exp 3 ∧ exp 3 < 2009 / 100 := by
  obtain ⟨h1, h2⟩ := e_bounds
  have hz : exp 3 = exp 1 * exp 1 * exp 1 := by rw [← exp_add, ← exp_add]; norm_num
  have hee : exp 1 * exp 1 < 27182819 / 10000000 * (27182819 / 10000000) :=
    mul_lt_mul'' h2 h2 (exp_pos 1).le (exp_pos 1).le
  have hee' : 27182818 / 10000000 * (27182818 / 10000000) < exp 1 * exp 1 :=
    mul_lt_mul'' h1 h1 (by norm_num) (by norm_num)
  rw [hz]
  constructor <;> nlinarith [mul_pos (exp_pos 1) (exp_pos 1)]

/-! ### Squid giant axon: resting state from the rate functions -/

/-- Rates at rest, from the definitions: `α_m(0) = 2.5 / (e^{2.5} - 1)`, `β_m(0) = 4`,
`α_h(0) = 0.07`, `β_h(0) = 1 / (e³ + 1)`, `α_n(0) = 0.1 / (e - 1)`, `β_n(0) = 0.125`. -/
example : alphaM 0 = 5 / 2 / (exp (5 / 2) - 1) := by
  simp only [alphaM, vtrap]; norm_num
example : betaM 0 = 4 := by simp [betaM]
example : alphaH 0 = 7 / 100 := by simp [alphaH]
example : betaH 0 = 1 / (exp 3 + 1) := by norm_num [betaH]
example : alphaN 0 = 1 / 10 / (exp 1 - 1) := by
  simp only [alphaN, vtrap]; norm_num; ring
example : betaN 0 = 1 / 8 := by simp [betaN]

/-- `m∞(0) = α_m / (α_m + β_m) ∈ (0.0529, 0.0530)`. -/
theorem mRest_bounds : 529 / 10000 < mRest ∧ mRest < 530 / 10000 := by
  obtain ⟨h1, h2⟩ := y_bounds
  have hαe : alphaM 0 = 5 / 2 / (exp (5 / 2) - 1) := by simp only [alphaM, vtrap]; norm_num
  have hα1 : 2235 / 10000 < alphaM 0 := by
    rw [hαe, lt_div_iff₀ (by linarith)]; linarith
  have hα2 : alphaM 0 < 2236 / 10000 := by
    rw [hαe, div_lt_iff₀ (by linarith)]; linarith
  have hβ : betaM 0 = 4 := by simp [betaM]
  simp only [mRest, steady, hβ]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- `h∞(0) ∈ (0.596, 0.5963)`. -/
theorem hRest_bounds : 596 / 1000 < hRest ∧ hRest < 5963 / 10000 := by
  obtain ⟨h1, h2⟩ := z_bounds
  have hβe : betaH 0 = 1 / (exp 3 + 1) := by norm_num [betaH]
  have hβ1 : 4741 / 100000 < betaH 0 := by
    rw [hβe, lt_div_iff₀ (by linarith)]; linarith
  have hβ2 : betaH 0 < 4744 / 100000 := by
    rw [hβe, div_lt_iff₀ (by linarith)]; linarith
  have hα : alphaH 0 = 7 / 100 := by simp [alphaH]
  simp only [hRest, steady, hα]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- `n∞(0) ∈ (0.3176, 0.3178)`. -/
theorem nRest_bounds : 3176 / 10000 < nRest ∧ nRest < 3178 / 10000 := by
  obtain ⟨h1, h2⟩ := e_bounds
  have hαe : alphaN 0 = 1 / 10 / (exp 1 - 1) := by simp only [alphaN, vtrap]; norm_num; ring
  have hα1 : 58197 / 1000000 < alphaN 0 := by
    rw [hαe, lt_div_iff₀ (by linarith)]; linarith
  have hα2 : alphaN 0 < 58198 / 1000000 := by
    rw [hαe, div_lt_iff₀ (by linarith)]; linarith
  have hβ : betaN 0 = 1 / 8 := by simp [betaN]
  simp only [nRest, steady, hβ]
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- The leak reversal potential fixed by zero net current at rest is `10.5 < EL < 10.7`,
matching Hodgkin and Huxley's `10.613` mV. -/
theorem squidEL_bounds : 21 / 2 < squidEL ∧ squidEL < 107 / 10 := by
  obtain ⟨m1, m2⟩ := mRest_bounds
  obtain ⟨h1, h2⟩ := hRest_bounds
  obtain ⟨n1, n2⟩ := nRest_bounds
  have hn4l : (3176 / 10000 : ℝ) ^ 4 < nRest ^ 4 := pow_lt_pow_left₀ n1 (by norm_num) (by norm_num)
  have hn4u : nRest ^ 4 < (3178 / 10000 : ℝ) ^ 4 := pow_lt_pow_left₀ n2 (by linarith) (by norm_num)
  have hm3l : (529 / 10000 : ℝ) ^ 3 < mRest ^ 3 := pow_lt_pow_left₀ m1 (by norm_num) (by norm_num)
  have hm3u : mRest ^ 3 < (530 / 10000 : ℝ) ^ 3 := pow_lt_pow_left₀ m2 (by linarith) (by norm_num)
  have hmh_l : (529 / 10000 : ℝ) ^ 3 * (596 / 1000) < mRest ^ 3 * hRest :=
    mul_lt_mul'' hm3l h1 (by norm_num) (by norm_num)
  have hmh_u : mRest ^ 3 * hRest < (530 / 10000 : ℝ) ^ 3 * (5963 / 10000) :=
    mul_lt_mul'' hm3u h2 (by positivity) (by linarith)
  have hEL : squidEL = 1440 * nRest ^ 4 - 46000 * (mRest ^ 3 * hRest) := by
    simp only [squidEL]; ring
  rw [hEL]
  norm_num at hn4l hn4u hmh_l hmh_u ⊢
  constructor <;> linarith

/-- The resting state is an equilibrium, checked coordinatewise from the definitions of the
field, the gating kinetics and `squidEL` (not through `field_eq_zero_iff`). -/
example : field squid rest = 0 := by
  have hm : alphaM 0 + betaM 0 ≠ 0 := (add_pos (alphaM_pos 0) (betaM_pos 0)).ne'
  have hh : alphaH 0 + betaH 0 ≠ 0 := (add_pos (alphaH_pos 0) (betaH_pos 0)).ne'
  have hn : alphaN 0 + betaN 0 ≠ 0 := (add_pos (alphaN_pos 0) (betaN_pos 0)).ne'
  funext i
  fin_cases i
  · simp [field, rest, ionic, squid, squidEL]; ring
  · simp [field, rest, gate, mRest, steady]; field_simp; ring
  · simp [field, rest, gate, hRest, steady]; field_simp; ring
  · simp [field, rest, gate, nRest, steady]; field_simp; ring

/-- The resting gating values lie in the open gating cube, and `rest` lies in the trapping box
`[-12, 115] × [0, 1]³`. -/
example : rest ∈ box (-12) 115 := by
  obtain ⟨m1, m2⟩ := mRest_bounds
  obtain ⟨h1, h2⟩ := hRest_bounds
  obtain ⟨n1, n2⟩ := nRest_bounds
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [rest, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] <;> norm_num <;> linarith

/-! ### Voltage clamp: gating variables stay in `[0, 1]` -/

/-- Under a voltage clamp `V ≡ 50` mV the sodium activation obeys the linear equation
`m' = α_m(50) (1 - m) - β_m(50) m`, solved by `m(t) = m∞ + (m₀ - m∞) e^{-(α + β) t}`. -/
noncomputable def clampM (m₀ t : ℝ) : ℝ :=
  steady alphaM betaM 50 + (m₀ - steady alphaM betaM 50) * exp (-(alphaM 50 + betaM 50) * t)

/-- `clampM` solves the clamped gating equation (computed from the definitions). -/
theorem hasDerivAt_clampM (m₀ t : ℝ) :
    HasDerivAt (clampM m₀) (gate alphaM betaM 50 (clampM m₀ t)) t := by
  have hk : alphaM 50 + betaM 50 ≠ 0 := (add_pos (alphaM_pos 50) (betaM_pos 50)).ne'
  have h := (((hasDerivAt_id t).const_mul (-(alphaM 50 + betaM 50))).exp).const_mul
    (m₀ - steady alphaM betaM 50) |>.const_add (steady alphaM betaM 50)
  refine h.congr_deriv ?_
  simp only [clampM, gate, steady, id]
  field_simp
  ring

/-- Starting from the resting value `m₀ = m∞(0)`, the clamped activation stays in `[0, 1]`:
`m(t)` is a convex combination of `m₀` and `m∞(50)`, both in `[0, 1]`. -/
example (t : ℝ) (ht : 0 ≤ t) : clampM mRest t ∈ Icc 0 1 := by
  have hs := steady_mem_Ioo (alphaM_pos 50) (betaM_pos 50)
  have hm := mRest_mem
  set w := exp (-(alphaM 50 + betaM 50) * t)
  have hw0 : 0 < w := exp_pos _
  have hw1 : w ≤ 1 := exp_le_one_iff.2 (by
    have := add_pos (alphaM_pos 50) (betaM_pos 50); nlinarith)
  have hconv : clampM mRest t = (1 - w) * steady alphaM betaM 50 + w * mRest := by
    simp only [clampM, w]; ring
  rw [hconv]
  constructor <;> nlinarith [hs.1, hs.2, hm.1, hm.2]

/-- The same statement through the library theorem `gate_mem_Icc`, for every clamped initial
value in `[0, 1]`. -/
example (m₀ : ℝ) (h₀ : m₀ ∈ Icc 0 1) (t : ℝ) (ht : 0 ≤ t) : clampM m₀ t ∈ Icc 0 1 := by
  have h0 : clampM m₀ 0 = m₀ := by simp [clampM]
  exact gate_mem_Icc (V := fun _ => 50) alphaM_pos betaM_pos
    (fun s _ => hasDerivAt_clampM m₀ s) (by rw [h0]; exact h₀) t ht

/-! ### A depolarized initial state stays bounded -/

/-- `[-12, 115]` is a trapping interval for the squid parameters, checked from the definitions
and the bounds on `EL`. -/
theorem squid_isTrapping : IsTrapping squid (-12) 115 := by
  obtain ⟨h1, h2⟩ := squidEL_bounds
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [squid] <;> norm_num <;> linarith

/-- The depolarized initial state `V₀ = 90` mV with resting gating values. -/
noncomputable def depolarized : Fin 4 → ℝ := ![90, mRest, hRest, nRest]

/-- From `V₀ = 90` mV a global solution exists and stays in `[-12, 115] × [0, 1]³`. -/
example : ∃ x : ℝ → Fin 4 → ℝ, x 0 = depolarized ∧ IsSolution squid x ∧
    ∀ t, 0 ≤ t → x t ∈ box (-12) 115 := by
  have hm := mRest_mem
  have hh := hRest_mem
  have hn := nRest_mem
  refine exists_isSolution_mem_box squid_valid squid_isTrapping ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩ <;> simp only [depolarized, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three] <;>
    norm_num <;> linarith [hm.1, hm.2, hh.1, hh.2, hn.1, hn.2]

/-- At the upper voltage face `V = 115` the voltage derivative is negative for every gating
state in `[0, 1]³` (computed from the definition of the field). -/
example (m h n : ℝ) (_hm : m ∈ Icc (0 : ℝ) 1) (_hh : h ∈ Icc (0 : ℝ) 1)
    (hn : n ∈ Icc (0 : ℝ) 1) :
    field squid ![115, m, h, n] 0 < 0 := by
  obtain ⟨h1, h2⟩ := squidEL_bounds
  have : 0 ≤ 36 * n ^ 4 * (115 - -12) := by have := hn.1; positivity
  simp only [field_zero, ionic, squid, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num at this ⊢
  nlinarith

/-! ### Linearization at rest -/

/-- The Jacobian at rest is Hurwitz, and the resting state is exponentially stable. -/
example : (jac squid rest).IsHurwitz := jac_squid_rest_isHurwitz

example : ∃ δ K α : ℝ, 0 < δ ∧ 0 < K ∧ 0 < α ∧ ∀ x₀ : Fin 4 → ℝ, ‖x₀ - rest‖ < δ →
    (∃ x, x 0 = x₀ ∧ IsSolution squid x) ∧ ∀ x, IsSolution squid x → x 0 = x₀ →
      ∀ t, 0 ≤ t → ‖x t - rest‖ ≤ K * exp (-(α * t)) * ‖x₀ - rest‖ :=
  rest_exponentially_stable

/-- `vtrap` removes the singularity: `vtrap 0 = 1` and `vtrap` is continuous there. -/
example : vtrap 0 = 1 := by simp [vtrap]

example : ContinuousAt vtrap 0 := contDiff_vtrap.continuous.continuousAt

end MathlibExtTest.Biology.Biophysics.HodgkinHuxley
