/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.SemilinearFlow.Instability
import MathlibExt.Biology.Dynamics.TuringPatterns

/-! Tests for linearized instability of semilinear flows.

* Non-vacuity of the map form: `G y = 2 y + y²` on `ℝ` has linearization `2` and a quadratic
  remainder, so all hypotheses of `exists_escape_of_eigenvalue` hold at `0`.
* Non-vacuity of the semigroup form: the flow `Φ t x = eᵗ x` on `ℂ` with semigroup `S t = eᵗ`,
  eigenvalue `κ = 1`, growth bound `ω = 1 < 2 · Re κ`.
* Boundary case: an unstable *continuum* wavenumber whose domain spectrum has no unstable mode.
  The Schnakenberg kinetics with `d_v / d_u = 9` have the unstable wavenumber `k = 1/√3`, but on
  `[0, 1]` with Neumann boundary conditions no admissible wavenumber `k_n = n π` is unstable:
  no Neumann Fourier mode `cos(n π x)` is unstable, so no such mode can supply the eigenvalue
  hypothesis of the instability theorems. (That the linearized operator has no other unstable
  eigenvalue would need completeness of the Neumann modes, not formalized here.) -/

namespace MathlibExtTest.Analysis.PDE.SemilinearFlow.Instability

open MathlibExt.Analysis.PDE.SemilinearFlow.Instability

/-! ### Map form: `G y = 2 y + y²` -/

/-- Multiplication by `2` on `ℝ`. -/
noncomputable def L₂ : ℝ →L[ℝ] ℝ := (2 : ℝ) • ContinuousLinearMap.id ℝ ℝ

theorem L₂_apply (y : ℝ) : L₂ y = 2 * y := by simp [L₂]

theorem norm_L₂_pow_le (n : ℕ) : ‖L₂ ^ n‖ ≤ 1 * 2 ^ n := by
  have h : L₂ ^ n = (2 : ℝ) ^ n • ContinuousLinearMap.id ℝ ℝ := by
    rw [L₂, smul_pow, ← ContinuousLinearMap.one_def, one_pow]
  rw [h, one_mul]
  refine (norm_smul_le ((2 : ℝ) ^ n) (ContinuousLinearMap.id ℝ ℝ)).trans ?_
  rw [norm_pow, Real.norm_two]
  exact mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le

/-- The origin is an unstable fixed point of `y ↦ 2 y + y²`: all hypotheses of
`exists_escape_of_eigenvalue` hold with `ρ = C = 1`, `p = 2`, `ν = 2`, `μ = 2 < 2² = 4`. -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ, ‖x - 0‖ < δ ∧
    ∃ n, (∀ k < n, ‖(fun y : ℝ => 2 * y + y ^ 2)^[k] x - 0‖ ≤ 1) ∧
      ε ≤ ‖(fun y : ℝ => 2 * y + y ^ 2)^[n] x - 0‖ := by
  refine exists_escape_of_eigenvalue (L := L₂) (ν := (2 : ℝ)) (v := 1) (p := 2) (M := 1)
    (μ := 2) one_pos zero_le_one one_lt_two (fun y _ => ?_) one_ne_zero ?_ ?_ zero_le_two ?_
    norm_L₂_pow_le
  · rw [L₂_apply, zero_add, sub_zero, show 2 * y + y ^ 2 - 2 * y = y ^ 2 by ring, one_mul,
      Real.rpow_two, norm_pow]
  · rw [L₂_apply, smul_eq_mul]
  · rw [Real.norm_two]; exact one_lt_two
  · rw [Real.norm_two, Real.rpow_two]; norm_num

/-! ### Semigroup form: `Φ t x = eᵗ x` -/

/-- The semigroup `S t = eᵗ` on `ℂ`. -/
noncomputable def expSemigroup (t : ℝ) : ℂ →L[ℂ] ℂ :=
  (Real.exp t : ℂ) • ContinuousLinearMap.id ℂ ℂ

theorem expSemigroup_apply (t : ℝ) (x : ℂ) : expSemigroup t x = Real.exp t * x := by
  simp [expSemigroup]

/-- The origin is unstable for `u' = u` (linear flow, zero remainder): all hypotheses of
`exists_escape_of_semigroup` hold with `T = 1`, `κ = 1`, `ω = 1`, `p = 2`. -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : ℂ, ‖x - 0‖ < δ ∧
    ∃ t, 0 ≤ t ∧ ε ≤ ‖(Real.exp t : ℂ) * x - 0‖ := by
  refine exists_escape_of_semigroup (Φ := fun t x => (Real.exp t : ℂ) * x) (S := expSemigroup)
    (T := 1) (ρ := 1) (C := 0) (p := 2) (M := 1) (ω := 1) (κ := 1) (φ := 1)
    one_pos one_pos le_rfl one_lt_two (fun x => by simp) (fun n x _ => ?_) (fun y _ => ?_)
    ?_ (fun s t _ _ => ?_) (fun t _ => ?_) one_ne_zero ?_ (by simp) (by norm_num)
  · simp only [mul_one, Real.exp_add, Complex.ofReal_mul]; ring
  · simp [expSemigroup_apply]
  · ext; simp [expSemigroup]
  · ext; simp [expSemigroup, Real.exp_add, mul_comm]
  · rw [one_mul, one_mul, expSemigroup]
    refine (norm_smul_le (Real.exp t : ℂ) (ContinuousLinearMap.id ℂ ℂ)).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos t)]
    exact mul_le_of_le_one_right (Real.exp_pos t).le ContinuousLinearMap.norm_id_le
  · rw [expSemigroup_apply, mul_one, mul_one, smul_eq_mul, mul_one, Complex.ofReal_exp]

/-! ### Boundary case: unstable continuum wavenumber absent from the domain spectrum -/

open MathlibExt.Biology.Dynamics.TuringPatterns in
/-- **Continuum instability without domain instability.** For the Schnakenberg kinetics at
`a = 1/10`, `b = 9/10` with `d_u = 1`, `d_v = 9`, the continuum wavenumber `k = 1/√3` is
unstable, yet on `[0, 1]` with Neumann boundary conditions no admissible wavenumber `n π` is.
An unstable continuum wavenumber therefore yields no Neumann Fourier mode that could supply the
eigenvalue hypothesis of `exists_escape_of_semigroup` on this domain. -/
example : IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 (Real.sqrt (1 / 3)) ∧
    ∀ n : ℕ,
      ¬ IsUnstableMode (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 (neumannWavenumber 1 n) := by
  have htr : (schnakenbergJacobian (1 / 10) (9 / 10)).trace < 0 :=
    (trace_schnakenbergJacobian_neg_iff (by norm_num)).2 (by norm_num)
  have hdet : 0 < (schnakenbergJacobian (1 / 10) (9 / 10)).det := by
    rw [det_schnakenbergJacobian (by norm_num)]; norm_num
  refine ⟨?_, fun n => ?_⟩
  · rw [isUnstableMode_iff_dispersionDet_neg htr zero_le_one (by norm_num),
      Real.sq_sqrt (by norm_num), dispersionDet, det_schnakenbergJacobian (by norm_num)]
    norm_num [schnakenbergJacobian]
  refine not_isUnstableMode_neumannWavenumber_of_le one_pos (by norm_num) htr hdet one_pos ?_ n
  have hΔ : bandDiscriminant (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9 ≤ 4 := by
    rw [bandDiscriminant, det_schnakenbergJacobian (by norm_num)]
    norm_num [schnakenbergJacobian]
  have hs : Real.sqrt (bandDiscriminant (schnakenbergJacobian (1 / 10) (9 / 10)) 1 9) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hΔ
  have hpi : (2 : ℝ) ^ 2 ≤ (Real.pi / 1) ^ 2 := by
    rw [div_one]
    exact pow_le_pow_left₀ (by norm_num) Real.two_le_pi 2
  unfold bandUpper
  norm_num [schnakenbergJacobian] at hs ⊢
  rw [div_le_iff₀ (by norm_num)]
  nlinarith

end MathlibExtTest.Analysis.PDE.SemilinearFlow.Instability
