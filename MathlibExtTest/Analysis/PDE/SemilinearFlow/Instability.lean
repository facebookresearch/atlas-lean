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
  eigenvalue would need completeness of the Neumann modes, not formalized here.)
* Public proof steps used from outside `Instability`: `duhamel` on an exact orbit and on a
  forced orbit, `geom_sum_le` (sharp at `μ = 0`), `exists_escape_radius` with the constant
  `1/4` and the failure at `c = 0`, `flow_escape_of_map_escape` for the flow `2ᵗ x`, and
  `exists_norm_pow_le_of_spectralRadius_lt` for a nilpotent operator of norm at least `10`. -/

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

/-! ### Public proof steps, used from outside `Instability` -/

/-- `duhamel` on an exact orbit of `L`: every remainder term vanishes, so `yₙ = Lⁿ y₀`. -/
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : X →L[ℝ] X) (y : ℕ → X)
    (hy : ∀ k, y (k + 1) = L (y k)) (n : ℕ) : y n = (L ^ n) (y 0) := by
  have h := duhamel L y n
  simp only [hy, sub_self, map_zero, Finset.sum_const_zero] at h
  exact sub_eq_zero.1 h

/-- `duhamel` with a nonzero remainder: for the forced orbit `yₖ₊₁ = L yₖ + e`, the deviation
from the linear orbit is `∑_{j<n} Lʲ e`. -/
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : X →L[ℝ] X) (y : ℕ → X)
    (e : X) (hy : ∀ k, y (k + 1) = L (y k) + e) (n : ℕ) :
    y n - (L ^ n) (y 0) = ∑ j ∈ Finset.range n, (L ^ j) e := by
  rw [duhamel L y n]
  simp only [hy, add_sub_cancel_left]

/-- `geom_sum_le` is sharp at the boundary `μ = 0`: the sum is `q^{n-1}`, which equals
`qⁿ / q`. Here `q = 2`, `n = 3`: both sides are `4`. -/
example : ∑ j ∈ Finset.range 3, (0 : ℝ) ^ j * 2 ^ (3 - 1 - j) = 4 ∧
    (2 : ℝ) ^ 3 / (2 - 0) = 4 ∧
    ∑ j ∈ Finset.range 3, (0 : ℝ) ^ j * 2 ^ (3 - 1 - j) ≤ 2 ^ 3 / (2 - 0) :=
  ⟨by norm_num [Finset.sum_range_succ], by norm_num, geom_sum_le le_rfl two_pos 3⟩

/-- `geom_sum_le` with `μ = 1`, `q = 2`, `n = 3`: `4 + 2 + 1 = 7 ≤ 8`. -/
example : ∑ j ∈ Finset.range 3, (1 : ℝ) ^ j * 2 ^ (3 - 1 - j) = 7 ∧
    ∑ j ∈ Finset.range 3, (1 : ℝ) ^ j * 2 ^ (3 - 1 - j) ≤ 2 ^ 3 / (2 - 1) :=
  ⟨by norm_num [Finset.sum_range_succ], geom_sum_le zero_le_one one_lt_two 3⟩

/-- `exists_escape_radius` with the constant `c = 1/4` (the choice made in the general
instability proof), for arbitrary `K ≥ 0`, `r > 0`, `ρ > 0`, `p > 1`. -/
example {K r ρ p : ℝ} (hK : 0 ≤ K) (hr : 0 < r) (hρ : 0 < ρ) (hp : 1 < p) :
    ∃ η, 0 < η ∧ η ≤ 2 * ρ / 3 ∧ K * (r * η) ^ (p - 1) ≤ 1 / 4 :=
  exists_escape_radius hK hr hρ hp (by norm_num)

/-- The hypothesis `0 < c` of `exists_escape_radius` cannot be dropped: with `c = 0`, `K = 1`
no radius exists. -/
example : ¬ ∃ η : ℝ, 0 < η ∧ η ≤ 2 * 1 / 3 ∧ (1 : ℝ) * (1 * η) ^ ((2 : ℝ) - 1) ≤ 0 := by
  rintro ⟨η, hη0, -, h⟩
  norm_num at h
  linarith

/-- The flow `Φ t x = 2ᵗ x` on `ℝ`. -/
noncomputable def powFlow (t : ℝ) (x : ℝ) : ℝ := (2 : ℝ) ^ t * x

/-- `flow_escape_of_map_escape`: the time-`1` map of `powFlow` is `L₂`, so map escape from
`exists_escape_of_eigenvalue` (zero remainder) transfers to escape of the flow. -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : ℝ, ‖x - 0‖ < δ ∧ ∃ t, 0 ≤ t ∧ ε ≤ ‖powFlow t x - 0‖ := by
  have h1 : ∀ x, powFlow 1 x = L₂ x := fun x => by rw [powFlow, Real.rpow_one, L₂_apply]
  refine flow_escape_of_map_escape (T := 1) (ρ := 1) zero_le_one
    (fun x => by rw [powFlow, Real.rpow_zero, one_mul]) (fun n x _ => ?_) ?_
  · rw [powFlow, powFlow, powFlow, mul_one, mul_one, Real.rpow_one,
      Real.rpow_add two_pos, Real.rpow_one, ← mul_assoc, mul_comm _ (2 : ℝ)]
  · refine exists_escape_of_eigenvalue (L := L₂) (ν := (2 : ℝ)) (v := 1) (p := 2) (M := 1)
      (μ := 2) one_pos le_rfl one_lt_two (fun y _ => ?_) one_ne_zero ?_ ?_ zero_le_two ?_
      norm_L₂_pow_le
    · rw [zero_add, h1, sub_zero, sub_self, norm_zero, zero_mul]
    · rw [L₂_apply, smul_eq_mul]
    · rw [Real.norm_two]; exact one_lt_two
    · rw [Real.norm_two, Real.rpow_two]; norm_num

/-- A nilpotent operator on `ℂ × ℂ` with large norm: `N (a, b) = (10 b, 0)`. -/
noncomputable def nil₁₀ : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (10 : ℂ) • (ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.snd ℂ ℂ ℂ)

theorem nil₁₀_apply (x : ℂ × ℂ) : nil₁₀ x = (10 * x.2, 0) := by
  simp [nil₁₀]

theorem nil₁₀_sq : nil₁₀ ^ 2 = 0 := by
  ext <;> simp [pow_two, nil₁₀_apply]

theorem spectralRadius_nil₁₀ : spectralRadius ℂ nil₁₀ = 0 := by
  have h := spectrum.spectralRadius_pow_le' (𝕜 := ℂ) nil₁₀ 2
  rw [nil₁₀_sq, spectrum.spectralRadius_zero, nonpos_iff_eq_zero] at h
  exact (pow_eq_zero_iff two_ne_zero).1 h

theorem ten_le_norm_nil₁₀ : 10 ≤ ‖nil₁₀‖ := by
  have h := nil₁₀.le_opNorm (0, 1)
  rw [nil₁₀_apply] at h
  simpa [Prod.norm_def] using h

/-- `exists_norm_pow_le_of_spectralRadius_lt` gives decay at rate `1/2` for an operator of norm
at least `10`: the growth bound comes from the spectral radius `0`, not from `‖N‖`. -/
example : 1 / 2 < ‖nil₁₀‖ ∧ ∃ M, ∀ n : ℕ, ‖nil₁₀ ^ n‖ ≤ M * (1 / 2 : ℝ) ^ n := by
  refine ⟨lt_of_lt_of_le (by norm_num) ten_le_norm_nil₁₀,
    exists_norm_pow_le_of_spectralRadius_lt ?_⟩
  rw [spectralRadius_nil₁₀]
  exact ENNReal.ofReal_pos.2 (by norm_num)

end MathlibExtTest.Analysis.PDE.SemilinearFlow.Instability
