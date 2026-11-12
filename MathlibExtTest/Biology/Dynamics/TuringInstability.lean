/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.TuringInstability
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Tests for nonlinear Turing instability.

* Values: the growth rate of the saddle `J = diag(1, -2)` is `1`; Neumann modes have the sup norm
  of their amplitude, and mode `0` is the constant state.
* Non-vacuity of `ActsByModalODE`: the scalar semigroup `eᵗ` acts on every Neumann mode through
  the modal ODE of the identity matrix.
* Non-vacuity of the main theorem `exists_escape_of_isUnstableMode`: with no diffusion and the
  saddle kinetics `J = diag(1, -2)` (`tr J = -1 < 0`, `det J = -2 < 0`), the pointwise semigroup
  `diag(eᵗ, e^{-2t})` is the linearized semigroup on `C([0, 1]; ℝ²)`. It acts on every Neumann
  mode through the modal ODE of `J`, has growth bound `eᵗ`, and its own flow satisfies every
  hypothesis with a zero remainder, so the theorem applies.
* Boundary case: for `L < 0` the interval `[0, L]` is empty and every Neumann mode is `0`, even
  with a nonzero amplitude, so the hypothesis `0 ≤ L` of `neumannMode_ne_zero` and
  `norm_neumannMode` cannot be dropped. -/

open Matrix Set
open scoped NNReal

namespace MathlibExtTest.Biology.Dynamics.TuringInstability

open MathlibExt.Biology.Dynamics.TuringPatterns
open MathlibExt.Biology.Dynamics.TuringInstability
open MathlibExt.Analysis.PDE.SemilinearFlow

/-- The saddle kinetics Jacobian `diag(1, -2)`. -/
noncomputable abbrev saddle : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -2]

/-- With no diffusion every mode matrix is the Jacobian itself. -/
theorem modeMatrix_saddle (k : ℝ) : modeMatrix saddle 0 0 k = saddle := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [modeMatrix, diffusionMatrix]

/-- The growth rate of the saddle is its unstable eigenvalue `1`: `(-1 + √9) / 2`. -/
theorem growthRate_saddle (k : ℝ) : growthRate saddle 0 0 k = 1 := by
  rw [growthRate, modeMatrix_saddle]
  have h : Real.sqrt (((saddle).trace) ^ 2 - 4 * (saddle).det) = 3 := by
    rw [show ((saddle).trace) ^ 2 - 4 * (saddle).det = 3 ^ 2 by
      simp [Matrix.trace_fin_two, Matrix.det_fin_two]; norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [h]
  simp [Matrix.trace_fin_two]
  norm_num

example : (modeMatrix saddle 0 0 1).det < 0 := by
  rw [modeMatrix_saddle]; simp [Matrix.det_fin_two]

/-- Every Neumann mode of the saddle is unstable. -/
theorem isUnstableMode_saddle (k : ℝ) : IsUnstableMode saddle 0 0 k := by
  rw [isUnstableMode_iff_dispersionDet_neg (by simp [Matrix.trace_fin_two]) le_rfl
    le_rfl]
  simp [dispersionDet, Matrix.det_fin_two]

example (n : ℕ) : 0 < growthRate saddle 0 0 (neumannWavenumber 1 n) ∧
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ modeMatrix saddle 0 0 (neumannWavenumber 1 n) *ᵥ v =
      growthRate saddle 0 0 (neumannWavenumber 1 n) • v :=
  exists_growthRate_of_isUnstableMode (by simp [Matrix.trace_fin_two]) le_rfl le_rfl
    (isUnstableMode_saddle _)

/-! ### Neumann modes -/

example (w : Fin 2 → ℝ) (n : ℕ) : ‖neumannMode 1 n w‖ = ‖w‖ :=
  norm_neumannMode zero_le_one n w

/-- Mode `0` is the constant state `w`. -/
example (L : ℝ) (w : Fin 2 → ℝ) : neumannMode L 0 w = ContinuousMap.const _ w := by
  ext x i
  simp [neumannWavenumber]

example : neumannMode 1 3 ![1, 0] ≠ 0 :=
  neumannMode_ne_zero zero_le_one 3 (by intro h; simpa using congrFun h 0)

/-- Boundary case: on the empty interval `[0, -1]` a mode with nonzero amplitude is `0`. -/
example : neumannMode (-1) 0 ![1, 0] = 0 := by
  ext x
  have := x.2
  exact absurd (this.1.trans this.2) (by norm_num)

/-! ### `ActsByModalODE`: the scalar semigroup `eᵗ` -/

/-- The scalar semigroup `eᵗ` acts on every Neumann mode through the modal ODE `c' = c`. -/
example (L : ℝ) (n : ℕ) :
    ActsByModalODE (L := L) (fun t => Real.exp t • (1 : _ →L[ℝ] _)) n 1 := by
  intro w
  refine ⟨fun t => Real.exp t • w, by simp, fun t => ?_, fun t => ?_⟩
  · simpa using (Real.hasDerivAt_exp t).smul_const w
  · simp [neumannMode_smul]

/-! ### `pointwiseMatrix` and the Nemytskii remainder -/

example (y : C(Icc (0 : ℝ) 1, Fin 2 → ℝ)) (x : Icc (0 : ℝ) 1) :
    pointwiseMatrix _ saddle y x 0 = y x 0 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

/-- Linear kinetics have a zero remainder. -/
example (y : C(Icc (0 : ℝ) 1, Fin 2 → ℝ)) :
    ‖nemytskii (fun z => saddle *ᵥ z) (by fun_prop) (ContinuousMap.const _ 0 + y) -
      nemytskii (fun z => saddle *ᵥ z) (by fun_prop) (ContinuousMap.const _ 0) -
        pointwiseMatrix _ saddle y‖ ≤ 0 * ‖y‖ ^ (2 : ℝ) :=
  norm_nemytskii_sub_le (r := ‖y‖) _ le_rfl (by norm_num)
    (fun z _ => by simp) y le_rfl

/-! ### Non-vacuity of the main theorem: the saddle without diffusion -/

/-- The pointwise linearized semigroup `diag(eᵗ, e^{-2t})` of the saddle on `C([0, 1]; ℝ²)`. -/
noncomputable def saddleSemigroup (t : ℝ≥0) :
    C(Icc (0 : ℝ) 1, Fin 2 → ℝ) →L[ℝ] C(Icc (0 : ℝ) 1, Fin 2 → ℝ) :=
  pointwiseMatrix _ (Matrix.diagonal ![Real.exp t, Real.exp (-2 * t)])

theorem saddleSemigroup_apply (t : ℝ≥0) (y : C(Icc (0 : ℝ) 1, Fin 2 → ℝ)) (x : Icc (0 : ℝ) 1)
    (i : Fin 2) :
    saddleSemigroup t y x i = ![Real.exp t, Real.exp (-2 * t)] i * y x i := by
  simp [saddleSemigroup, Matrix.mulVec_diagonal]

theorem norm_saddleSemigroup_le (t : ℝ≥0) :
    ‖saddleSemigroup t‖ ≤ 1 * Real.exp (1 * t) := by
  rw [one_mul, one_mul]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun y => ?_
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have hyi : ‖y x i‖ ≤ ‖y‖ := (norm_le_pi_norm (y x) i).trans (y.norm_coe_le_norm x)
  have h2 : Real.exp (-2 * t) ≤ Real.exp t :=
    Real.exp_le_exp.2 (by have := t.coe_nonneg; linarith)
  rw [saddleSemigroup_apply, norm_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left hyi (Real.exp_pos _).le
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul h2 hyi (abs_nonneg _) (Real.exp_pos _).le

theorem isC0Semigroup_saddleSemigroup : IsC0Semigroup saddleSemigroup where
  map_zero := by
    ext y x i
    fin_cases i <;> simp [saddleSemigroup_apply]
  map_add s t := by
    ext y x i
    fin_cases i <;>
      simp [saddleSemigroup_apply, Real.exp_add, mul_add] <;> ring
  continuous_apply y := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have : Function.uncurry (fun t x => saddleSemigroup t y x) =
        fun p : ℝ≥0 × Icc (0 : ℝ) 1 => fun i =>
          ![Real.exp p.1, Real.exp (-2 * p.1)] i * y p.2 i := by
      ext p i; simp [Function.uncurry, saddleSemigroup_apply]
    rw [this]
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  locally_bounded T := ⟨Real.exp T, fun t ht =>
    (norm_saddleSemigroup_le t).trans (by simpa using Real.exp_le_exp.2 (NNReal.coe_le_coe.2 ht))⟩

theorem actsByModalODE_saddleSemigroup (n : ℕ) :
    ActsByModalODE saddleSemigroup n (modeMatrix saddle 0 0 (neumannWavenumber 1 n)) := by
  rw [modeMatrix_saddle]
  intro w
  refine ⟨fun t => ![Real.exp t * w 0, Real.exp (-2 * t) * w 1], ?_, fun t => ?_, fun t => ?_⟩
  · ext i; fin_cases i <;> simp
  · refine hasDerivAt_pi.2 fun i => ?_
    fin_cases i
    · simpa [mulVec, dotProduct, Fin.sum_univ_two] using (Real.hasDerivAt_exp t).mul_const (w 0)
    · show HasDerivAt (fun t => Real.exp (-2 * t) * w 1)
        ((saddle *ᵥ ![Real.exp t * w 0, Real.exp (-2 * t) * w 1]) 1) t
      have h : (saddle *ᵥ ![Real.exp t * w 0, Real.exp (-2 * t) * w 1]) 1 =
          Real.exp (-2 * t) * (-2 * 1) * w 1 := by
        simp [mulVec, dotProduct, Fin.sum_univ_two]
        ring
      rw [h]
      exact (((hasDerivAt_id t).const_mul (-2)).exp).mul_const (w 1)
  · ext x i
    fin_cases i <;> simp [saddleSemigroup_apply] <;> ring

/-- **Non-vacuity of `exists_escape_of_isUnstableMode`.** The saddle steady state `0` of the
linear flow `Φ t = diag(eᵗ, e^{-2t})` on `C([0, 1]; ℝ²)` is unstable, from the unstable Neumann
mode `n = 1` (growth rate `1`, growth bound `ω = 1 < 2 · 1`, zero remainder). -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : C(Icc (0 : ℝ) 1, Fin 2 → ℝ), ‖x - 0‖ < δ ∧
    ∃ t : ℝ, 0 ≤ t ∧ ε ≤ ‖saddleSemigroup t.toNNReal x - 0‖ := by
  refine exists_escape_of_isUnstableMode (J := saddle) (du := 0) (dv := 0) (L := 1) (n := 1)
    (by simp [Matrix.trace_fin_two]) le_rfl le_rfl zero_le_one (isUnstableMode_saddle _)
    isC0Semigroup_saddleSemigroup (actsByModalODE_saddleSemigroup 1) norm_saddleSemigroup_le
    (p := 2) (by norm_num) (by rw [growthRate_saddle]; norm_num)
    (Φ := fun t x => saddleSemigroup t.toNNReal x) (T := 1) (ρ := 1) (C := 0) one_pos one_pos
    le_rfl (fun x => by simp [isC0Semigroup_saddleSemigroup.map_zero]) (fun m x _ => ?_)
    (fun y _ => by simp)
  have h : ((m : ℝ) + 1).toNNReal = 1 + (m : ℝ).toNNReal := by
    rw [Real.toNNReal_add (by positivity) zero_le_one, add_comm]; simp
  simp only [NNReal.coe_one, mul_one, Real.toNNReal_one, h, isC0Semigroup_saddleSemigroup.map_add,
    ContinuousLinearMap.comp_apply]

end MathlibExtTest.Biology.Dynamics.TuringInstability
