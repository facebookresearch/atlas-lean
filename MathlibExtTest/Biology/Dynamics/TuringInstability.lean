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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

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
* Non-vacuity of the mild-formulation theorems: `exists_norm_timeMap_sub_le` with zero reaction
  and trivial semigroups on `ℝ`; `exists_escape_of_isUnstableMode_of_mild` with the linear saddle
  kinetics `f z = J z`, no diffusion (`SA = 1`), and the saddle semigroup, whose orbits are shown
  to be mild solutions of `w' = J w` (`isMildSolution_saddleSemigroup`).
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

/-! ### Non-vacuity of the mild-formulation theorems -/

/-- The trivial semigroup `SA t = 1` (no diffusion) is C₀. -/
theorem isC0Semigroup_one {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] :
    IsC0Semigroup fun _ : ℝ≥0 => (1 : X →L[ℝ] X) where
  map_zero := rfl
  map_add _ _ := by ext; simp
  continuous_apply _ := continuous_const
  locally_bounded _ := ⟨1, fun _ _ => ContinuousLinearMap.norm_id_le⟩

/-- **Non-vacuity of `exists_norm_timeMap_sub_le`**: zero reaction, trivial semigroups and the
identity flow on `ℝ`. -/
example : ∃ ρ > 0, ∃ C ≥ 0, ∀ y : ℝ, ‖y‖ ≤ ρ →
    ‖(fun (_ : ℝ) (x : ℝ) => x) 1 (0 + y) - 0 - (1 : ℝ →L[ℝ] ℝ) y‖ ≤ C * ‖y‖ ^ (2 : ℝ) := by
  refine exists_norm_timeMap_sub_le (SA := fun _ => (1 : ℝ →L[ℝ] ℝ))
    (S := fun _ => (1 : ℝ →L[ℝ] ℝ)) (F := fun _ => 0) (B := 0) (Φ := fun _ x => x) (u₀ := 0)
    (T := 1) (ρ₀ := 1) (R := 1) (r := 1) (K := 0) (p := 2) isC0Semigroup_one
    (fun _ => ⟨0, LipschitzWith.const' 0 |>.lipschitzOnWith⟩)
    zero_le_one one_pos one_pos le_rfl (by norm_num) (fun _ => rfl) rfl (fun z _ => by simp)
    (fun y => ⟨continuousOn_const, fun _ _ => by simp, fun _ _ => by simp [duhamel]⟩)
    (fun x hx => ⟨⟨continuousOn_const, fun _ _ => by simp, fun _ _ => by simp [duhamel]⟩, ?_⟩)
  intro t _
  simpa using hx

/-- The saddle semigroup on all real times, as an explicit combination of exponentials. -/
private theorem saddleSemigroup_eq (y : C(Icc (0 : ℝ) 1, Fin 2 → ℝ)) {t : ℝ} (ht : 0 ≤ t) :
    saddleSemigroup t.toNNReal y =
      Real.exp t • pointwiseMatrix _ (Matrix.diagonal ![1, 0]) y +
        Real.exp (-2 * t) • pointwiseMatrix _ (Matrix.diagonal ![0, 1]) y := by
  ext x i
  fin_cases i <;> simp [saddleSemigroup_apply, Matrix.mulVec_diagonal, Real.coe_toNNReal _ ht]

/-- The orbits of the saddle semigroup are mild solutions of `w' = J w` (no diffusion). -/
theorem isMildSolution_saddleSemigroup (y : C(Icc (0 : ℝ) 1, Fin 2 → ℝ)) (T : ℝ) :
    IsMildSolution (fun _ => (1 : C(Icc (0 : ℝ) 1, Fin 2 → ℝ) →L[ℝ] _))
      (pointwiseMatrix _ saddle) y T fun t => saddleSemigroup t.toNNReal y := by
  set P₀ := pointwiseMatrix _ (Matrix.diagonal ![(1 : ℝ), 0]) y
  set P₁ := pointwiseMatrix _ (Matrix.diagonal ![(0 : ℝ), 1]) y
  set g : ℝ → C(Icc (0 : ℝ) 1, Fin 2 → ℝ) := fun t => Real.exp t • P₀ + Real.exp (-2 * t) • P₁
  have hB : ∀ t, pointwiseMatrix _ saddle (g t) =
      Real.exp t • P₀ + (Real.exp (-2 * t) * -2) • P₁ := by
    intro t
    ext x i
    simp only [g, P₀, P₁, pointwiseMatrix_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    fin_cases i
    · simp [Matrix.diagonal]
    · simp [Matrix.diagonal]
      ring
  have hg : ∀ t, HasDerivAt g (pointwiseMatrix _ saddle (g t)) t := by
    intro t
    rw [hB]
    have h1 := ((Real.hasDerivAt_exp t).smul_const P₀).add
      ((((hasDerivAt_id t).const_mul (-2)).exp).smul_const P₁)
    refine h1.congr_deriv ?_
    simp only [id, mul_one]
  have hgc : Continuous fun t => pointwiseMatrix _ saddle (g t) :=
    (pointwiseMatrix _ saddle).continuous.comp
      (continuous_iff_continuousAt.2 fun t => (hg t).continuousAt)
  have hcont : Continuous fun t : ℝ => saddleSemigroup t.toNNReal y :=
    (isC0Semigroup_saddleSemigroup.continuous_apply y).comp continuous_real_toNNReal
  refine ⟨hcont.continuousOn, fun t _ => ?_, fun t ht => ?_⟩
  · simp only [one_apply_eq_self]
    exact ((pointwiseMatrix _ saddle).continuous.comp hcont).intervalIntegrable 0 t
  · simp only [duhamel, one_apply_eq_self]
    have hcongr : ∫ s in (0 : ℝ)..t, pointwiseMatrix _ saddle (saddleSemigroup s.toNNReal y) =
        ∫ s in (0 : ℝ)..t, pointwiseMatrix _ saddle (g s) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [saddleSemigroup_eq y hs.1, g, P₀, P₁]
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hg s)
      (hgc.intervalIntegrable 0 t), saddleSemigroup_eq y ht.1]
    have hg0 : g 0 = y := by
      ext x i
      fin_cases i <;> simp [g, P₀, P₁, Matrix.mulVec_diagonal]
    rw [hg0, add_sub_cancel]

/-- **Non-vacuity of `exists_escape_of_isUnstableMode_of_mild`.** Linear saddle kinetics
`f z = J z` with `J = diag(1, -2)`, no diffusion (`SA = 1`), linearized semigroup and flow the
pointwise `diag(eᵗ, e^{-2t})`, steady state `a = 0`, remainder order `p = 2` (zero remainder). -/
example : ∃ ε > 0, ∀ δ > 0, ∃ x : C(Icc (0 : ℝ) 1, Fin 2 → ℝ),
    ‖x - ContinuousMap.const _ 0‖ < δ ∧
      ∃ t : ℝ, 0 ≤ t ∧ ε ≤ ‖saddleSemigroup t.toNNReal x - ContinuousMap.const _ 0‖ := by
  have hfc : Continuous fun z : Fin 2 → ℝ => saddle *ᵥ z := by fun_prop
  set A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin saddle)
  have hN : nemytskii (K := Icc (0 : ℝ) 1) (fun z => saddle *ᵥ z) hfc =
      ⇑(pointwiseMatrix _ saddle) := by
    funext u; ext x i; rfl
  have hstep : ∀ (m : ℕ) (x : C(Icc (0 : ℝ) 1, Fin 2 → ℝ)),
      saddleSemigroup (((m : ℝ) + 1) * ((1 : ℝ≥0) : ℝ)).toNNReal x =
        saddleSemigroup ((1 : ℝ≥0) : ℝ).toNNReal
          (saddleSemigroup ((m : ℝ) * ((1 : ℝ≥0) : ℝ)).toNNReal x) := by
    intro m x
    have h : ((m : ℝ) + 1).toNNReal = 1 + (m : ℝ).toNNReal := by
      rw [Real.toNNReal_add (by positivity) zero_le_one, add_comm]; simp
    simp only [NNReal.coe_one, mul_one, Real.toNNReal_one, h,
      isC0Semigroup_saddleSemigroup.map_add, ContinuousLinearMap.comp_apply]
  refine exists_escape_of_isUnstableMode_of_mild (J := saddle) (du := 0) (dv := 0) (L := 1)
    (n := 1) (by simp [Matrix.trace_fin_two]) le_rfl le_rfl zero_le_one (isUnstableMode_saddle _)
    hfc (fun _ => ⟨‖A‖₊, A.lipschitzWith.lipschitzOnWith⟩) (a := 0) (by simp)
    (r := 1) (K := 0) (p := 2) one_pos le_rfl (by norm_num) (fun z _ => by simp)
    (SA := fun _ => 1) (S := saddleSemigroup) isC0Semigroup_one (fun _ => rfl)
    isC0Semigroup_saddleSemigroup (T := 1) one_pos (fun y => isMildSolution_saddleSemigroup y _)
    (actsByModalODE_saddleSemigroup 1) norm_saddleSemigroup_le
    (by rw [growthRate_saddle]; norm_num) (Φ := fun t x => saddleSemigroup t.toNNReal x)
    (ρ₀ := 1) (R := Real.exp 1) one_pos
    (fun x => by simp [isC0Semigroup_saddleSemigroup.map_zero]) (fun m x _ => hstep m x)
    (fun x hx => ⟨hN ▸ isMildSolution_saddleSemigroup x _, fun t ht => ?_⟩)
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  refine ((saddleSemigroup _).le_opNorm x).trans ?_
  refine (mul_le_mul (norm_saddleSemigroup_le _) hx' (norm_nonneg _) (by positivity)).trans ?_
  have : ((t.toNNReal : ℝ)) ≤ 1 := by
    rw [Real.coe_toNNReal _ ht.1]; simpa using ht.2
  simpa using Real.exp_le_exp.2 this

end MathlibExtTest.Biology.Dynamics.TuringInstability
