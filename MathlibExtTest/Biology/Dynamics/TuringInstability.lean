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
* Non-vacuity of the general theorem `exists_escape_of_isUnstableMode`: with no diffusion and the
  saddle kinetics `J = diag(1, -2)` (`tr J = -1 < 0`, `det J = -2 < 0`), the pointwise semigroup
  `diag(eᵗ, e^{-2t})` is the linearized semigroup on `C([0, 1]; ℝ²)`. It acts on every Neumann
  mode through the modal ODE of `J`, has growth bound `eᵗ`, and its own flow satisfies every
  hypothesis with a zero remainder, so the theorem applies. This instability is *not* diffusion
  driven: the kinetics alone are unstable (`det J < 0`).
* Non-vacuity of the mild-formulation theorems: `exists_norm_timeMap_sub_le` with zero reaction
  and trivial semigroups on `ℝ`; `exists_escape_of_isUnstableMode_of_mild` with the linear saddle
  kinetics `f z = J z`, no diffusion (`SA = 1`), and the saddle semigroup, whose orbits are shown
  to be mild solutions of `w' = J w` (`isMildSolution_saddleSemigroup`).
* Non-vacuity of the Turing corollaries `turing_instability_exists_escape` and
  `turing_instability_exists_escape_of_mild` on a genuinely diffusion-driven instability: the
  activator–inhibitor Jacobian `J = [[37/4, 8], [-11, -19/2]]` has `tr J = -1/4 < 0` and
  `det J = 1/8 > 0`, so no mode is unstable without diffusion, while with
  `D = diag(1/4, 1/2)` the Neumann mode `n = 1` on `[0, π]` (`k = 1`) has
  `J - D = [[9, 8], [-11, -10]]` with eigenvalues `1` and `-2`. The linearized semigroup is the
  pointwise `e^{t (J - D)} = eᵗ P + e^{-2t} Q` (spectral projections `P`, `Q`) and the diffusion
  semigroup the pointwise `e^{-t D}`. These are *not* the Neumann semigroups `e^{t (D Δ_N + J)}`
  and `e^{t D Δ_N}`: they act on every mode as those act on the mode `n = 1` only. The theorems
  constrain the semigroups on that mode (`ActsByModalODE`) and otherwise only through the
  C₀ property, the growth bound and the mild-solution identity, which the stand-ins satisfy; the
  spectral data (`tr J < 0 < det J`, mode `1` unstable only with diffusion) are those of a
  genuine Turing instability. The linearized orbits are shown to be mild solutions of
  `w' = -D w + J w` for the stand-in diffusion semigroup (`isMildSolution_turingSemigroup`).
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

/-! ### Non-vacuity of the Turing corollaries: a diffusion-driven instability -/

/-- Activator–inhibitor kinetics Jacobian `J = [[37/4, 8], [-11, -19/2]]`. -/
noncomputable abbrev turingJ : Matrix (Fin 2) (Fin 2) ℝ := !![37 / 4, 8; -11, -19 / 2]

/-- `tr J = -1/4 < 0`. -/
theorem trace_turingJ : turingJ.trace < 0 := by
  norm_num [Matrix.trace_fin_two]

/-- `det J = 1/8 > 0`: together with `tr J < 0`, the kinetics are stable without diffusion. -/
theorem det_turingJ : 0 < turingJ.det := by
  norm_num [Matrix.det_fin_two]

/-- Without diffusion no mode of `turingJ` is unstable, so the instability below is diffusion
driven. -/
example (k : ℝ) : ¬ IsUnstableMode turingJ 0 0 k := by
  rw [isUnstableMode_iff_dispersionDet_neg trace_turingJ le_rfl le_rfl]
  intro h
  simp only [dispersionDet] at h
  linarith [det_turingJ]

/-- The Neumann wavenumber of mode `1` on `[0, π]` is `1`. -/
theorem neumannWavenumber_pi_one : neumannWavenumber Real.pi 1 = 1 := by
  simp [neumannWavenumber, Real.pi_ne_zero]

/-- The mode matrix `J - k² D` at `k = 1` with `D = diag(1/4, 1/2)`. -/
noncomputable abbrev turingM : Matrix (Fin 2) (Fin 2) ℝ := !![9, 8; -11, -10]

theorem modeMatrix_turingJ :
    modeMatrix turingJ (1 / 4) (1 / 2) (neumannWavenumber Real.pi 1) = turingM := by
  rw [neumannWavenumber_pi_one]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [modeMatrix, diffusionMatrix]

/-- The Neumann mode `1` is unstable with diffusion (`det (J - D) = -2 < 0`). -/
theorem isUnstableMode_turingJ :
    IsUnstableMode turingJ (1 / 4) (1 / 2) (neumannWavenumber Real.pi 1) :=
  (turing_instability trace_turingJ det_turingJ (by norm_num) (by norm_num)
    (by rw [modeMatrix_turingJ]; norm_num [Matrix.det_fin_two])).2

/-- The growth rate of the unstable mode is `1`: `(-1 + √9) / 2`. -/
theorem growthRate_turingJ :
    growthRate turingJ (1 / 4) (1 / 2) (neumannWavenumber Real.pi 1) = 1 := by
  rw [growthRate, modeMatrix_turingJ]
  have h : Real.sqrt (turingM.trace ^ 2 - 4 * turingM.det) = 3 := by
    rw [show turingM.trace ^ 2 - 4 * turingM.det = 3 ^ 2 by
      norm_num [Matrix.trace_fin_two, Matrix.det_fin_two]]
    exact Real.sqrt_sq (by norm_num)
  rw [h]
  norm_num [Matrix.trace_fin_two]

/-- The spectral projection of `J - D` onto its eigenvalue `1`. -/
noncomputable abbrev turingP : Matrix (Fin 2) (Fin 2) ℝ := !![11 / 3, 8 / 3; -11 / 3, -8 / 3]

/-- The spectral projection of `J - D` onto its eigenvalue `-2`. -/
noncomputable abbrev turingQ : Matrix (Fin 2) (Fin 2) ℝ := !![-8 / 3, -8 / 3; 11 / 3, 11 / 3]

/-- The phase space `C([0, π]; ℝ²)`. -/
abbrev TuringSpace := C(Icc (0 : ℝ) Real.pi, Fin 2 → ℝ)

/-- `e^{t (J - D)} = eᵗ P + e^{-2t} Q`, acting pointwise, for all real `t`. -/
noncomputable def turingOp (t : ℝ) : TuringSpace →L[ℝ] TuringSpace :=
  Real.exp t • pointwiseMatrix _ turingP + Real.exp (-2 * t) • pointwiseMatrix _ turingQ

theorem turingOp_apply (t : ℝ) (y : TuringSpace) (x : Icc (0 : ℝ) Real.pi) :
    turingOp t y x = Real.exp t • (turingP *ᵥ y x) + Real.exp (-2 * t) • (turingQ *ᵥ y x) :=
  rfl

theorem continuous_turingOp : Continuous turingOp := by
  unfold turingOp
  fun_prop

/-- The stand-in linearized semigroup `e^{t (J - D)}` on `C([0, π]; ℝ²)`, acting pointwise. It
agrees with `e^{t (D Δ_N + J)}` on the Neumann mode `n = 1` only. -/
noncomputable def turingSemigroup (t : ℝ≥0) : TuringSpace →L[ℝ] TuringSpace :=
  turingOp t

/-- The growth-bound constant `‖P‖ + ‖Q‖` (operator norms on the phase space). -/
noncomputable abbrev turingBound : ℝ :=
  ‖pointwiseMatrix (Icc (0 : ℝ) Real.pi) turingP‖ + ‖pointwiseMatrix (Icc (0 : ℝ) Real.pi) turingQ‖

theorem norm_turingSemigroup_le (t : ℝ≥0) :
    ‖turingSemigroup t‖ ≤ turingBound * Real.exp (1 * t) := by
  have h2 : Real.exp (-2 * t) ≤ Real.exp t :=
    Real.exp_le_exp.2 (by have := t.coe_nonneg; linarith)
  have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (pointwiseMatrix (Icc (0 : ℝ) Real.pi)
    turingQ))
  have hP := ContinuousLinearMap.opNorm_smul_le (Real.exp (t : ℝ))
    (pointwiseMatrix (Icc (0 : ℝ) Real.pi) turingP)
  have hQ := ContinuousLinearMap.opNorm_smul_le (Real.exp (-2 * (t : ℝ)))
    (pointwiseMatrix (Icc (0 : ℝ) Real.pi) turingQ)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hP hQ
  unfold turingSemigroup turingOp
  refine (norm_add_le (E := TuringSpace →L[ℝ] TuringSpace) _ _).trans ?_
  rw [one_mul]
  linarith

theorem isC0Semigroup_turingSemigroup : IsC0Semigroup turingSemigroup where
  map_zero := by
    ext y x i
    fin_cases i <;> simp [turingSemigroup, turingOp_apply, dotProduct, Fin.sum_univ_two] <;>
      ring
  map_add s t := by
    ext y x i
    have h1 : Real.exp ((s : ℝ) + t) = Real.exp s * Real.exp t := Real.exp_add _ _
    have h2 : Real.exp (-2 * ((s : ℝ) + t)) = Real.exp (-2 * s) * Real.exp (-2 * t) := by
      rw [← Real.exp_add]; ring_nf
    simp only [turingSemigroup, NNReal.coe_add, ContinuousLinearMap.comp_apply, turingOp_apply,
      h1, h2]
    fin_cases i <;> simp [dotProduct, Fin.sum_univ_two] <;> ring
  continuous_apply y :=
    (continuous_turingOp.comp NNReal.continuous_coe).clm_apply continuous_const
  locally_bounded T := ⟨turingBound * Real.exp T, fun t ht =>
    (norm_turingSemigroup_le t).trans (by gcongr; simpa using ht)⟩

theorem actsByModalODE_turingSemigroup :
    ActsByModalODE turingSemigroup 1
      (modeMatrix turingJ (1 / 4) (1 / 2) (neumannWavenumber Real.pi 1)) := by
  rw [modeMatrix_turingJ]
  intro w
  refine ⟨fun t => Real.exp t • (turingP *ᵥ w) + Real.exp (-2 * t) • (turingQ *ᵥ w), ?_,
    fun t => ?_, fun t => ?_⟩
  · ext i; fin_cases i <;> simp [dotProduct, Fin.sum_univ_two] <;> ring
  · have h := ((Real.hasDerivAt_exp t).smul_const (turingP *ᵥ w)).add
      ((((hasDerivAt_id t).const_mul (-2)).exp).smul_const (turingQ *ᵥ w))
    refine h.congr_deriv ?_
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · ext x i
    fin_cases i <;> simp [turingSemigroup, turingOp_apply, dotProduct, Fin.sum_univ_two] <;>
      ring

theorem turingSemigroup_step (m : ℕ) (x : TuringSpace) :
    turingSemigroup (((m : ℝ) + 1) * ((1 : ℝ≥0) : ℝ)).toNNReal x =
      turingSemigroup ((1 : ℝ≥0) : ℝ).toNNReal
        (turingSemigroup ((m : ℝ) * ((1 : ℝ≥0) : ℝ)).toNNReal x) := by
  have h : ((m : ℝ) + 1).toNNReal = 1 + (m : ℝ).toNNReal := by
    rw [Real.toNNReal_add (by positivity) zero_le_one, add_comm]; simp
  simp only [NNReal.coe_one, mul_one, Real.toNNReal_one, h,
    isC0Semigroup_turingSemigroup.map_add, ContinuousLinearMap.comp_apply]

/-- **Non-vacuity of `turing_instability_exists_escape`** on a diffusion-driven instability:
kinetics stable without diffusion (`tr J < 0 < det J`), the unstable Neumann mode `n = 1` on
`[0, π]` with `D = diag(1/4, 1/2)` (growth rate `1`, growth bound `ω = 1 < 2 · 1`), and the
stand-in linear flow `e^{t (J - D)}` (zero remainder). -/
example : ¬ IsUnstableMode turingJ (1 / 4) (1 / 2) 0 ∧ 0 < 1 ∧
    ∃ ε > 0, ∀ δ > 0, ∃ x : TuringSpace, ‖x - 0‖ < δ ∧
      ∃ t : ℝ, 0 ≤ t ∧ ε ≤ ‖turingSemigroup t.toNNReal x - 0‖ :=
  turing_instability_exists_escape (J := turingJ) (du := 1 / 4) (dv := 1 / 2) (L := Real.pi)
    (n := 1) trace_turingJ det_turingJ (by norm_num) (by norm_num) Real.pi_pos.le
    isUnstableMode_turingJ isC0Semigroup_turingSemigroup actsByModalODE_turingSemigroup
    norm_turingSemigroup_le (p := 2) (by norm_num) (by rw [growthRate_turingJ]; norm_num)
    (Φ := fun t x => turingSemigroup t.toNNReal x) (T := 1) (ρ := 1) (C := 0) one_pos one_pos
    le_rfl (fun x => by simp [isC0Semigroup_turingSemigroup.map_zero])
    (fun m x _ => turingSemigroup_step m x) (fun y _ => by simp)

/-! #### The mild formulation of the diffusion-driven example -/

/-- `e^{-t D}` with `D = diag(1/4, 1/2)`, acting pointwise, for all real `t`. -/
noncomputable def turingDiffOp (t : ℝ) : TuringSpace →L[ℝ] TuringSpace :=
  Real.exp (-(1 / 4) * t) • pointwiseMatrix _ (Matrix.diagonal ![1, 0]) +
    Real.exp (-(1 / 2) * t) • pointwiseMatrix _ (Matrix.diagonal ![0, 1])

theorem turingDiffOp_apply (t : ℝ) (y : TuringSpace) (x : Icc (0 : ℝ) Real.pi) :
    turingDiffOp t y x = Real.exp (-(1 / 4) * t) • (Matrix.diagonal ![1, 0] *ᵥ y x) +
      Real.exp (-(1 / 2) * t) • (Matrix.diagonal ![0, 1] *ᵥ y x) :=
  rfl

theorem continuous_turingDiffOp : Continuous turingDiffOp := by
  unfold turingDiffOp
  fun_prop

/-- The stand-in diffusion semigroup `e^{-t D}`, acting pointwise. It agrees with `e^{t D Δ_N}`
on the Neumann mode `n = 1` of `[0, π]` only (where `Δ_N = -1`). -/
noncomputable def turingDiffusion (t : ℝ≥0) : TuringSpace →L[ℝ] TuringSpace :=
  turingDiffOp t

theorem norm_turingDiffusion_le (t : ℝ≥0) :
    ‖turingDiffusion t‖ ≤ ‖pointwiseMatrix (Icc (0 : ℝ) Real.pi) (Matrix.diagonal ![1, 0])‖ +
      ‖pointwiseMatrix (Icc (0 : ℝ) Real.pi) (Matrix.diagonal ![0, 1])‖ := by
  have h1 : Real.exp (-(1 / 4) * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := t.coe_nonneg; linarith)
  have h2 : Real.exp (-(1 / 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := t.coe_nonneg; linarith)
  have hE₀ := ContinuousLinearMap.opNorm_smul_le (Real.exp (-(1 / 4) * (t : ℝ)))
    (pointwiseMatrix (Icc (0 : ℝ) Real.pi) (Matrix.diagonal ![1, 0]))
  have hE₁ := ContinuousLinearMap.opNorm_smul_le (Real.exp (-(1 / 2) * (t : ℝ)))
    (pointwiseMatrix (Icc (0 : ℝ) Real.pi) (Matrix.diagonal ![0, 1]))
  rw [Real.norm_of_nonneg (Real.exp_pos _).le] at hE₀ hE₁
  have h3 := mul_le_of_le_one_left (norm_nonneg
    (pointwiseMatrix (Icc (0 : ℝ) Real.pi) (Matrix.diagonal ![(1 : ℝ), 0]))) h1
  have h4 := mul_le_of_le_one_left (norm_nonneg
    (pointwiseMatrix (Icc (0 : ℝ) Real.pi) (Matrix.diagonal ![(0 : ℝ), 1]))) h2
  unfold turingDiffusion turingDiffOp
  refine (norm_add_le (E := TuringSpace →L[ℝ] TuringSpace) _ _).trans ?_
  linarith

theorem isC0Semigroup_turingDiffusion : IsC0Semigroup turingDiffusion where
  map_zero := by
    ext y x i
    fin_cases i <;> simp [turingDiffusion, turingDiffOp_apply, Matrix.mulVec_diagonal]
  map_add s t := by
    ext y x i
    have h1 : Real.exp (-(1 / 4) * ((s : ℝ) + t)) =
        Real.exp (-(1 / 4) * s) * Real.exp (-(1 / 4) * t) := by
      rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (-(1 / 2) * ((s : ℝ) + t)) =
        Real.exp (-(1 / 2) * s) * Real.exp (-(1 / 2) * t) := by
      rw [← Real.exp_add]; ring_nf
    simp only [turingDiffusion, NNReal.coe_add, ContinuousLinearMap.comp_apply, turingDiffOp_apply,
      h1, h2]
    fin_cases i <;> simp [Matrix.mulVec_diagonal] <;> ring
  continuous_apply y :=
    (continuous_turingDiffOp.comp NNReal.continuous_coe).clm_apply continuous_const
  locally_bounded _ := ⟨_, fun t _ => norm_turingDiffusion_le t⟩

/-- The orbits of `e^{t (J - D)}` are mild solutions of `w' = -D w + J w` for the diffusion
semigroup `e^{-t D}`: `S t y = e^{-t D} y + ∫₀ᵗ e^{-(t - s) D} J S s y ds`. -/
theorem isMildSolution_turingSemigroup (y : TuringSpace) (T : ℝ) :
    IsMildSolution turingDiffusion (pointwiseMatrix _ turingJ) y T
      fun t => turingSemigroup t.toNNReal y := by
  have hB : ∀ s, HasDerivAt (fun s => turingOp s y) (pointwiseMatrix _ turingM (turingOp s y))
      s := by
    intro s
    have h := ((Real.hasDerivAt_exp s).smul_const (pointwiseMatrix _ turingP y)).add
      ((((hasDerivAt_id s).const_mul (-2)).exp).smul_const (pointwiseMatrix _ turingQ y))
    refine h.congr_deriv ?_
    ext x i
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, turingOp_apply,
      pointwiseMatrix_apply]
    fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  have hcont : Continuous fun t : ℝ => turingSemigroup t.toNNReal y :=
    (isC0Semigroup_turingSemigroup.continuous_apply y).comp continuous_real_toNNReal
  refine ⟨hcont.continuousOn, fun t _ => ?_, fun t ht => ?_⟩
  · exact ((continuous_turingDiffOp.comp (NNReal.continuous_coe.comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id)))).clm_apply
      ((pointwiseMatrix _ turingJ).continuous.comp hcont)).intervalIntegrable 0 t
  · set g : ℝ → TuringSpace := fun s => turingDiffOp (t - s) (turingOp s y)
    have hg : ∀ s, HasDerivAt g (turingDiffOp (t - s) (pointwiseMatrix _ turingJ (turingOp s y)))
        s := by
      intro s
      -- `d/ds e^{-(t - s) D} v(s) = e^{-(t - s) D} (D v + (J - D) v) = e^{-(t - s) D} J v`
      have h1 := (((hasDerivAt_id s).const_sub t).const_mul (-(1 / 4) : ℝ)).exp
      have h2 := (((hasDerivAt_id s).const_sub t).const_mul (-(1 / 2) : ℝ)).exp
      have hE₀ := (pointwiseMatrix (Icc (0 : ℝ) Real.pi)
        (Matrix.diagonal ![(1 : ℝ), 0])).hasFDerivAt.comp_hasDerivAt s (hB s)
      have hE₁ := (pointwiseMatrix (Icc (0 : ℝ) Real.pi)
        (Matrix.diagonal ![(0 : ℝ), 1])).hasFDerivAt.comp_hasDerivAt s (hB s)
      refine ((h1.smul hE₀).add (h2.smul hE₁)).congr_deriv ?_
      ext x i
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, turingDiffOp_apply,
        pointwiseMatrix_apply, Function.comp_apply, turingOp_apply]
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    have hgc : Continuous fun s =>
        turingDiffOp (t - s) (pointwiseMatrix _ turingJ (turingOp s y)) :=
      (continuous_turingDiffOp.comp (continuous_const.sub continuous_id)).clm_apply
        ((pointwiseMatrix _ turingJ).continuous.comp
          (continuous_turingOp.clm_apply continuous_const))
    have hcongr : ∫ s in (0 : ℝ)..t, turingDiffusion (t - s).toNNReal
          (pointwiseMatrix _ turingJ (turingSemigroup s.toNNReal y)) =
        ∫ s in (0 : ℝ)..t, turingDiffOp (t - s) (pointwiseMatrix _ turingJ (turingOp s y)) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le ht.1] at hs
      simp only [turingDiffusion, turingSemigroup, Real.coe_toNNReal _ hs.1,
        Real.coe_toNNReal _ (sub_nonneg.2 hs.2)]
    simp only [duhamel]
    rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hg s)
      (hgc.intervalIntegrable 0 t)]
    have hgt : g t = turingOp t y := by
      ext x i
      fin_cases i <;> simp [g, turingDiffOp_apply, Matrix.mulVec_diagonal]
    have hg0 : g 0 = turingDiffOp t y := by
      ext x i
      simp only [g, sub_zero, turingDiffOp_apply, turingOp_apply]
      fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> ring
    rw [hgt, hg0]
    simp only [turingSemigroup, turingDiffusion, Real.coe_toNNReal _ ht.1]
    abel

/-- **Non-vacuity of `turing_instability_exists_escape_of_mild`** on the diffusion-driven
example: linear kinetics `f z = J z` (steady state `a = 0`, zero remainder of order `p = 2`),
stand-in diffusion semigroup `e^{-t D}`, stand-in linearized semigroup and flow
`e^{t (J - D)}`. -/
example : ¬ IsUnstableMode turingJ (1 / 4) (1 / 2) 0 ∧ 0 < 1 ∧
    ∃ ε > 0, ∀ δ > 0, ∃ x : TuringSpace, ‖x - ContinuousMap.const _ 0‖ < δ ∧
      ∃ t : ℝ, 0 ≤ t ∧ ε ≤ ‖turingSemigroup t.toNNReal x - ContinuousMap.const _ 0‖ := by
  have hfc : Continuous fun z : Fin 2 → ℝ => turingJ *ᵥ z := by fun_prop
  set A : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin turingJ)
  have hN : nemytskii (K := Icc (0 : ℝ) Real.pi) (fun z => turingJ *ᵥ z) hfc =
      ⇑(pointwiseMatrix _ turingJ) := by
    funext u; ext x i; rfl
  refine turing_instability_exists_escape_of_mild (J := turingJ) (du := 1 / 4) (dv := 1 / 2)
    (L := Real.pi) (n := 1) trace_turingJ det_turingJ (by norm_num) (by norm_num)
    Real.pi_pos.le isUnstableMode_turingJ hfc (fun _ => ⟨‖A‖₊, A.lipschitzWith.lipschitzOnWith⟩)
    (a := 0) (by simp) (r := 1) (K := 0) (p := 2) one_pos le_rfl (by norm_num)
    (fun z _ => by simp) (SA := turingDiffusion) (S := turingSemigroup)
    isC0Semigroup_turingDiffusion (fun t => by ext; simp) isC0Semigroup_turingSemigroup
    (T := 1) one_pos (fun y => isMildSolution_turingSemigroup y _)
    actsByModalODE_turingSemigroup norm_turingSemigroup_le
    (by rw [growthRate_turingJ]; norm_num) (Φ := fun t x => turingSemigroup t.toNNReal x)
    (ρ₀ := 1) (R := turingBound * Real.exp 1) one_pos
    (fun x => by simp [isC0Semigroup_turingSemigroup.map_zero])
    (fun m x _ => turingSemigroup_step m x)
    (fun x hx => ⟨hN ▸ isMildSolution_turingSemigroup x _, fun t ht => ?_⟩)
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  refine ((turingSemigroup _).le_opNorm x).trans ?_
  have hB : 0 ≤ turingBound := by positivity
  refine (mul_le_mul (norm_turingSemigroup_le _) hx' (norm_nonneg _) (by positivity)).trans ?_
  have : ((t.toNNReal : ℝ)) ≤ 1 := by
    rw [Real.coe_toNNReal _ ht.1]; simpa using ht.2
  rw [mul_one]
  gcongr
  simpa using this

end MathlibExtTest.Biology.Dynamics.TuringInstability
