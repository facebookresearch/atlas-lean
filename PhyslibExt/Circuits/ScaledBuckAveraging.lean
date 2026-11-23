/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.AffinePWMErrorBound
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Scaled ideal-buck switched-to-averaged error bound

## i. Overview

An ideal buck converter in continuous conduction has inductance
`L > 0`, capacitance `C > 0`, load `R > 0` and constant input
voltage `Vin`; its inductor current `i` and capacitor voltage `v`
obey `L i' = s Vin - v` and `C v' = i - v / R`, with no diode clamp
and no state reset. In the state `x = (i, v)` this is the affine
system `x' = A x + s • b` with `A = [[0, -1/L], [1/C, -1/(R C)]]`
and `b = (Vin / L, 0)`.

The switched trajectory uses the pulse-width signal
`s = pwmSignal ε d` with switching-cycle length `ε > 0` and a duty
`d` with values in `[0, 1]` that is `Ld`-Lipschitz on `[0, T]`; the averaged
trajectory uses `d` itself. Both are continuous on `[0, T]` and are
given in integral-equation form there.

Amperes and volts are not combined in one norm directly. Declared
positive scales `Iref` and `Vref` give the dimensionless state
`z = (i / Iref, v / Vref)` with the sup norm, and the scaled system
`z' = Ã z + s • b̃` has `Ã = S⁻¹ A S` for `S = diag(Iref, Vref)` and
`b̃ = (Vin / (L Iref), 0)`. The affine PWM error bound applied to
`(Ã, b̃)` and translated back gives, for every `t ∈ [0, T]`,
`|i t - ī t| ≤ Iref * B` and `|v t - v̄ t| ≤ Vref * B` with
`B = exp(κ T) * (max(|Δi₀| / Iref, |Δv₀| / Vref)
  + |Vin| / (L Iref) * ε * (1 + Ld T / 2))`
and `κ = max(Vref/(L Iref), Iref/(C Vref) + 1/(R C))`, the largest
absolute row sum of `Ã`, which bounds its sup-norm operator norm.

The initial mismatch is kept in the bound. No hybrid or Zeno
dynamics, stability transfer, switching loss, dead time or
alternative diode-conduction topology is treated, and the factor
`exp(κ T)` makes the bound informative only over horizons of a few
`1 / κ`.

## ii. Key results

- `buck_switched_averaged_error_le`: the per-coordinate current and
  voltage bounds `Iref * B` and `Vref * B` on `[0, T]`.
- `buck_switched_averaged_error_le_of_constDuty`: a fixed duty `D`
  reduces the ripple term to `|Vin| / (L Iref) * (D (1 - D) ε)`, zero
  at `D = 0` and `D = 1`.
- `scaledState_switched_averaged_error_le`: the sup-norm bound on
  the scaled state, with the operator norm `‖Ã‖` in the exponent.
- `stateScaling_mul_scaledBuckMatrix`,
  `stateScaling_mulVec_scaledBuckInput`: `S Ã = A S` and `S b̃ = b`.
- `norm_scaledBuckOperator_le`: `‖Ã‖ ≤ κ`.

## iii. Table of contents

- A. Physical and scaled model data
- B. Model identities
- C. Norm computations
- D. Scaled integral equations
- E. Error bounds

## iv. References

- R. W. Erickson and D. Maksimović, *Fundamentals of Power
  Electronics*, third edition, Springer, 2020: the ideal buck
  converter and state-space averaging.
- R. D. Middlebrook and S. Ćuk, "A general unified approach to
  modelling switching-converter power stages", IEEE Power
  Electronics Specialists Conference, 1976.
-/

@[expose] public section

open MeasureTheory Set Matrix
open scoped NNReal

namespace PhyslibExt.Circuits.ScaledBuckAveraging

open MathlibExt.Analysis.ODE.PWMPrimitiveBound

/-! ## A. Physical and scaled model data -/

/-- State matrix of the ideal buck in the state `(i, v)`:
`A = [[0, -1/L], [1/C, -1/(R C)]]`. -/
noncomputable def buckMatrix (L C R : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -1 / L; 1 / C, -1 / (R * C)]

/-- Input direction of the ideal buck: `b = (Vin / L, 0)`. -/
noncomputable def buckInput (L Vin : ℝ) : Fin 2 → ℝ :=
  ![Vin / L, 0]

/-- Declared state scaling `S = diag(Iref, Vref)`. -/
def stateScaling (Iref Vref : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![Iref, Vref]

/-- Scaled state matrix `Ã = S⁻¹ A S`, written out entrywise. -/
noncomputable def scaledBuckMatrix (L C R Iref Vref : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, -Vref / (L * Iref); Iref / (C * Vref), -1 / (R * C)]

/-- Scaled input direction `b̃ = S⁻¹ b = (Vin / (L Iref), 0)`. -/
noncomputable def scaledBuckInput (L Vin Iref : ℝ) : Fin 2 → ℝ :=
  ![Vin / (L * Iref), 0]

/-- The scaled state matrix as a bounded operator on `Fin 2 → ℝ`
(sup norm). -/
noncomputable def scaledBuckOperator (L C R Iref Vref : ℝ) :
    (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (scaledBuckMatrix L C R Iref Vref))

/-- Dimensionless state `(i / Iref, v / Vref)`. -/
noncomputable def scaledState (Iref Vref i v : ℝ) : Fin 2 → ℝ :=
  ![i / Iref, v / Vref]

/-- Explicit growth rate `κ = max(Vref/(L Iref), Iref/(C Vref) + 1/(R C))`,
the largest absolute row sum of `Ã`. -/
noncomputable def scaledBuckGrowthRate (L C R Iref Vref : ℝ) : ℝ :=
  max (Vref / (L * Iref)) (Iref / (C * Vref) + 1 / (R * C))

/-- Dimensionless error bound
`B = exp(κ T) * (max(|Δi₀| / Iref, |Δv₀| / Vref) + |Vin| / (L Iref) * ε * (1 + Ld T / 2))`. -/
noncomputable def scaledBuckErrorBound (L C R Vin Iref Vref T ε Ld Δi₀ Δv₀ : ℝ) : ℝ :=
  Real.exp (scaledBuckGrowthRate L C R Iref Vref * T) *
    (max (|Δi₀| / Iref) (|Δv₀| / Vref) + |Vin| / (L * Iref) * ε * (1 + Ld * T / 2))

/-! ## B. Model identities -/

/-- The linear form reproduces the two-state laws: the `i` row is
`(s Vin - v) / L` and the `v` row is `(i - v / R) / C`. -/
lemma buckMatrix_mulVec_add_smul_buckInput (L C R Vin s i v : ℝ) :
    buckMatrix L C R *ᵥ ![i, v] + s • buckInput L Vin =
      ![(s * Vin - v) / L, (i - v / R) / C] := by
  ext j
  fin_cases j <;> simp [buckMatrix, buckInput] <;> ring

/-- The scaled matrix is the conjugate of the buck matrix by the
declared scaling: `S Ã = A S`. -/
lemma stateScaling_mul_scaledBuckMatrix (L C R Iref Vref : ℝ)
    (hI : Iref ≠ 0) (hV : Vref ≠ 0) :
    stateScaling Iref Vref * scaledBuckMatrix L C R Iref Vref =
      buckMatrix L C R * stateScaling Iref Vref := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateScaling, scaledBuckMatrix, buckMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp

/-- The scaled input is the scaled-back buck input: `S b̃ = b`. -/
lemma stateScaling_mulVec_scaledBuckInput (L Vin Iref Vref : ℝ) (hI : Iref ≠ 0) :
    stateScaling Iref Vref *ᵥ scaledBuckInput L Vin Iref = buckInput L Vin := by
  ext j
  fin_cases j <;>
    simp [stateScaling, scaledBuckInput, buckInput, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]
  field_simp

/-- The scaled operator acts by the scaled matrix. -/
lemma scaledBuckOperator_apply (L C R Iref Vref : ℝ) (z : Fin 2 → ℝ) :
    scaledBuckOperator L C R Iref Vref z = scaledBuckMatrix L C R Iref Vref *ᵥ z := by
  rfl

/-- In scaled coordinates the two-state right-hand sides read
`Ã z + s • b̃`. -/
lemma scaledBuckOperator_scaledState_add (L C R Vin Iref Vref s i v : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hI : 0 < Iref) (hV : 0 < Vref) :
    scaledBuckOperator L C R Iref Vref (scaledState Iref Vref i v) +
        s • scaledBuckInput L Vin Iref =
      ![((s * Vin - v) / L) / Iref, ((i - v / R) / C) / Vref] := by
  rw [scaledBuckOperator_apply]
  ext j
  fin_cases j <;>
    simp [scaledBuckMatrix, scaledState, scaledBuckInput] <;>
    field_simp <;> ring

/-! ## C. Norm computations -/

/-- The sup norm on `Fin 2 → ℝ` is the larger absolute coordinate. -/
private lemma norm_fin_two_eq_max (x : Fin 2 → ℝ) : ‖x‖ = max |x 0| |x 1| := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (le_max_of_le_left (abs_nonneg _))).2
    fun j => ?_) (max_le ?_ ?_)
  · fin_cases j
    · simp [Real.norm_eq_abs]
    · simp [Real.norm_eq_abs]
  · simpa [Real.norm_eq_abs] using norm_le_pi_norm x 0
  · simpa [Real.norm_eq_abs] using norm_le_pi_norm x 1

/-- The sup-norm operator norm of `Ã` is at most `κ`. -/
lemma norm_scaledBuckOperator_le (L C R Iref Vref : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (hI : 0 < Iref) (hV : 0 < Vref) :
    ‖scaledBuckOperator L C R Iref Vref‖ ≤ scaledBuckGrowthRate L C R Iref Vref := by
  have ha : 0 ≤ Vref / (L * Iref) := by positivity
  have hb : 0 ≤ Iref / (C * Vref) := by positivity
  have hc : 0 ≤ 1 / (R * C) := by positivity
  have hk1 : Vref / (L * Iref) ≤ scaledBuckGrowthRate L C R Iref Vref := le_max_left _ _
  have hk2 : Iref / (C * Vref) + 1 / (R * C) ≤ scaledBuckGrowthRate L C R Iref Vref :=
    le_max_right _ _
  have hκ0 : 0 ≤ scaledBuckGrowthRate L C R Iref Vref := ha.trans hk1
  refine ContinuousLinearMap.opNorm_le_bound _ hκ0 fun z => ?_
  have h0 : |z 0| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z 0
  have h1 : |z 1| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z 1
  have hz : scaledBuckOperator L C R Iref Vref z =
      ![-(Vref / (L * Iref)) * z 1, Iref / (C * Vref) * z 0 - 1 / (R * C) * z 1] := by
    rw [scaledBuckOperator_apply]
    ext j
    fin_cases j <;>
      simp [scaledBuckMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [norm_fin_two_eq_max, hz]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine max_le ?_ ?_
  · rw [abs_mul, abs_neg, abs_of_nonneg ha]
    nlinarith [norm_nonneg z]
  · calc |Iref / (C * Vref) * z 0 - 1 / (R * C) * z 1|
        ≤ |Iref / (C * Vref) * z 0| + |1 / (R * C) * z 1| := abs_sub _ _
      _ = Iref / (C * Vref) * |z 0| + 1 / (R * C) * |z 1| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
      _ ≤ (Iref / (C * Vref) + 1 / (R * C)) * ‖z‖ := by nlinarith
      _ ≤ scaledBuckGrowthRate L C R Iref Vref * ‖z‖ := by nlinarith [norm_nonneg z]

/-- The scaled input has sup norm `|Vin| / (L Iref)`. -/
lemma norm_scaledBuckInput (L Vin Iref : ℝ) (hL : 0 < L) (hI : 0 < Iref) :
    ‖scaledBuckInput L Vin Iref‖ = |Vin| / (L * Iref) := by
  rw [norm_fin_two_eq_max]
  simp only [scaledBuckInput, Matrix.cons_val_zero, Matrix.cons_val_one, abs_zero]
  rw [max_eq_left (abs_nonneg _), abs_div, abs_of_pos (mul_pos hL hI)]

/-- The sup norm of a scaled state difference is the larger of the
two scaled coordinate differences. -/
lemma norm_scaledState_sub (Iref Vref i v i' v' : ℝ) (hI : 0 < Iref) (hV : 0 < Vref) :
    ‖scaledState Iref Vref i v - scaledState Iref Vref i' v'‖ =
      max (|i - i'| / Iref) (|v - v'| / Vref) := by
  rw [norm_fin_two_eq_max]
  simp only [scaledState, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← sub_div, ← sub_div, abs_div, abs_div, abs_of_pos hI, abs_of_pos hV]

/-! ## D. Scaled integral equations -/

/-- Coordinate integral equations with continuous states and an
integrable switching function give the vector integral equation of
the scaled state `z' = Ã z + s • b̃` on `[0, T]`. -/
lemma scaledState_integral_eq (L C R Vin Iref Vref T : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (hI : 0 < Iref) (hV : 0 < Vref) (hT : 0 ≤ T)
    (s i v : ℝ → ℝ) (i₀ v₀ : ℝ)
    (hs : IntervalIntegrable s volume 0 T)
    (hi_cont : ContinuousOn i (Set.Icc 0 T)) (hv_cont : ContinuousOn v (Set.Icc 0 T))
    (hi : ∀ t ∈ Set.Icc 0 T, i t = i₀ + ∫ u in (0 : ℝ)..t, (s u * Vin - v u) / L)
    (hv : ∀ t ∈ Set.Icc 0 T, v t = v₀ + ∫ u in (0 : ℝ)..t, (i u - v u / R) / C)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    scaledState Iref Vref (i t) (v t) =
      scaledState Iref Vref i₀ v₀ +
        ∫ u in (0 : ℝ)..t, (scaledBuckOperator L C R Iref Vref
            (scaledState Iref Vref (i u) (v u)) + (s u) • scaledBuckInput L Vin Iref) := by
  have hsub : uIcc 0 t ⊆ Icc 0 T := by
    rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2
  have hsub' : uIcc 0 t ⊆ uIcc 0 T := by rw [uIcc_of_le hT]; exact hsub
  have hst : IntervalIntegrable s volume 0 t := hs.mono_set hsub'
  have hvt : IntervalIntegrable v volume 0 t := (hv_cont.mono hsub).intervalIntegrable
  have hit : IntervalIntegrable i volume 0 t := (hi_cont.mono hsub).intervalIntegrable
  have hg0 : IntervalIntegrable (fun u => (s u * Vin - v u) / L / Iref) volume 0 t :=
    (((hst.mul_const Vin).sub hvt).div_const L).div_const Iref
  have hg1 : IntervalIntegrable (fun u => (i u - v u / R) / C / Vref) volume 0 t :=
    ((hit.sub (hvt.div_const R)).div_const C).div_const Vref
  have hsm : ∀ {g : ℝ → ℝ} (e : Fin 2 → ℝ), IntervalIntegrable g volume 0 t →
      IntervalIntegrable (fun u => g u • e) volume 0 t := fun e h =>
    ⟨h.1.smul_const e, h.2.smul_const e⟩
  have hf : (fun u => scaledBuckOperator L C R Iref Vref (scaledState Iref Vref (i u) (v u)) +
      s u • scaledBuckInput L Vin Iref) = fun u =>
        ((s u * Vin - v u) / L / Iref) • (![1, 0] : Fin 2 → ℝ) +
          ((i u - v u / R) / C / Vref) • (![0, 1] : Fin 2 → ℝ) := by
    funext u
    rw [scaledBuckOperator_scaledState_add L C R Vin Iref Vref (s u) (i u) (v u) hL hC hI hV]
    ext j
    fin_cases j <;> simp
  rw [hf, intervalIntegral.integral_add (hsm _ hg0) (hsm _ hg1),
    intervalIntegral.integral_smul_const, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_div, intervalIntegral.integral_div, hi t ht, hv t ht]
  ext j
  fin_cases j <;> simp [scaledState] <;> ring

/-! ## E. Error bounds -/

/-- Scaled-state bound: the affine PWM bound instantiated at
`(Ã, b̃)` with zero common forcing. -/
lemma scaledState_switched_averaged_error_le (L C R Vin Iref Vref : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (hI : 0 < Iref) (hV : 0 < Vref)
    (T ε : ℝ) (Ld : ℝ≥0) (d : ℝ → ℝ) (hT : 0 ≤ T) (hε : 0 < ε)
    (hd : ∀ t ∈ Set.Icc 0 T, d t ∈ Set.Icc 0 1)
    (hLip : LipschitzOnWith Ld d (Set.Icc 0 T))
    (i v iAvg vAvg : ℝ → ℝ) (i₀ v₀ iAvg₀ vAvg₀ : ℝ)
    (hi_cont : ContinuousOn i (Set.Icc 0 T)) (hv_cont : ContinuousOn v (Set.Icc 0 T))
    (hiAvg_cont : ContinuousOn iAvg (Set.Icc 0 T))
    (hvAvg_cont : ContinuousOn vAvg (Set.Icc 0 T))
    (hi : ∀ t ∈ Set.Icc 0 T,
      i t = i₀ + ∫ u in (0 : ℝ)..t, (pwmSignal ε d u * Vin - v u) / L)
    (hv : ∀ t ∈ Set.Icc 0 T, v t = v₀ + ∫ u in (0 : ℝ)..t, (i u - v u / R) / C)
    (hiAvg : ∀ t ∈ Set.Icc 0 T,
      iAvg t = iAvg₀ + ∫ u in (0 : ℝ)..t, (d u * Vin - vAvg u) / L)
    (hvAvg : ∀ t ∈ Set.Icc 0 T,
      vAvg t = vAvg₀ + ∫ u in (0 : ℝ)..t, (iAvg u - vAvg u / R) / C)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    ‖scaledState Iref Vref (i t) (v t) - scaledState Iref Vref (iAvg t) (vAvg t)‖ ≤
      Real.exp (‖scaledBuckOperator L C R Iref Vref‖ * T) *
        (‖scaledState Iref Vref i₀ v₀ - scaledState Iref Vref iAvg₀ vAvg₀‖ +
          ‖scaledBuckInput L Vin Iref‖ * ε * (1 + (Ld : ℝ) * T / 2)) := by
  have hdi : IntervalIntegrable d volume 0 T :=
    (hLip.continuousOn.mono (by rw [uIcc_of_le hT])).intervalIntegrable
  have hsi : IntervalIntegrable (pwmSignal ε d) volume 0 T :=
    intervalIntegrable_pwmSignal ε d 0 T
  refine MathlibExt.Analysis.ODE.AffinePWMErrorBound.switched_averaged_error_le
    (scaledBuckOperator L C R Iref Vref) (scaledBuckInput L Vin Iref) 0 continuous_const
    T ε Ld d hT hε hd hLip (fun t => scaledState Iref Vref (i t) (v t))
    (fun t => scaledState Iref Vref (iAvg t) (vAvg t))
    (scaledState Iref Vref i₀ v₀) (scaledState Iref Vref iAvg₀ vAvg₀) ?_ ?_ t ht
  · intro t ht
    simp only [Pi.zero_apply, add_zero]
    exact scaledState_integral_eq L C R Vin Iref Vref T hL hC hR hI hV hT (pwmSignal ε d) i v
      i₀ v₀ hsi hi_cont hv_cont hi hv t ht
  · intro t ht
    simp only [Pi.zero_apply, add_zero]
    exact scaledState_integral_eq L C R Vin Iref Vref T hL hC hR hI hV hT d iAvg vAvg
      iAvg₀ vAvg₀ hdi hiAvg_cont hvAvg_cont hiAvg hvAvg t ht

/-- A scaled-state bound with ripple factor `Q ≥ 0` translates into the
per-coordinate current and voltage bounds, with `‖Ã‖` replaced by `κ`. -/
private lemma coord_error_le_of_scaledState_error_le (L C R Vin Iref Vref T Q : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (hI : 0 < Iref) (hV : 0 < Vref) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (i v i' v' i₀ v₀ i₀' v₀' : ℝ)
    (h : ‖scaledState Iref Vref i v - scaledState Iref Vref i' v'‖ ≤
      Real.exp (‖scaledBuckOperator L C R Iref Vref‖ * T) *
        (‖scaledState Iref Vref i₀ v₀ - scaledState Iref Vref i₀' v₀'‖ +
          ‖scaledBuckInput L Vin Iref‖ * Q)) :
    |i - i'| ≤
        Iref * (Real.exp (scaledBuckGrowthRate L C R Iref Vref * T) *
          (max (|i₀ - i₀'| / Iref) (|v₀ - v₀'| / Vref) + |Vin| / (L * Iref) * Q)) ∧
      |v - v'| ≤
        Vref * (Real.exp (scaledBuckGrowthRate L C R Iref Vref * T) *
          (max (|i₀ - i₀'| / Iref) (|v₀ - v₀'| / Vref) + |Vin| / (L * Iref) * Q)) := by
  rw [norm_scaledState_sub _ _ _ _ _ _ hI hV, norm_scaledState_sub _ _ _ _ _ _ hI hV,
    norm_scaledBuckInput L Vin Iref hL hI] at h
  have hop := norm_scaledBuckOperator_le L C R Iref Vref hL hC hR hI hV
  have hin : 0 ≤ max (|i₀ - i₀'| / Iref) (|v₀ - v₀'| / Vref) + |Vin| / (L * Iref) * Q :=
    add_nonneg (le_max_of_le_left (by positivity)) (mul_nonneg (by positivity) hQ)
  have hexp : Real.exp (‖scaledBuckOperator L C R Iref Vref‖ * T) ≤
      Real.exp (scaledBuckGrowthRate L C R Iref Vref * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hop hT)
  have hB := h.trans (mul_le_mul_of_nonneg_right hexp hin)
  constructor
  · have h1 := (le_max_left _ _).trans hB
    rw [div_le_iff₀ hI] at h1
    linarith
  · have h1 := (le_max_right _ _).trans hB
    rw [div_le_iff₀ hV] at h1
    linarith

/-- **Scaled ideal-buck averaging bound.** Under the hypotheses above,
the switched and averaged inductor currents differ by at most
`Iref * B` and the capacitor voltages by at most `Vref * B` at every
`t ∈ [0, T]`, with `B = scaledBuckErrorBound`. -/
lemma buck_switched_averaged_error_le (L C R Vin Iref Vref : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (hI : 0 < Iref) (hV : 0 < Vref)
    (T ε : ℝ) (Ld : ℝ≥0) (d : ℝ → ℝ) (hT : 0 ≤ T) (hε : 0 < ε)
    (hd : ∀ t ∈ Set.Icc 0 T, d t ∈ Set.Icc 0 1)
    (hLip : LipschitzOnWith Ld d (Set.Icc 0 T))
    (i v iAvg vAvg : ℝ → ℝ) (i₀ v₀ iAvg₀ vAvg₀ : ℝ)
    (hi_cont : ContinuousOn i (Set.Icc 0 T)) (hv_cont : ContinuousOn v (Set.Icc 0 T))
    (hiAvg_cont : ContinuousOn iAvg (Set.Icc 0 T))
    (hvAvg_cont : ContinuousOn vAvg (Set.Icc 0 T))
    (hi : ∀ t ∈ Set.Icc 0 T,
      i t = i₀ + ∫ u in (0 : ℝ)..t, (pwmSignal ε d u * Vin - v u) / L)
    (hv : ∀ t ∈ Set.Icc 0 T, v t = v₀ + ∫ u in (0 : ℝ)..t, (i u - v u / R) / C)
    (hiAvg : ∀ t ∈ Set.Icc 0 T,
      iAvg t = iAvg₀ + ∫ u in (0 : ℝ)..t, (d u * Vin - vAvg u) / L)
    (hvAvg : ∀ t ∈ Set.Icc 0 T,
      vAvg t = vAvg₀ + ∫ u in (0 : ℝ)..t, (iAvg u - vAvg u / R) / C)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    |i t - iAvg t| ≤
        Iref * scaledBuckErrorBound L C R Vin Iref Vref T ε Ld (i₀ - iAvg₀) (v₀ - vAvg₀) ∧
      |v t - vAvg t| ≤
        Vref * scaledBuckErrorBound L C R Vin Iref Vref T ε Ld (i₀ - iAvg₀) (v₀ - vAvg₀) := by
  have h := scaledState_switched_averaged_error_le L C R Vin Iref Vref hL hC hR hI hV T ε Ld d
    hT hε hd hLip i v iAvg vAvg i₀ v₀ iAvg₀ vAvg₀ hi_cont hv_cont hiAvg_cont hvAvg_cont
    hi hv hiAvg hvAvg t ht
  rw [mul_assoc ‖scaledBuckInput L Vin Iref‖] at h
  unfold scaledBuckErrorBound
  rw [mul_assoc (|Vin| / (L * Iref))]
  exact coord_error_le_of_scaledState_error_le L C R Vin Iref Vref T _ hL hC hR hI hV hT
    (by positivity) _ _ _ _ _ _ _ _ h

/-- Fixed duty `D ∈ [0, 1]`: the ripple term reduces to
`|Vin| / (L Iref) * (D (1 - D) ε)`, which vanishes at `D = 0` and
`D = 1`, where the pulse-width signal equals the duty. -/
lemma buck_switched_averaged_error_le_of_constDuty (L C R Vin Iref Vref : ℝ)
    (hL : 0 < L) (hC : 0 < C) (hR : 0 < R) (hI : 0 < Iref) (hV : 0 < Vref)
    (T ε D : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) (hD : D ∈ Set.Icc 0 1)
    (i v iAvg vAvg : ℝ → ℝ) (i₀ v₀ iAvg₀ vAvg₀ : ℝ)
    (hi_cont : ContinuousOn i (Set.Icc 0 T)) (hv_cont : ContinuousOn v (Set.Icc 0 T))
    (hiAvg_cont : ContinuousOn iAvg (Set.Icc 0 T))
    (hvAvg_cont : ContinuousOn vAvg (Set.Icc 0 T))
    (hi : ∀ t ∈ Set.Icc 0 T,
      i t = i₀ + ∫ u in (0 : ℝ)..t, (pwmSignal ε (fun _ => D) u * Vin - v u) / L)
    (hv : ∀ t ∈ Set.Icc 0 T, v t = v₀ + ∫ u in (0 : ℝ)..t, (i u - v u / R) / C)
    (hiAvg : ∀ t ∈ Set.Icc 0 T,
      iAvg t = iAvg₀ + ∫ u in (0 : ℝ)..t, (D * Vin - vAvg u) / L)
    (hvAvg : ∀ t ∈ Set.Icc 0 T,
      vAvg t = vAvg₀ + ∫ u in (0 : ℝ)..t, (iAvg u - vAvg u / R) / C)
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    |i t - iAvg t| ≤
        Iref * (Real.exp (scaledBuckGrowthRate L C R Iref Vref * T) *
          (max (|i₀ - iAvg₀| / Iref) (|v₀ - vAvg₀| / Vref) +
            |Vin| / (L * Iref) * (D * (1 - D) * ε))) ∧
      |v t - vAvg t| ≤
        Vref * (Real.exp (scaledBuckGrowthRate L C R Iref Vref * T) *
          (max (|i₀ - iAvg₀| / Iref) (|v₀ - vAvg₀| / Vref) +
            |Vin| / (L * Iref) * (D * (1 - D) * ε))) := by
  refine coord_error_le_of_scaledState_error_le L C R Vin Iref Vref T _ hL hC hR hI hV hT
    (mul_nonneg (mul_nonneg hD.1 (sub_nonneg.2 hD.2)) hε.le) _ _ _ _ _ _ _ _
    (MathlibExt.Analysis.ODE.AffinePWMErrorBound.switched_averaged_error_le_of_constDuty_sharp
      (scaledBuckOperator L C R Iref Vref) (scaledBuckInput L Vin Iref) 0 continuous_const
      T ε D hT hε hD (fun t => scaledState Iref Vref (i t) (v t))
      (fun t => scaledState Iref Vref (iAvg t) (vAvg t))
      (scaledState Iref Vref i₀ v₀) (scaledState Iref Vref iAvg₀ vAvg₀) ?_ ?_ t ht)
  · intro t ht
    simp only [Pi.zero_apply, add_zero]
    exact scaledState_integral_eq L C R Vin Iref Vref T hL hC hR hI hV hT
      (pwmSignal ε fun _ => D) i v i₀ v₀ (intervalIntegrable_pwmSignal ε _ 0 T)
      hi_cont hv_cont hi hv t ht
  · intro t ht
    simp only [Pi.zero_apply, add_zero]
    exact scaledState_integral_eq L C R Vin Iref Vref T hL hC hR hI hV hT
      (fun _ => D) iAvg vAvg iAvg₀ vAvg₀ intervalIntegrable_const
      hiAvg_cont hvAvg_cont hiAvg hvAvg t ht

end PhyslibExt.Circuits.ScaledBuckAveraging
