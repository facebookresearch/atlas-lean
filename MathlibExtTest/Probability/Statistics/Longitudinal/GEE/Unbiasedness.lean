/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Longitudinal.GEE.Unbiasedness
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public section

set_option autoImplicit false

open Matrix MeasureTheory
open MathlibExt.Probability.Statistics.Longitudinal.GEE
open scoped ENNReal

namespace MathlibExtTest.Probability.Statistics.Longitudinal.GEE

/-! ### A fair coin -/

/-- A fair coin on `Bool`. -/
noncomputable def coin : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure coin :=
  ⟨by simp [coin, ← two_mul]; exact ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top⟩

theorem integral_coin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : Bool → E) : ∫ ω, f ω ∂coin = (2⁻¹ : ℝ) • (f true + f false) := by
  rw [coin, integral_smul_measure, integral_add_measure Integrable.of_finite Integrable.of_finite,
    integral_dirac, integral_dirac]
  simp

/-- The sign `±1` of the coin; mean `0`, variance `1`. -/
def sgn (ω : Bool) : ℝ := if ω then 1 else -1

/-! ### Smoke test: the Jacobian of a linear mean and one evaluation of `U` -/

/-- Design of a cluster of size two with an intercept only. -/
def ones2 : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => 1

example (β : Fin 1 → ℝ) : meanJacobian (fun b => ones2 *ᵥ b) β = ones2 :=
  meanJacobian_mulVec ones2 β

/-- With working independence, `U(β) = ∑ₜ (yₜ - β)` for an intercept-only model. -/
example (y : Fin 2 → ℝ) (b : ℝ) :
    geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => ones2 *ᵥ β) (fun _ _ => 1)
      (fun _ => y) (fun _ => b) 0 = y 0 + y 1 - 2 * b := by
  simp [geeEstFun, geeWeight, meanJacobian_mulVec, ones2, mulVec, dotProduct, Fin.sum_univ_two]

/-! ### Misspecified working covariance

`Y = s · (1, 1)` with a fair sign `s`, so `E[Y] = 0` and `Cov(Y)` is the all-ones matrix (perfect
within-cluster correlation, singular). The declared working covariance is the identity
(working independence), which is not `Cov(Y)`; `U(0)` is still unbiased. -/

/-- The response of the single cluster. -/
noncomputable def Ycorr (ω : Bool) : Fin 2 → ℝ := fun _ => sgn ω

theorem integral_Ycorr : ∫ ω, Ycorr ω ∂coin = ones2 *ᵥ (0 : Fin 1 → ℝ) := by
  ext t
  rw [eval_integral fun _ => Integrable.of_finite, integral_coin]
  simp [Ycorr, sgn]

/-- The true covariance has off-diagonal entry `E[Y₀ Y₁] = 1`, while the declared working
covariance `1` has off-diagonal entry `0`. -/
example : ∫ ω, Ycorr ω 0 * Ycorr ω 1 ∂coin = 1 ∧ (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
  refine ⟨?_, by simp⟩
  rw [integral_coin]
  norm_num [Ycorr, sgn]

/-- Unbiasedness at `β* = 0` under the misspecified working covariance `V = 1`. -/
example : ∫ ω, geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => ones2 *ᵥ β) (fun _ _ => 1)
    (fun _ => Ycorr ω) 0 ∂coin = 0 :=
  integral_geeEstFun_eq_zero (T := fun _ : Unit => Fin 2) _ _ (fun _ => Ycorr) 0
    (fun _ => Integrable.of_finite) fun _ => integral_Ycorr

/-- The same for any declared working covariance `V(β)`, including singular ones. -/
example (V : (Fin 1 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) :
    ∫ ω, geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => ones2 *ᵥ β) (fun _ => V)
      (fun _ => Ycorr ω) 0 ∂coin = 0 :=
  integral_geeEstFun_eq_zero (T := fun _ : Unit => Fin 2) _ _ (fun _ => Ycorr) 0
    (fun _ => Integrable.of_finite) fun _ => integral_Ycorr

/-- **Dependent clusters.** Two clusters with identical (perfectly dependent) responses:
unbiasedness does not need independence between clusters. -/
example : ∫ ω, geeEstFun (T := fun _ : Fin 2 => Fin 2) (fun _ β => ones2 *ᵥ β) (fun _ _ => 1)
    (fun _ => Ycorr ω) 0 ∂coin = 0 :=
  integral_geeEstFun_eq_zero (T := fun _ : Fin 2 => Fin 2) _ _ (fun _ => Ycorr) 0
    (fun _ => Integrable.of_finite) fun _ => integral_Ycorr

/-! ### One cluster (`n = 1`)

A single cluster with a single observation `Y ∈ {1/2, 3/2}` (fair coin, `E[Y] = 1`), log-linear
mean `μ(β) = e^β` and `V = 1`. The target is `β* = 0`. Unbiasedness of `U(β*)` holds, but the root
`β̂ = log Y` of `U` is a biased estimator: `E[log Y] = log(3/4) / 2 < 0`. -/

/-- The one-observation response. -/
noncomputable def Yone (ω : Bool) : Unit → ℝ := fun _ => if ω then 3 / 2 else 1 / 2

/-- The log-linear mean model. -/
noncomputable def expMean (β : Unit → ℝ) : Unit → ℝ := fun _ => Real.exp (β ())

theorem integral_Yone : ∫ ω, Yone ω ∂coin = expMean 0 := by
  ext t
  rw [eval_integral fun _ => Integrable.of_finite, integral_coin]
  norm_num [Yone, expMean]

/-- `E[U(β*)] = 0` with a single cluster. -/
example : ∫ ω, geeEstFun (T := fun _ : Unit => Unit) (fun _ => expMean) (fun _ _ => 1)
    (fun _ => Yone ω) 0 ∂coin = 0 :=
  integral_geeEstFun_eq_zero (T := fun _ : Unit => Unit) _ _ (fun _ => Yone) 0
    (fun _ => Integrable.of_finite) fun _ => integral_Yone

/-- `β̂ = log Y` is a root of `U`, whatever the Jacobian is. -/
theorem geeEstFun_log_Yone (ω : Bool) :
    geeEstFun (T := fun _ : Unit => Unit) (fun _ => expMean) (fun _ _ => 1)
      (fun _ => Yone ω) (fun _ => Real.log (Yone ω ())) = 0 := by
  have hpos : 0 < Yone ω () := by cases ω <;> norm_num [Yone]
  have h : Yone ω - expMean (fun _ => Real.log (Yone ω ())) = 0 := by
    ext u
    simp [expMean, Real.exp_log hpos]
  simp [geeEstFun, h]

/-- The root is biased: `E[log Y] = log(3/4) / 2 < 0 = β*`. -/
example : ∫ ω, Real.log (Yone ω ()) ∂coin < 0 := by
  rw [integral_coin]
  simp only [Yone, ite_true, Bool.false_eq_true, ite_false, smul_eq_mul]
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  have : Real.log (3 / 2 * (1 / 2) : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  linarith

/-! ### One small cluster: `β*` is not identified

One cluster with one observation `Y = s` (mean `0`) and two parameters, `μ(β) = β₀ + β₁`. Here
`DᵀV⁻¹D` is the singular all-ones matrix. `E[U(β)] = 0` holds at `β* = 0`, and equally at
`β = (1, -1)`: unbiasedness does not single out `β*`. -/

/-- The design row `(1, 1)`. -/
def row11 : Matrix Unit (Fin 2) ℝ := fun _ _ => 1

theorem integral_sgn_eq (β : Fin 2 → ℝ) (hβ : β 0 + β 1 = 0) :
    ∫ ω, (fun _ : Unit => sgn ω) ∂coin = row11 *ᵥ β := by
  ext u
  rw [eval_integral fun _ => Integrable.of_finite, integral_coin]
  simp [sgn, row11, mulVec, dotProduct, Fin.sum_univ_two, hβ]

example : ∃ β : Fin 2 → ℝ, β ≠ 0 ∧
    ∫ ω, geeEstFun (T := fun _ : Unit => Unit) (fun _ b => row11 *ᵥ b) (fun _ _ => 1)
      (fun _ _ => sgn ω) 0 ∂coin = 0 ∧
    ∫ ω, geeEstFun (T := fun _ : Unit => Unit) (fun _ b => row11 *ᵥ b) (fun _ _ => 1)
      (fun _ _ => sgn ω) β ∂coin = 0 := by
  refine ⟨![1, -1], fun h => by simpa using congrFun h 0, ?_, ?_⟩
  · exact integral_geeEstFun_eq_zero (T := fun _ : Unit => Unit) _ _
      (fun _ ω _ => sgn ω) 0 (fun _ => Integrable.of_finite)
      fun _ => integral_sgn_eq 0 (by simp)
  · exact integral_geeEstFun_eq_zero (T := fun _ : Unit => Unit) _ _
      (fun _ ω _ => sgn ω) ![1, -1] (fun _ => Integrable.of_finite)
      fun _ => integral_sgn_eq ![1, -1] (by simp)

/-! ### Incorrect mean

The response is deterministic, `Y = (1, 1)`, but the model is `μ(β) = β · (1, 2)` (no intercept),
so no `β` has `μ(β) = E[Y]`. Then `E[U(β)]` depends on the declared working covariance:
`3 - 5β` for `V = 1` and `3/2 - 2β` for `V = diag(1, 4)`. At `β* = 1`, where the first coordinate
is correct, `E[U(β*)] = -2 ≠ 0`, and no `β` makes both expectations vanish. -/

/-- The misspecified design `(1, 2)ᵀ`. -/
def x12 : Matrix (Fin 2) (Fin 1) ℝ := fun t _ => if t = 0 then 1 else 2

/-- The deterministic response `(1, 1)`. -/
def Yconst (_ : Bool) : Fin 2 → ℝ := fun _ => 1

theorem integral_geeEstFun_x12_one (b : ℝ) :
    ∫ ω, geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => x12 *ᵥ β) (fun _ _ => 1)
      (fun _ => Yconst ω) (fun _ => b) ∂coin = fun _ => 3 - 5 * b := by
  rw [integral_coin]
  ext k
  simp [geeEstFun, geeWeight, meanJacobian_mulVec, x12, Yconst, mulVec, dotProduct,
    Fin.sum_univ_two]
  ring

theorem inv_diagonal_one_four :
    (diagonal ![1, 4] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = diagonal ![1, 4⁻¹] := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem integral_geeEstFun_x12_diag (b : ℝ) :
    ∫ ω, geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => x12 *ᵥ β)
      (fun _ _ => diagonal ![1, 4]) (fun _ => Yconst ω) (fun _ => b) ∂coin =
      fun _ => 3 / 2 - 2 * b := by
  rw [integral_coin]
  ext k
  simp [geeEstFun, geeWeight, meanJacobian_mulVec, inv_diagonal_one_four, x12, Yconst, mulVec,
    dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
  ring

/-- At `β* = 1` the incorrect mean gives `E[U(β*)] ≠ 0`. -/
example : ∫ ω, geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => x12 *ᵥ β) (fun _ _ => 1)
    (fun _ => Yconst ω) (fun _ => 1) ∂coin ≠ 0 := by
  rw [integral_geeEstFun_x12_one]
  intro h
  have := congrFun h 0
  norm_num at this

/-- Under the incorrect mean, no `β` is a zero of the expected estimating function for both
declared working covariances: the "target" moves with `V`. -/
example : ¬ ∃ b : ℝ,
    ∫ ω, geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => x12 *ᵥ β) (fun _ _ => 1)
      (fun _ => Yconst ω) (fun _ => b) ∂coin = 0 ∧
    ∫ ω, geeEstFun (T := fun _ : Unit => Fin 2) (fun _ β => x12 *ᵥ β)
      (fun _ _ => diagonal ![1, 4]) (fun _ => Yconst ω) (fun _ => b) ∂coin = 0 := by
  rintro ⟨b, h1, h2⟩
  rw [integral_geeEstFun_x12_one] at h1
  rw [integral_geeEstFun_x12_diag] at h2
  have e1 := congrFun h1 0
  have e2 := congrFun h2 0
  simp only [Pi.zero_apply] at e1 e2
  linarith

end MathlibExtTest.Probability.Statistics.Longitudinal.GEE
