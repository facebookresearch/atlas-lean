/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Sequential Kalman conditioning over observation histories (G06)

Two-observation scalar specialization: for `x1 = F * x0 + w`,
`y0 = H0 * x0 + v0`, `y1 = H1 * x1 + v1`, with prior variance `P0 ≥ 0`,
process variance `Q ≥ 0`, and observation variances `R0, R1 > 0`, the
recursively computed Kalman belief after the two observations (update,
predict, update) equals the one-shot joint Gaussian conditioning of
the final state `x1` given the whole observation history `(y0, y1)`,
by the Schur-complement formulas.

This is explicitly the two-observation scalar case with general
parameters, not the general-horizon matrix case: the batch formulas
use the joint covariance of the whole history, and the proof verifies
the recursive steps reproduce exactly that joint conditioning rather
than chaining an unconditional one-step theorem. The law-level
statement (the recursive belief's law is a version of
`condDistrib x1 (y0, y1)`) follows in a consumer from these parameters
plus the fact that a Gaussian law is determined by its mean and
covariance, and is not proved in this file.

## Key results

- `g06_recursive_eq_batch`: recursive belief = batch conditioning.
-/

@[expose] public section

open Matrix

namespace Cslib.MachineLearning.Sequence.G06KalmanHistory

/-- Scalar Kalman predict step: `(m, P) ↦ (F * m, F^2 * P + Q)`. -/
noncomputable def g06Predict (F Q : ℝ) (b : ℝ × ℝ) : ℝ × ℝ :=
  (F * b.1, F ^ 2 * b.2 + Q)

/-- Scalar Kalman update step with observation `y`: gain
`K = P * H / (H^2 * P + R)`, mean `m + K * (y - H * m)`,
covariance `(1 - K * H) * P`. -/
noncomputable def g06Update (H R : ℝ) (b : ℝ × ℝ) (y : ℝ) : ℝ × ℝ :=
  (b.1 + (b.2 * H / (H ^ 2 * b.2 + R)) * (y - H * b.1),
    (1 - (b.2 * H / (H ^ 2 * b.2 + R)) * H) * b.2)

/-- Recursive Kalman belief for the final state `x1`: update with `y0`
on `x0`, predict to `x1`, update with `y1` on `x1`. -/
noncomputable def g06Recursive (F Q H0 H1 R0 R1 : ℝ) (b0 : ℝ × ℝ)
    (y0 y1 : ℝ) : ℝ × ℝ :=
  g06Update H1 R1 (g06Predict F Q (g06Update H0 R0 b0 y0)) y1

/-- Prior mean of the final state `x1 = F * x0 + w`. -/
noncomputable def g06BatchMeanX (F : ℝ) (m0 : ℝ) : ℝ :=
  F * m0

/-- Prior variance of `x1`: `F^2 * P0 + Q`. -/
noncomputable def g06BatchVarX (F Q P0 : ℝ) : ℝ :=
  F ^ 2 * P0 + Q

/-- Prior mean of the observation pair `(y0, y1)`. -/
noncomputable def g06BatchMeanY (F H0 H1 : ℝ) (m0 : ℝ) : Fin 2 → ℝ :=
  ![H0 * m0, H1 * (F * m0)]

/-- Covariance matrix of the observation pair `(y0, y1)`:
`Var(y0) = H0^2 P0 + R0`,
`Cov(y0, y1) = H0 * H1 * F * P0`,
`Var(y1) = H1^2 * (F^2 * P0 + Q) + R1`. -/
noncomputable def g06BatchCovY (F H0 H1 R0 R1 Q P0 : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![H0 ^ 2 * P0 + R0, H0 * H1 * F * P0;
      H0 * H1 * F * P0, H1 ^ 2 * (F ^ 2 * P0 + Q) + R1]

/-- Cross-covariance vector `Cov(x1, (y0, y1))`:
`Cov(x1, y0) = F * H0 * P0`,
`Cov(x1, y1) = H1 * (F^2 * P0 + Q)`. -/
noncomputable def g06BatchCovXY (F H0 H1 Q P0 : ℝ) : Fin 2 → ℝ :=
  ![F * H0 * P0, H1 * (F ^ 2 * P0 + Q)]

/-- Batch (joint) Gaussian conditioning: conditional mean of `x1`
given `(y0, y1)`, by the Schur-complement formula. -/
noncomputable def g06BatchMean (F H0 H1 R0 R1 Q P0 m0 : ℝ)
    (y : Fin 2 → ℝ) : ℝ :=
  g06BatchMeanX F m0 +
    (g06BatchCovXY F H0 H1 Q P0) ⬝ᵥ
      ((g06BatchCovY F H0 H1 R0 R1 Q P0)⁻¹ *ᵥ
        (y - g06BatchMeanY F H0 H1 m0))

/-- Batch (joint) Gaussian conditioning: conditional variance of `x1`
given `(y0, y1)`, by the Schur-complement formula. -/
noncomputable def g06BatchVar (F H0 H1 R0 R1 Q P0 : ℝ) : ℝ :=
  g06BatchVarX F Q P0 -
    (g06BatchCovXY F H0 H1 Q P0) ⬝ᵥ
      ((g06BatchCovY F H0 H1 R0 R1 Q P0)⁻¹ *ᵥ
        (g06BatchCovXY F H0 H1 Q P0))


/-- Innovation variance `H^2 * P + R` is positive for `P ≥ 0`, `R > 0`. -/
lemma g06_innov_pos (H R P : ℝ) (hP : 0 ≤ P) (hR : 0 < R) :
    0 < H ^ 2 * P + R := by
  have h := mul_nonneg (sq_nonneg H) hP
  linarith

/-- Updated variance in closed form: `(1 - K * H) * P = R * P / S`. -/
lemma g06_update_var_eq (H R P : ℝ) (hS : H ^ 2 * P + R ≠ 0) :
    (1 - (P * H / (H ^ 2 * P + R)) * H) * P
      = R * P / (H ^ 2 * P + R) := by
  have hS2 : P * H ^ 2 + R ≠ 0 := by
    have h : P * H ^ 2 + R = H ^ 2 * P + R := by ring
    rwa [h]
  field_simp
  ring

/-- Joint observation covariance determinant is positive: the `P0^2`
terms cancel, leaving `R0 * R1` plus nonnegative terms. -/
lemma g06_det_pos (F H0 H1 R0 R1 Q P0 : ℝ) (hP0 : 0 ≤ P0) (hQ : 0 ≤ Q)
    (hR0 : 0 < R0) (hR1 : 0 < R1) :
    0 < (H0 ^ 2 * P0 + R0) * (H1 ^ 2 * (F ^ 2 * P0 + Q) + R1)
      - H0 * H1 * F * P0 * (H0 * H1 * F * P0) := by
  have heq : (H0 ^ 2 * P0 + R0) * (H1 ^ 2 * (F ^ 2 * P0 + Q) + R1)
        - H0 * H1 * F * P0 * (H0 * H1 * F * P0)
      = R0 * R1 + (R0 * (H1 ^ 2 * (F ^ 2 * P0 + Q))
        + R1 * (H0 ^ 2 * P0) + (H0 * H1) ^ 2 * P0 * Q) := by
    ring
  rw [heq]
  have h1 : 0 < R0 * R1 := mul_pos hR0 hR1
  have h2 : 0 ≤ R0 * (H1 ^ 2 * (F ^ 2 * P0 + Q)) := by positivity
  have h3 : 0 ≤ R1 * (H0 ^ 2 * P0) := by positivity
  have h4 : 0 ≤ (H0 * H1) ^ 2 * P0 * Q := by positivity
  linarith

/-- Two-observation specialization of sequential Kalman conditioning
(scalar case, general parameters): the recursively computed belief
after two observations equals the one-shot joint Gaussian conditioning
of the final state given the whole observation history. States:
`x1 = F * x0 + w`, `y0 = H0 * x0 + v0`, `y1 = H1 * x1 + v1`.
The observation-noise variances are positive (so both innovation
variances and the joint observation covariance are invertible), the
prior and process variances are nonnegative. -/
theorem g06_recursive_eq_batch (F Q H0 H1 R0 R1 : ℝ) (b0 : ℝ × ℝ)
    (y0 y1 : ℝ) (hP0 : 0 ≤ b0.2) (hQ : 0 ≤ Q)
    (hR0 : 0 < R0) (hR1 : 0 < R1) :
    g06Recursive F Q H0 H1 R0 R1 b0 y0 y1 =
      (g06BatchMean F H0 H1 R0 R1 Q b0.2 b0.1 ![y0, y1],
        g06BatchVar F H0 H1 R0 R1 Q b0.2) := by
  have hS0 : 0 < H0 ^ 2 * b0.2 + R0 :=
    g06_innov_pos H0 R0 b0.2 hP0 hR0
  have hP0c : 0 ≤ R0 * b0.2 / (H0 ^ 2 * b0.2 + R0) :=
    div_nonneg (mul_nonneg hR0.le hP0) hS0.le
  have hP1c : 0 ≤ F ^ 2 * (R0 * b0.2 / (H0 ^ 2 * b0.2 + R0)) + Q :=
    add_nonneg (mul_nonneg (sq_nonneg F) hP0c) hQ
  have hS1c : 0 < H1 ^ 2 * (F ^ 2 * (R0 * b0.2 / (H0 ^ 2 * b0.2 + R0)) + Q)
      + R1 :=
    g06_innov_pos H1 R1 _ hP1c hR1
  have hD : 0 < (H0 ^ 2 * b0.2 + R0) * (H1 ^ 2 * (F ^ 2 * b0.2 + Q) + R1)
      - H0 * H1 * F * b0.2 * (H0 * H1 * F * b0.2) :=
    g06_det_pos F H0 H1 R0 R1 Q b0.2 hP0 hQ hR0 hR1
  have hS0ne := ne_of_gt hS0
  have hDne := ne_of_gt hD
  have hS0ne2 : b0.2 * H0 ^ 2 + R0 ≠ 0 := by
    have h : b0.2 * H0 ^ 2 + R0 = H0 ^ 2 * b0.2 + R0 := by ring
    rwa [h]
  have hS1eq : H1 ^ 2 * (F ^ 2 * (R0 * b0.2 / (H0 ^ 2 * b0.2 + R0)) + Q) + R1
      = (H1 ^ 2 * (F ^ 2 * R0 * b0.2 + Q * (H0 ^ 2 * b0.2 + R0))
        + R1 * (H0 ^ 2 * b0.2 + R0)) / (H0 ^ 2 * b0.2 + R0) := by
    field_simp
  have hS1num : 0 < H1 ^ 2 * (F ^ 2 * R0 * b0.2 + Q * (H0 ^ 2 * b0.2 + R0))
      + R1 * (H0 ^ 2 * b0.2 + R0) := by
    have hpos : 0 < (H1 ^ 2 * (F ^ 2 * R0 * b0.2 + Q * (H0 ^ 2 * b0.2 + R0))
        + R1 * (H0 ^ 2 * b0.2 + R0)) / (H0 ^ 2 * b0.2 + R0) := by
      rwa [← hS1eq]
    have hmul := mul_pos hpos hS0
    rwa [div_mul_cancel₀ _ hS0ne] at hmul
  have hS1numne := ne_of_gt hS1num
  simp only [g06Recursive, g06Predict, g06Update, g06BatchMean, g06BatchVar,
    g06BatchMeanX, g06BatchVarX, g06BatchMeanY, g06BatchCovY, g06BatchCovXY,
    Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two,
    Ring.inverse_eq_inv, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.smul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, smul_eq_mul, Pi.sub_apply, Prod.mk.injEq]
  rw [g06_update_var_eq H0 R0 b0.2 hS0ne, hS1eq]
  set S0 : ℝ := H0 ^ 2 * b0.2 + R0 with hS0def
  set N1 : ℝ := H1 ^ 2 * (F ^ 2 * R0 * b0.2 + Q * S0) + R1 * S0 with hN1def
  set DD : ℝ := S0 * (H1 ^ 2 * (F ^ 2 * b0.2 + Q) + R1)
    - H0 * H1 * F * b0.2 * (H0 * H1 * F * b0.2) with hDDdef
  clear hS0ne2
  constructor
  · field_simp
    simp only [hS0def, hN1def, hDDdef]
    ring
  · field_simp
    simp only [hS0def, hN1def, hDDdef]
    ring

end Cslib.MachineLearning.Sequence.G06KalmanHistory
