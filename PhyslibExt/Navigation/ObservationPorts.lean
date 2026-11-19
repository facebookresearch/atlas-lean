/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.Sequence.KalmanFilter
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem
public import PhyslibExt.EarthScience.GnssPseudorange

/-!
# Observation ports: stacked GNSS geometry at one epoch and its frozen linear surrogate

The pseudorange of satellite `j` at receiver position `x` is `‖x - s_j‖ + b`, the geometric range
plus the receiver clock bias `b`, the clock offset times the speed of light, so `b` is a length.
At one epoch, in one common Cartesian frame, with the receiver at the origin and satellites at
`-e₁, -e₂, -e₃, +e₁`, the derivatives of the four pseudoranges along the affine perturbation
`(x, b) = (t • d, b₀ + t * db)` stack into the linear observation operator with rows
`(e₁, 1), (e₂, 1), (e₃, 1), (-e₁, 1)`. Its determinant is `2`, so it is injective and every
residual vector has exactly one state correction. Frozen into a linear Gaussian model with the
known offsets removed, the same operator gives the exact conditional law of the predicted state
given the observation: the Kalman step of `Cslib.MachineLearning.Sequence.KalmanFilter`.

## i. Overview

* Rows. At `x₀ ≠ s` the directional derivative of `t ↦ ‖x₀ + t • d - s‖ + (b₀ + t * db)` at `0`
  is `⟪x₀ - s, d⟫ / ‖x₀ - s‖ + db`, by `EarthScience.gnss_directional_derivative`: the unit
  vector from the satellite toward the receiver, dotted with the position direction, plus the
  clock rate. At `x₀ = 0` and `s = -e₁` the unit vector is `e₁`; at `s = +e₁` it is `-e₁`.
* Stacking. The four rows form `observationMatrix`; the derivative of the stacked pseudorange
  map along `(d, db)` is `observationMatrix *ᵥ (d₁, d₂, d₃, db)`.
* Rank. `det observationMatrix = 2`, so `mulVec` is injective and each residual has a unique
  preimage (`Matrix.exists_unique_mulVec_eq`).
* Boundaries, checked in the test module. At a receiver coinciding with a satellite the range
  `‖t • d‖ = |t| ‖d‖` is not differentiable at `0` for `d ≠ 0`, so that row does not exist.
  Repeating a satellite repeats a row; the determinant is then `0` and a nonzero direction is
  invisible.
* Frozen surrogate. With the known deterministic offsets (the linearization point and the
  predicted pseudoranges) removed, the prior state `X0`, the process noise `w` and the
  measurement noise `v` give the predicted state `X1 = F X0 + w` and the observation
  `Y = H X1 + v` with `H = observationMatrix`. If `X0` and `w` are independent, `(X0, w)` and `v`
  are independent, the laws are `N(m, P)`, `N(0, Q)` and `N(0, R)` with positive semidefinite
  covariances, and the innovation covariance `H (F P Fᵀ + Q) Hᵀ + R` is invertible, then for
  almost every `y` the conditional law of `X1` given `Y = y` is the Kalman step
  `step F Q H R y` (`condDistrib_step`). A positive definite `R` makes the innovation
  invertible, but `R ⪰ 0` suffices for the posterior; the separate validity lemma `step_valid`
  needs `R ≻ 0`. Sensor noise equal to a nondegenerate process noise violates the independence
  premise.

Model inputs: one epoch, one common Cartesian frame, the clock bias in length units; the
receiver differs from every satellite. Sections A and B use error-free pseudoranges: they are
the derivative of the displayed affine perturbation and a finite row geometry, not a Fréchet
Jacobian, not global nonlinear localization, and no estimator or accuracy claim. Section C is
an exact frozen linear surrogate with the stated Gaussian noise: not the posterior of the
nonlinear raw pseudoranges and not full-history filtering; correlated process and sensor noise
and nonlinear observations are outside it.

## ii. Key results

- `satellite`, `stackedPseudorange`, `observationMatrix`, `stateDirection` : the geometry.
- `satellite_ne_receiver`, `pseudorange_hasDerivAt`, `jacobianRow_eq` : the four instantiated
  rows.
- `stackedPseudorange_hasDerivAt` : the stacked derivative is the observation operator.
- `observationMatrix_det`, `observationMatrix_mulVec_injective`,
  `observationMatrix_existsUnique` : determinant `2`, injectivity, unique corrections.
- `predictedState`, `surrogateObservation`, `measurable_predictedState`,
  `measurable_surrogateObservation` : the frozen surrogate and its measurability.
- `condDistrib_predictedState_surrogateObservation` : the conditional law of the predicted
  state given the observation, from `condDistrib_step`.
- `innovation_isUnit_of_posDef`, `not_indepFun_of_shared_noise` : positive measurement noise
  makes the innovation invertible; shared process and sensor noise is excluded.

## iii. Table of contents

- A. Geometry and rows
- B. The stacked operator and its rank
- C. The frozen linear surrogate and its conditional law

## iv. References

- E. D. Kaplan and C. J. Hegarty (eds.), *Understanding GPS: Principles and Applications*,
  2nd ed., Artech House (2006), Sections 2.4.1-2.4.2 and 7.3.1: pseudoranges and their
  linearization with rows `(a_i, 1)`.
- C. M. Bishop, *Pattern Recognition and Machine Learning*, Springer (2006), Section 13.3: the
  linear dynamical system and the Kalman filter.
- `PhyslibExt.EarthScience.GnssPseudorange` (`gnss_directional_derivative`) and
  `MathlibExt.LinearAlgebra.Matrix.FullRankLinearSystem` (`exists_unique_mulVec_eq`).
- `Cslib.MachineLearning.Sequence.KalmanFilter` (`condDistrib_step`, `step_valid`).
-/

@[expose] public section

open scoped InnerProductSpace Matrix

namespace Navigation.ObservationPorts

/-! ## A. Geometry and rows -/

/-- The four satellite positions `-e₁, -e₂, -e₃, +e₁` (unit distance from the receiver at the
origin), in one common Cartesian frame at one epoch. -/
noncomputable def satellite : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![-EuclideanSpace.single 0 1, -EuclideanSpace.single 1 1, -EuclideanSpace.single 2 1,
    EuclideanSpace.single 0 1]

/-- The four pseudoranges along the affine perturbation `x = 0 + t • d`, `b = b₀ + t * db` of the
receiver at the origin; `b` is the clock bias in length units. -/
noncomputable def stackedPseudorange (d : EuclideanSpace ℝ (Fin 3)) (b₀ db t : ℝ) : Fin 4 → ℝ :=
  fun j => ‖(0 : EuclideanSpace ℝ (Fin 3)) + t • d - satellite j‖ + (b₀ + t * db)

/-- The stacked linearized observation operator, rows `(e₁, 1), (e₂, 1), (e₃, 1), (-e₁, 1)`:
three position columns, then the clock column. -/
def observationMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 1; 0, 1, 0, 1; 0, 0, 1, 1; -1, 0, 0, 1]

/-- The state direction `(d, db)` in `ℝ⁴`, position components first, clock rate last. -/
def stateDirection (d : EuclideanSpace ℝ (Fin 3)) (db : ℝ) : Fin 4 → ℝ :=
  ![d 0, d 1, d 2, db]

/-- The receiver at the origin differs from every satellite. -/
lemma satellite_ne_receiver (j : Fin 4) : (0 : EuclideanSpace ℝ (Fin 3)) ≠ satellite j := by
  fin_cases j
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    simp [satellite] at h2
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
    simp [satellite] at h2
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 2) h
    simp [satellite] at h2
  · intro h
    have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    simp [satellite] at h2

/-- Each row is the directional derivative of its pseudorange at `t = 0`:
`⟪0 - s_j, d⟫ / ‖0 - s_j‖ + db`. -/
lemma pseudorange_hasDerivAt (j : Fin 4) (d : EuclideanSpace ℝ (Fin 3)) (b₀ db : ℝ) :
    HasDerivAt (fun t : ℝ => ‖(0 : EuclideanSpace ℝ (Fin 3)) + t • d - satellite j‖ + (b₀ + t * db))
      (⟪(0 : EuclideanSpace ℝ (Fin 3)) - satellite j, d⟫_ℝ /
        ‖(0 : EuclideanSpace ℝ (Fin 3)) - satellite j‖ + db) 0 := by
  exact EarthScience.gnss_directional_derivative 0 (satellite j) d b₀ db (satellite_ne_receiver j)

/-- The rows of `observationMatrix` are the instantiated Jacobian rows: the unit vector from
satellite `j` toward the receiver, then `1` for the clock. -/
lemma jacobianRow_eq (j : Fin 4) (d : EuclideanSpace ℝ (Fin 3)) (db : ℝ) :
    ⟪(0 : EuclideanSpace ℝ (Fin 3)) - satellite j, d⟫_ℝ /
        ‖(0 : EuclideanSpace ℝ (Fin 3)) - satellite j‖ + db =
      (observationMatrix *ᵥ stateDirection d db) j := by
  fin_cases j <;> simp [satellite, EuclideanSpace.inner_single_left, observationMatrix,
    stateDirection, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]

/-! ## B. The stacked operator and its rank -/

/-- The derivative of the stacked pseudorange map along `(d, db)` at `t = 0` is the observation
operator applied to the state direction. -/
lemma stackedPseudorange_hasDerivAt (d : EuclideanSpace ℝ (Fin 3)) (b₀ db : ℝ) :
    HasDerivAt (stackedPseudorange d b₀ db) (observationMatrix *ᵥ stateDirection d db) 0 := by
  rw [hasDerivAt_pi]
  intro j
  have h := pseudorange_hasDerivAt j d b₀ db
  rwa [jacobianRow_eq j d db] at h

/-- The observation operator has determinant `2`. -/
lemma observationMatrix_det : observationMatrix.det = 2 := by
  rw [observationMatrix, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove]
  norm_num

/-- The observation operator is injective: distinct state directions give distinct stacked
derivatives. -/
lemma observationMatrix_mulVec_injective : Function.Injective observationMatrix.mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, observationMatrix_det]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- Every residual vector has exactly one state correction. -/
lemma observationMatrix_existsUnique (r : Fin 4 → ℝ) :
    ∃! v : Fin 4 → ℝ, observationMatrix *ᵥ v = r := by
  exact Matrix.exists_unique_mulVec_eq observationMatrix_mulVec_injective r

/-! ## C. The frozen linear surrogate and its conditional law -/

open MeasureTheory ProbabilityTheory Matrix WithLp
open Cslib.MachineLearning.Sequence.KalmanFilter (Belief predict step)

variable {Ω : Type*}

/-- The predicted state `X1 = F X0 + w` of the frozen surrogate, offsets removed. -/
noncomputable def predictedState (F : Matrix (Fin 4) (Fin 4) ℝ)
    (X0 w : Ω → EuclideanSpace ℝ (Fin 4)) (ω : Ω) : EuclideanSpace ℝ (Fin 4) :=
  toEuclideanLin F (X0 ω) + w ω

/-- The observation `Y = H X1 + v` of the predicted state through the fixed stacked operator
`H = observationMatrix`, offsets removed. -/
noncomputable def surrogateObservation (F : Matrix (Fin 4) (Fin 4) ℝ)
    (X0 w v : Ω → EuclideanSpace ℝ (Fin 4)) (ω : Ω) : EuclideanSpace ℝ (Fin 4) :=
  toEuclideanLin observationMatrix (predictedState F X0 w ω) + v ω

variable {mΩ : MeasurableSpace Ω}

/-- The predicted state is measurable when the prior state and the process noise are. -/
lemma measurable_predictedState (F : Matrix (Fin 4) (Fin 4) ℝ)
    {X0 w : Ω → EuclideanSpace ℝ (Fin 4)} (hX0 : Measurable X0) (hw : Measurable w) :
    Measurable (predictedState F X0 w) := by
  exact ((MetaMathlibExt.continuous_toEuclideanLin F).measurable.comp hX0).add hw

/-- The observation is measurable when the prior state and both noises are. -/
lemma measurable_surrogateObservation (F : Matrix (Fin 4) (Fin 4) ℝ)
    {X0 w v : Ω → EuclideanSpace ℝ (Fin 4)} (hX0 : Measurable X0) (hw : Measurable w)
    (hv : Measurable v) :
    Measurable (surrogateObservation F X0 w v) := by
  exact ((MetaMathlibExt.continuous_toEuclideanLin observationMatrix).measurable.comp
    (measurable_predictedState F hX0 hw)).add hv

/-- The conditional law of the frozen surrogate: with `X0` independent of `w`, `(X0, w)`
independent of `v`, the Gaussian laws `N(m, P)`, `N(0, Q)`, `N(0, R)` with positive semidefinite
covariances and an invertible innovation covariance, the conditional law of `X1 = F X0 + w` given
`Y = H X1 + v` is the Kalman step `step F Q H R y` for almost every observation `y`. -/
lemma condDistrib_predictedState_surrogateObservation {P : Measure Ω} [IsProbabilityMeasure P]
    {X0 w v : Ω → EuclideanSpace ℝ (Fin 4)} (hX0 : Measurable X0) (hw : Measurable w)
    (hv : Measurable v) (hX0w : IndepFun X0 w P) (hX0wv : IndepFun (fun ω => (X0 ω, w ω)) v P)
    {b : Belief (Fin 4)} {Q R : Matrix (Fin 4) (Fin 4) ℝ} (hP : b.cov.PosSemidef)
    (hQ : Q.PosSemidef) (hR : R.PosSemidef) (hX0l : P.map X0 = b.law)
    (hwl : P.map w = multivariateGaussian 0 Q) (hvl : P.map v = multivariateGaussian 0 R)
    (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hinv : IsUnit (observationMatrix * (predict F Q b).cov * observationMatrixᵀ + R).det) :
    ∀ᵐ y ∂P.map (surrogateObservation F X0 w v),
      condDistrib (predictedState F X0 w) (surrogateObservation F X0 w v) P y =
        (step F Q observationMatrix R y b).law := by
  exact Cslib.MachineLearning.Sequence.KalmanFilter.condDistrib_step hX0 hw hv hX0w hX0wv hP hQ hR
    hX0l hwl hvl F observationMatrix hinv

/-- Positive measurement noise makes the innovation invertible: for every positive semidefinite
predicted covariance `C` and positive definite `R`, `H C Hᵀ + R` has a unit determinant. -/
lemma innovation_isUnit_of_posDef {C R : Matrix (Fin 4) (Fin 4) ℝ} (hC : C.PosSemidef)
    (hR : R.PosDef) : IsUnit (observationMatrix * C * observationMatrixᵀ + R).det := by
  have hHC : (observationMatrix * C * observationMatrixᵀ).PosSemidef := by
    have h := hC.mul_mul_conjTranspose_same observationMatrix
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.posSemidef_add hHC hR).isUnit

/-- Correlated process and sensor noise is outside the theorem: sensor noise equal to a Gaussian
process noise `w ~ N(0, Q)` with a nonzero variance `Q i i` is never independent of `(X0, w)`, so
the second independence premise fails. -/
lemma not_indepFun_of_shared_noise {P : Measure Ω} [IsProbabilityMeasure P]
    {X0 w : Ω → EuclideanSpace ℝ (Fin 4)} (hw : Measurable w) {Q : Matrix (Fin 4) (Fin 4) ℝ}
    (hQ : Q.PosSemidef) (hwl : P.map w = multivariateGaussian 0 Q) {i : Fin 4}
    (hQi : Q i i ≠ 0) :
    ¬ IndepFun (fun ω => (X0 ω, w ω)) w P := by
  intro h
  have hi : IndepFun (fun ω => w ω i) (fun ω => w ω i) P :=
    h.comp (φ := fun p : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 4) => p.2 i)
      (ψ := fun x : EuclideanSpace ℝ (Fin 4) => x i) (by fun_prop) (by fun_prop)
  have hcoord : MemLp (fun x : EuclideanSpace ℝ (Fin 4) => x i) 2 (multivariateGaussian 0 Q) := by
    have h' := IsGaussian.memLp_dual (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 4)) Q)
      (EuclideanSpace.proj i) 2 (by simp)
    rwa [EuclideanSpace.coe_proj] at h'
  have hmem : MemLp (fun ω => w ω i) 2 P := by
    rw [← hwl] at hcoord
    exact (memLp_map_measure_iff (by fun_prop) hw.aemeasurable).mp hcoord
  have hcov0 := hi.covariance_eq_zero hmem hmem
  have hcovQ : cov[fun x : EuclideanSpace ℝ (Fin 4) => x i, fun x => x i; P.map w] = Q i i := by
    rw [hwl]
    exact covariance_eval_multivariateGaussian hQ i i
  rw [covariance_map_fun (by fun_prop) (by fun_prop) hw.aemeasurable] at hcovQ
  exact hQi (hcovQ.symm.trans hcov0)

end Navigation.ObservationPorts
