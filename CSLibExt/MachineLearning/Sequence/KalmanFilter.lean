/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianConditioning

/-!
# The Kalman filter: predict and update as exact Gaussian posteriors

The linear-Gaussian state-space model (Bishop, *Pattern Recognition and Machine Learning*,
Section 13.3; Murphy, *Machine Learning: A Probabilistic Perspective*, Section 18.3):

  `x' = F x + w`, `w ~ N(0, Q)`; `y = H x' + v`, `v ~ N(0, R)`.

The filter keeps a Gaussian belief `N(m, P)` about the state (`Belief`) and alternates

* `predict`: `N(F m, F P Fᵀ + Q)`;
* `update` with observation `y`: `N(m + K (y - H m), (1 - K H) P)` with the gain
  `K = P Hᵀ (H P Hᵀ + R)⁻¹` (`gain`);
* `step`: predict, then update.

`Belief.Valid` (positive semidefinite covariance) is preserved by all three (`predict_valid`,
`update_valid`, `step_valid`).

Main results, all exact statements about Mathlib's `multivariateGaussian` and `condDistrib`:

* `map_predict`: **the predict step is exact**: the law of `F x + w` is `predict F Q b`;
* `condDistrib_update`: **the update step is the exact posterior** of the state given `y`;
* `condDistrib_step`: **one filter step is the exact posterior** of `x'` given `y`, from a Gaussian
  prior on `x`.

They are corollaries of the linear-Gaussian Bayes theorem
`MetaMathlibExt.condDistrib_linear_add_of_indepFun`. Iterating them over a whole observation
sequence also needs the model's conditional independence of the past given the current state; that
recursion over histories is not formalized here.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Sequence.KalmanFilter

open MeasureTheory ProbabilityTheory Matrix WithLp MetaMathlibExt
open scoped MatrixOrder

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- The parameters of a Gaussian belief about the state: a mean and a covariance matrix. They
describe the Gaussian `N(mean, cov)` when the covariance is positive semidefinite
(`Belief.Valid`); for other matrices Mathlib's `multivariateGaussian` is a junk value. `predict`,
`update` and `step` preserve validity (`predict_valid`, `update_valid`, `step_valid`). -/
structure Belief (n : Type*) where
  /-- The mean. -/
  mean : EuclideanSpace ℝ n
  /-- The covariance. -/
  cov : Matrix n n ℝ

/-- A belief is valid when its covariance is positive semidefinite. -/
def Belief.Valid (b : Belief n) : Prop :=
  b.cov.PosSemidef

/-- The belief as a measure, `N(mean, cov)` for a valid belief. -/
noncomputable def Belief.law (b : Belief n) : Measure (EuclideanSpace ℝ n) :=
  multivariateGaussian b.mean b.cov

/-- **Predict**: for the dynamics `x' = F x + w`, `w ~ N(0, Q)`, the belief
`N(F m, F P Fᵀ + Q)`. -/
noncomputable def predict (F Q : Matrix n n ℝ) (b : Belief n) : Belief n :=
  ⟨toEuclideanLin F b.mean, F * b.cov * Fᵀ + Q⟩

/-- The Kalman gain `K = P Hᵀ (H P Hᵀ + R)⁻¹`. -/
noncomputable def gain (H : Matrix p n ℝ) (R : Matrix p p ℝ) (b : Belief n) : Matrix n p ℝ :=
  b.cov * Hᵀ * (H * b.cov * Hᵀ + R)⁻¹

/-- **Update**: for the observation `y = H x + v`, `v ~ N(0, R)`, the belief
`N(m + K (y - H m), (1 - K H) P)`. -/
noncomputable def update (H : Matrix p n ℝ) (R : Matrix p p ℝ) (y : EuclideanSpace ℝ p)
    (b : Belief n) : Belief n :=
  ⟨b.mean + toEuclideanLin (gain H R b) (y - toEuclideanLin H b.mean),
    (1 - gain H R b * H) * b.cov⟩

/-- One filter step: predict, then update with the new observation. -/
noncomputable def step (F Q : Matrix n n ℝ) (H : Matrix p n ℝ) (R : Matrix p p ℝ)
    (y : EuclideanSpace ℝ p) (b : Belief n) : Belief n :=
  update H R y (predict F Q b)

/-- **Prediction preserves validity** (positive semidefinite process noise `Q`). -/
theorem predict_valid (F Q : Matrix n n ℝ) {b : Belief n} (hb : b.Valid) (hQ : Q.PosSemidef) :
    (predict F Q b).Valid := by
  have := hb.mul_mul_conjTranspose_same F
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this.add hQ

/-- The update's covariance in Schur form: `(1 - K H) P = P - P Hᵀ (H P Hᵀ + R)⁻¹ H P`. -/
theorem update_cov_eq (H : Matrix p n ℝ) (R : Matrix p p ℝ) (y : EuclideanSpace ℝ p)
    (b : Belief n) :
    (update H R y b).cov = b.cov - b.cov * Hᵀ * (H * b.cov * Hᵀ + R)⁻¹ * (H * b.cov) := by
  rw [update, gain, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ H]

/-- **The update preserves validity** (positive definite observation noise `R`). -/
theorem update_valid (H : Matrix p n ℝ) {R : Matrix p p ℝ} (y : EuclideanSpace ℝ p)
    {b : Belief n} (hb : b.Valid) (hR : R.PosDef) : (update H R y b).Valid := by
  rw [Belief.Valid, update_cov_eq]
  exact posSemidef_sub_mul_inv_mul hb hR H

/-- **A filter step preserves validity.** -/
theorem step_valid (F Q : Matrix n n ℝ) (H : Matrix p n ℝ) {R : Matrix p p ℝ}
    (y : EuclideanSpace ℝ p) {b : Belief n} (hb : b.Valid) (hQ : Q.PosSemidef) (hR : R.PosDef) :
    (step F Q H R y b).Valid :=
  update_valid H y (predict_valid F Q hb hQ) hR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The predict step is exact**: if the state has law `N(m, P)` and the process noise
`w ~ N(0, Q)` is independent of it, then `F x + w` has law `predict F Q`. -/
theorem map_predict {x w : Ω → EuclideanSpace ℝ n} (hx : Measurable x) (hw : Measurable w)
    (hind : IndepFun x w P) {b : Belief n} {Q : Matrix n n ℝ} (hP : b.cov.PosSemidef)
    (hQ : Q.PosSemidef) (hxl : P.map x = b.law) (hwl : P.map w = multivariateGaussian 0 Q)
    (F : Matrix n n ℝ) :
    P.map (fun ω => toEuclideanLin F (x ω) + w ω) = (predict F Q b).law := by
  rw [map_linear_add_of_indepFun hx hw hind hP hQ hxl hwl F, add_zero]
  rfl

/-- **The update step is the exact posterior**: if the state has law `N(m, P)`, the observation
noise `v ~ N(0, R)` is independent of it and `H P Hᵀ + R` is invertible, then given the
observation `y = H x + v` the state has law `update H R y` (for almost every `y`). -/
theorem condDistrib_update {x : Ω → EuclideanSpace ℝ n} {v : Ω → EuclideanSpace ℝ p}
    (hx : Measurable x) (hv : Measurable v) (hind : IndepFun x v P) {b : Belief n}
    {R : Matrix p p ℝ} (hP : b.cov.PosSemidef) (hR : R.PosSemidef) (hxl : P.map x = b.law)
    (hvl : P.map v = multivariateGaussian 0 R) (H : Matrix p n ℝ)
    (hinv : IsUnit (H * b.cov * Hᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin H (x ω) + v ω),
      condDistrib x (fun ω => toEuclideanLin H (x ω) + v ω) P y = (update H R y b).law := by
  filter_upwards [condDistrib_linear_add_of_indepFun hx hv hind hP hR hxl hvl H hinv] with y hy
  rw [hy, Belief.law, update_cov_eq]
  rfl

/-- **One filter step is the exact posterior**: with prior state `x ~ N(m, P)`, dynamics
`x' = F x + w` and observation `y = H x' + v`, where `x`, `w` are independent, `(x, w)` is
independent of `v`, `w ~ N(0, Q)`, `v ~ N(0, R)` and the innovation covariance is invertible, the
posterior of `x'` given `y` is `step F Q H R y` (for almost every `y`). -/
theorem condDistrib_step {x w : Ω → EuclideanSpace ℝ n} {v : Ω → EuclideanSpace ℝ p}
    (hx : Measurable x) (hw : Measurable w) (hv : Measurable v) (hxw : IndepFun x w P)
    (hxwv : IndepFun (fun ω => (x ω, w ω)) v P) {b : Belief n} {Q : Matrix n n ℝ}
    {R : Matrix p p ℝ} (hP : b.cov.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (hxl : P.map x = b.law) (hwl : P.map w = multivariateGaussian 0 Q)
    (hvl : P.map v = multivariateGaussian 0 R) (F : Matrix n n ℝ) (H : Matrix p n ℝ)
    (hinv : IsUnit (H * (predict F Q b).cov * Hᵀ + R).det) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin H (toEuclideanLin F (x ω) + w ω) + v ω),
      condDistrib (fun ω => toEuclideanLin F (x ω) + w ω)
          (fun ω => toEuclideanLin H (toEuclideanLin F (x ω) + w ω) + v ω) P y =
        (step F Q H R y b).law := by
  have hx' : Measurable fun ω => toEuclideanLin F (x ω) + w ω :=
    ((continuous_toEuclideanLin F).measurable.comp hx).add hw
  have hind : IndepFun (fun ω => toEuclideanLin F (x ω) + w ω) v P := by
    have hg : Measurable fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ n =>
        toEuclideanLin F q.1 + q.2 :=
      ((continuous_toEuclideanLin F).measurable.comp measurable_fst).add measurable_snd
    exact hxwv.comp hg measurable_id
  exact condDistrib_update hx' hv hind (predict_valid F Q hP hQ) hR
    (map_predict hx hw hxw hP hQ hxl hwl F) hvl H hinv

end Cslib.MachineLearning.Sequence.KalmanFilter
