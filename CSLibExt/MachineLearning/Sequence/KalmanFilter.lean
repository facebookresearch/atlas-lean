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

/-- **Gaussian belief.** For an index type $n$, a belief about the state consists of a mean
$m \in \mathbb{R}^n$ and a covariance matrix $P$, an arbitrary real $n \times n$ matrix. It
describes the Gaussian distribution $N(m, P)$ when $P$ is positive semidefinite (the belief is
valid); for other matrices Mathlib's multivariate Gaussian is a junk value. Prediction with
positive semidefinite process noise, update with positive definite observation noise, and a filter
step with both preserve validity. -/
structure Belief (n : Type*) where
  /-- The mean. -/
  mean : EuclideanSpace ℝ n
  /-- The covariance. -/
  cov : Matrix n n ℝ

/-- **Valid Gaussian beliefs.** A belief is valid when its covariance matrix is positive
semidefinite. -/
def Belief.Valid (b : Belief n) : Prop :=
  b.cov.PosSemidef

/-- **Law of a belief.** The law of a belief with mean $m$ and covariance $P$ is Mathlib's
multivariate Gaussian measure $N(m, P)$ on $\mathbb{R}^n$. It is the Gaussian distribution with
mean $m$ and covariance $P$ when $P$ is positive semidefinite (the belief is valid); otherwise it
is the point mass at $m$. -/
noncomputable def Belief.law (b : Belief n) : Measure (EuclideanSpace ℝ n) :=
  multivariateGaussian b.mean b.cov

/-- **Kalman prediction.** Given real $n \times n$ matrices $F$ and $Q$, the prediction of a
belief with mean $m$ and covariance $P$ is the belief with mean $F m$ and covariance
$F P F^\top + Q$. It models the dynamics $x' = F x + w$ with process noise $w \sim N(0, Q)$. -/
noncomputable def predict (F Q : Matrix n n ℝ) (b : Belief n) : Belief n :=
  ⟨toEuclideanLin F b.mean, F * b.cov * Fᵀ + Q⟩

/-- **Kalman gain.** For a real $p \times n$ matrix $H$, a real $p \times p$ matrix $R$ and a
belief with covariance $P$, the Kalman gain is the real $n \times p$ matrix
$K = P H^\top (H P H^\top + R)^{-1}$, where the inverse is taken to be $0$ when
$H P H^\top + R$ is singular. -/
noncomputable def gain (H : Matrix p n ℝ) (R : Matrix p p ℝ) (b : Belief n) : Matrix n p ℝ :=
  b.cov * Hᵀ * (H * b.cov * Hᵀ + R)⁻¹

/-- **Kalman filter update.** Given a real $p \times n$ observation matrix $H$, a real $p \times p$
matrix $R$, an observation $y \in \mathbb{R}^p$ and a belief with mean $m$ and covariance $P$,
the updated belief has mean $m + K (y - H m)$ and covariance $(I - K H) P$, where
$K = P H^\top (H P H^\top + R)^{-1}$ is the Kalman gain and the matrix inverse is taken to be
$0$ when $H P H^\top + R$ is singular.

It corresponds to observing a state $x$ as $y = H x + v$ with Gaussian noise $v \sim N(0, R)$. -/
noncomputable def update (H : Matrix p n ℝ) (R : Matrix p p ℝ) (y : EuclideanSpace ℝ p)
    (b : Belief n) : Belief n :=
  ⟨b.mean + toEuclideanLin (gain H R b) (y - toEuclideanLin H b.mean),
    (1 - gain H R b * H) * b.cov⟩

/-- **Kalman filter step.** Given real $n \times n$ matrices $F$ and $Q$, a real $p \times n$
matrix $H$, a real $p \times p$ matrix $R$ and an observation $y \in \mathbb{R}^p$, one filter
step sends a belief to the update, with $H$, $R$ and $y$, of its prediction with $F$ and $Q$. -/
noncomputable def step (F Q : Matrix n n ℝ) (H : Matrix p n ℝ) (R : Matrix p p ℝ)
    (y : EuclideanSpace ℝ p) (b : Belief n) : Belief n :=
  update H R y (predict F Q b)

/-- **Prediction preserves validity.** Let $F$ and $Q$ be real $n \times n$ matrices with $Q$
positive semidefinite. If a belief is valid, that is, its covariance $P$ is positive
semidefinite, then the predicted belief, with covariance $F P F^\top + Q$, is valid. -/
theorem predict_valid (F Q : Matrix n n ℝ) {b : Belief n} (hb : b.Valid) (hQ : Q.PosSemidef) :
    (predict F Q b).Valid := by
  have := hb.mul_mul_conjTranspose_same F
  rw [conjTranspose_eq_transpose_of_trivial] at this
  exact this.add hQ

/-- **Schur form of the updated covariance.** Let $H$ be a real $p \times n$ matrix, $R$ a real
$p \times p$ matrix and $y \in \mathbb{R}^p$, and let a belief have covariance $P$. Then the
covariance of the belief updated with $H$, $R$ and $y$ equals
$P - P H^\top (H P H^\top + R)^{-1} H P$. Here $M^{-1}$ is the matrix inverse, taken to be $0$
when $M$ is singular, so no invertibility is assumed.

With the Kalman gain $K = P H^\top (H P H^\top + R)^{-1}$ this says $(I - K H) P =
P - P H^\top (H P H^\top + R)^{-1} H P$. -/
theorem update_cov_eq (H : Matrix p n ℝ) (R : Matrix p p ℝ) (y : EuclideanSpace ℝ p)
    (b : Belief n) :
    (update H R y b).cov = b.cov - b.cov * Hᵀ * (H * b.cov * Hᵀ + R)⁻¹ * (H * b.cov) := by
  rw [update, gain, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc _ H]

/-- **The Kalman update preserves validity.** Let $H$ be a real $p \times n$ matrix, $R$ a
symmetric positive definite real $p \times p$ matrix and $y \in \mathbb{R}^p$. If a belief is
valid, then the belief updated with $H$, $R$ and $y$ is valid. -/
theorem update_valid (H : Matrix p n ℝ) {R : Matrix p p ℝ} (y : EuclideanSpace ℝ p)
    {b : Belief n} (hb : b.Valid) (hR : R.PosDef) : (update H R y b).Valid := by
  rw [Belief.Valid, update_cov_eq]
  exact posSemidef_sub_mul_inv_mul hb hR H

/-- **A filter step preserves validity.** Let $F$ and $Q$ be real $n \times n$ matrices with $Q$
positive semidefinite, $H$ a real $p \times n$ matrix, $R$ a positive definite real $p \times p$
matrix and $y \in \mathbb{R}^p$. If a belief is valid (its covariance is positive semidefinite),
then so is the belief obtained from it by one filter step with $F$, $Q$, $H$, $R$ and the
observation $y$. -/
theorem step_valid (F Q : Matrix n n ℝ) (H : Matrix p n ℝ) {R : Matrix p p ℝ}
    (y : EuclideanSpace ℝ p) {b : Belief n} (hb : b.Valid) (hQ : Q.PosSemidef) (hR : R.PosDef) :
    (step F Q H R y b).Valid :=
  update_valid H y (predict_valid F Q hb hQ) hR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The predict step is exact.** Let $x$ and $w$ be measurable, independent random vectors in
$\mathbb{R}^n$ on a probability space. If $x$ has the law $N(m, P)$ of a belief with mean $m$ and
positive semidefinite covariance $P$, and $w$ has law $N(0, Q)$ with $Q$ positive semidefinite,
then for every real $n \times n$ matrix $F$ the random vector $F x + w$ has the law of the
predicted belief, $N(F m, F P F^\top + Q)$. -/
theorem map_predict {x w : Ω → EuclideanSpace ℝ n} (hx : Measurable x) (hw : Measurable w)
    (hind : IndepFun x w P) {b : Belief n} {Q : Matrix n n ℝ} (hP : b.cov.PosSemidef)
    (hQ : Q.PosSemidef) (hxl : P.map x = b.law) (hwl : P.map w = multivariateGaussian 0 Q)
    (F : Matrix n n ℝ) :
    P.map (fun ω => toEuclideanLin F (x ω) + w ω) = (predict F Q b).law := by
  rw [map_linear_add_of_indepFun hx hw hind hP hQ hxl hwl F, add_zero]
  rfl

/-- **The update step is the exact posterior.** Let $x$ be a measurable random vector in
$\mathbb{R}^n$ and $v$ a measurable random vector in $\mathbb{R}^p$ on a probability space, with
$x$ independent of $v$. Suppose $x$ has the law $N(m, P)$ of a belief with mean $m$ and positive
semidefinite covariance $P$, and $v$ has law $N(0, R)$ with $R$ positive semidefinite. Let $H$ be
a real $p \times n$ matrix with $H P H^\top + R$ invertible, and put $Y = H x + v$. Then for
almost every $y$ with respect to the law of $Y$, the conditional distribution of $x$ given
$Y = y$ is the law of the belief obtained from $(m, P)$ by the update with $H$, $R$ and the
observation $y$. -/
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

/-- **One filter step is the exact posterior.** Let $x$ and $w$ be measurable random vectors in
$\mathbb{R}^n$ and $v$ a measurable random vector in $\mathbb{R}^p$ on a probability space, with
$x$ independent of $w$ and the pair $(x, w)$ independent of $v$. Suppose $x$ has the law
$N(m, P)$ of a belief with mean $m$ and positive semidefinite covariance $P$, $w$ has law
$N(0, Q)$ and $v$ has law $N(0, R)$, with $Q$ and $R$ positive semidefinite. Let $F$ be a real
$n \times n$ matrix and $H$ a real $p \times n$ matrix with $H (F P F^\top + Q) H^\top + R$
invertible, and put $x' = F x + w$ and $Y = H x' + v$. Then for almost every $y$ with respect to
the law of $Y$, the conditional distribution of $x'$ given $Y = y$ is the law of the belief
obtained from $(m, P)$ by one filter step with $F$, $Q$, $H$, $R$ and the observation $y$. -/
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
