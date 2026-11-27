/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianConditioning
import Mathlib.Probability.Distributions.Gaussian.Fernique

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
* `condDistrib_update`: **the update step is the exact posterior** of the state given `y`, when the
  innovation covariance `H P Hᵀ + R` is invertible;
* `condDistrib_step`: **one filter step is the exact posterior** of `x'` given `y`, from a Gaussian
  prior on `x`, when the innovation covariance is invertible.

They are corollaries of the linear-Gaussian Bayes theorem
`MetaMathlibExt.condDistrib_linear_add_of_indepFun`.

Over a whole observation history (Anderson and Moore, *Optimal Filtering*, Section 3.1), the
time-varying signal model with horizon `N` is `x_{k+1} = F_k x_k + G_k w_k` for `k < N` and
`z_k = H_kᵀ x_k + v_k` for `k ≤ N`, with mutually independent `x_0 ~ N(x̄_0, P_0)`,
`w_k ~ N(0, Q_k)` and `v_k ~ N(0, R_k)`, `P_0` and `Q_k` positive semidefinite and `R_k` positive
definite:

* `predictedBelief`, `filteredBelief`: the filter run on observations `z_0, …, z_{k-1}` and
  `z_0, …, z_k`, giving `(x̂_{k|k-1}, Σ_{k|k-1})` and `(x̂_{k|k}, Σ_{k|k})`; the gain inverts the
  innovation covariance `H_kᵀ Σ_{k|k-1} H_k + R_k`, with the inverse taken to be `0` when it is
  singular;
* `condDistrib_observationHistory`: **the Kalman filter gives the conditional law given the whole
  observation history**: for every `k ≤ N`, `x_k` given `z_0, …, z_{k-1}` is
  `N(x̂_{k|k-1}, Σ_{k|k-1})` for almost every history under its law, and `x_k` given
  `z_0, …, z_k` is `N(x̂_{k|k}, Σ_{k|k})` for almost every history under its law; `Σ_{k|k}` does
  not depend on the observations; and `x̂_{k|k}` is almost surely the conditional expectation of
  `x_k` given `z_0, …, z_k` and, among measurable functions of `z_0, …, z_k`, the minimizer of the
  mean squared error, unique up to almost sure equality.

The theorem assumes `R_k` positive definite. When an innovation covariance is singular, the zero
inverse is only a convention, and the beliefs need not be the conditional laws: for
`x_0 ~ N(0, 1)` observed without noise as `z_0 = (x_0, 0)`, the innovation covariance is singular
and the filtered variance stays `1`, while `x_0` given `z_0` is a point mass.

The proof conditions step by step: given the past, the current noise is independent of the past
and of the state, so each predict and update step is the one-step result applied fibrewise.
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

/-- **Under Gaussian hypotheses with an invertible innovation covariance, the update step gives the
conditional law for almost every observation.** Let $n$ and $p$ be finite index types with decidable
equality, let $x$ be a measurable random vector in $\mathbb{R}^n$ and $v$ a measurable random vector
in $\mathbb{R}^p$ on a probability space, with $x$ independent of $v$. Suppose $x$ has the law
$N(m, P)$ of a belief with mean $m$ and positive semidefinite covariance $P$, and $v$ has law
$N(0, R)$ with $R$ positive semidefinite. Let $H$ be a real $p \times n$ matrix with
$H P H^\top + R$ invertible, and put $Y = H x + v$. Then for almost every $y$ with respect to the
law of $Y$, the conditional distribution of $x$ given $Y = y$ is the law of the belief obtained from
$(m, P)$ by the update with $H$, $R$ and the observation $y$. -/
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

/-! ### Gaussian conditioning given an observed history

Private lemmas for the history theorem: one predict and one update step, conditionally on a past
whose conditional law of the state is Gaussian with a mean depending on the past. -/

section StepLemmas

open scoped RealInnerProductSpace

variable {r : Type*} [Fintype r] [DecidableEq r]

private theorem noiseKernel_multivariateGaussian_apply {α : Type*} [MeasurableSpace α]
    (f : α → EuclideanSpace ℝ n) (hf : Measurable f) (S : Matrix n n ℝ) (a : α) :
    noiseKernel f hf (multivariateGaussian 0 S) a = multivariateGaussian (f a) S := by
  rw [noiseKernel_apply, map_add_multivariateGaussian, add_zero]

private theorem compProd_prod_apply {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ]
    (ν : Measure γ) [SFinite ν] {t : Set ((α × β) × γ)} (ht : MeasurableSet t) :
    ((μ ⊗ₘ κ).prod ν) t = ∫⁻ a, ((κ a).prod ν) ((fun q => ((a, q.1), q.2)) ⁻¹' t) ∂μ := by
  rw [Measure.prod_apply ht, Measure.lintegral_compProd (measurable_measure_prodMk_left ht)]
  refine lintegral_congr fun a => ?_
  rw [Measure.prod_apply (ht.preimage (by fun_prop))]
  rfl

private theorem map_prod_multivariateGaussian_predict (m : EuclideanSpace ℝ n)
    {S : Matrix n n ℝ} {Q : Matrix r r ℝ} (hS : S.PosSemidef) (hQ : Q.PosSemidef)
    (F : Matrix n n ℝ) (G : Matrix n r ℝ) :
    ((multivariateGaussian m S).prod (multivariateGaussian 0 Q)).map
        (fun q => toEuclideanLin F q.1 + toEuclideanLin G q.2) =
      multivariateGaussian (toEuclideanLin F m) (F * S * Fᵀ + G * Q * Gᵀ) := by
  set μ := (multivariateGaussian m S).prod (multivariateGaussian 0 Q)
  have hG : Measurable (toEuclideanLin G) := (continuous_toEuclideanLin G).measurable
  have hGQ : (G * Q * Gᵀ).PosSemidef := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hQ.mul_mul_conjTranspose_same G
  have hind : IndepFun (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ r => q.1)
      (fun q => toEuclideanLin G q.2) μ :=
    indepFun_prod measurable_id hG
  have h1 : μ.map (fun q => q.1) = multivariateGaussian m S := by
    rw [show (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ r => q.1) = Prod.fst from rfl,
      Measure.map_fst_prod, measure_univ, one_smul]
  have h2 : μ.map (fun q => toEuclideanLin G q.2) = multivariateGaussian 0 (G * Q * Gᵀ) := by
    rw [show (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ r => toEuclideanLin G q.2) =
        toEuclideanLin G ∘ Prod.snd from rfl, ← Measure.map_map hG measurable_snd,
      Measure.map_snd_prod, measure_univ, one_smul, map_toEuclideanLin_multivariateGaussian G 0 hQ,
      map_zero]
  have h := map_linear_add_of_indepFun measurable_fst (hG.comp measurable_snd) hind hS hGQ h1 h2 F
  rwa [add_zero] at h

private theorem map_prod_multivariateGaussian_update (m : EuclideanSpace ℝ n)
    {S : Matrix n n ℝ} {R : Matrix p p ℝ} (hS : S.PosSemidef) (hR : R.PosSemidef)
    (H : Matrix p n ℝ) (hinv : IsUnit (H * S * Hᵀ + R).det) :
    ((multivariateGaussian m S).prod (multivariateGaussian 0 R)).map
        (fun q => (toEuclideanLin H q.1 + q.2, q.1)) =
      multivariateGaussian (toEuclideanLin H m) (H * S * Hᵀ + R) ⊗ₘ
        noiseKernel
          (fun y => m + toEuclideanLin (S * Hᵀ * (H * S * Hᵀ + R)⁻¹) (y - toEuclideanLin H m))
          ((continuous_const.add ((continuous_toEuclideanLin _).comp
            (continuous_id.sub continuous_const))).measurable)
          (multivariateGaussian 0 (S - S * Hᵀ * (H * S * Hᵀ + R)⁻¹ * (H * S))) := by
  set μ := (multivariateGaussian m S).prod (multivariateGaussian 0 R)
  have hind : IndepFun (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ p => q.1) (fun q => q.2) μ :=
    indepFun_prod measurable_id measurable_id
  have h1 : μ.map (fun q => q.1) = multivariateGaussian m S := by
    rw [show (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ p => q.1) = Prod.fst from rfl,
      Measure.map_fst_prod, measure_univ, one_smul]
  have h2 : μ.map (fun q => q.2) = multivariateGaussian 0 R := by
    rw [show (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ p => q.2) = Prod.snd from rfl,
      Measure.map_snd_prod, measure_univ, one_smul]
  have hY : Measurable fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ p =>
      toEuclideanLin H q.1 + q.2 :=
    ((continuous_toEuclideanLin H).measurable.comp measurable_fst).add measurable_snd
  have hlawY : μ.map (fun q => toEuclideanLin H q.1 + q.2) =
      multivariateGaussian (toEuclideanLin H m) (H * S * Hᵀ + R) := by
    have h := map_linear_add_of_indepFun measurable_fst measurable_snd hind hS hR h1 h2 H
    rwa [add_zero] at h
  have hcd := condDistrib_linear_add_of_indepFun measurable_fst measurable_snd hind hS hR h1 h2 H
    hinv
  rw [← compProd_map_condDistrib hY.aemeasurable measurable_fst.aemeasurable]
  rw [hlawY] at hcd ⊢
  refine Measure.compProd_congr ?_
  filter_upwards [hcd] with y hy
  rw [hy, noiseKernel_multivariateGaussian_apply]

private theorem map_compProd_prod_predict {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → EuclideanSpace ℝ n) (hf : Measurable f) {S : Matrix n n ℝ}
    {Q : Matrix r r ℝ} (hS : S.PosSemidef) (hQ : Q.PosSemidef) (F : Matrix n n ℝ)
    (G : Matrix n r ℝ) :
    ((μ ⊗ₘ noiseKernel f hf (multivariateGaussian 0 S)).prod (multivariateGaussian 0 Q)).map
        (fun q => (q.1.1, toEuclideanLin F q.1.2 + toEuclideanLin G q.2)) =
      μ ⊗ₘ noiseKernel (fun a => toEuclideanLin F (f a))
        ((continuous_toEuclideanLin F).measurable.comp hf)
        (multivariateGaussian 0 (F * S * Fᵀ + G * Q * Gᵀ)) := by
  have hψ : Measurable fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ r =>
      toEuclideanLin F q.1 + toEuclideanLin G q.2 :=
    ((continuous_toEuclideanLin F).measurable.comp measurable_fst).add
      ((continuous_toEuclideanLin G).measurable.comp measurable_snd)
  have hg : Measurable fun q : (α × EuclideanSpace ℝ n) × EuclideanSpace ℝ r =>
      (q.1.1, toEuclideanLin F q.1.2 + toEuclideanLin G q.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      (((continuous_toEuclideanLin F).measurable.comp (measurable_snd.comp measurable_fst)).add
        ((continuous_toEuclideanLin G).measurable.comp measurable_snd))
  ext s hs
  rw [Measure.map_apply hg hs, compProd_prod_apply _ _ _ (hg hs), Measure.compProd_apply hs]
  refine lintegral_congr fun a => ?_
  rw [noiseKernel_multivariateGaussian_apply, noiseKernel_multivariateGaussian_apply,
    ← map_prod_multivariateGaussian_predict (f a) hS hQ F G,
    Measure.map_apply hψ (measurable_prodMk_left hs)]
  rfl

private theorem map_compProd_prod_update {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → EuclideanSpace ℝ n) (hf : Measurable f) {S : Matrix n n ℝ}
    {R : Matrix p p ℝ} (hS : S.PosSemidef) (hR : R.PosSemidef) (H : Matrix p n ℝ)
    (hinv : IsUnit (H * S * Hᵀ + R).det) :
    ((μ ⊗ₘ noiseKernel f hf (multivariateGaussian 0 S)).prod (multivariateGaussian 0 R)).map
        (fun q => ((q.1.1, toEuclideanLin H q.1.2 + q.2), q.1.2)) =
      (μ ⊗ₘ noiseKernel (fun a => toEuclideanLin H (f a))
          ((continuous_toEuclideanLin H).measurable.comp hf)
          (multivariateGaussian 0 (H * S * Hᵀ + R))) ⊗ₘ
        noiseKernel (fun q : α × EuclideanSpace ℝ p =>
            f q.1 + toEuclideanLin (S * Hᵀ * (H * S * Hᵀ + R)⁻¹) (q.2 - toEuclideanLin H (f q.1)))
          ((hf.comp measurable_fst).add ((continuous_toEuclideanLin _).measurable.comp
            (measurable_snd.sub ((continuous_toEuclideanLin H).measurable.comp
              (hf.comp measurable_fst)))))
          (multivariateGaussian 0 (S - S * Hᵀ * (H * S * Hᵀ + R)⁻¹ * (H * S))) := by
  have hφ : Measurable fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ p =>
      (toEuclideanLin H q.1 + q.2, q.1) :=
    (((continuous_toEuclideanLin H).measurable.comp measurable_fst).add measurable_snd).prodMk
      measurable_fst
  have hg : Measurable fun q : (α × EuclideanSpace ℝ n) × EuclideanSpace ℝ p =>
      ((q.1.1, toEuclideanLin H q.1.2 + q.2), q.1.2) :=
    ((measurable_fst.comp measurable_fst).prodMk (((continuous_toEuclideanLin H).measurable.comp
      (measurable_snd.comp measurable_fst)).add measurable_snd)).prodMk
      (measurable_snd.comp measurable_fst)
  ext s hs
  rw [Measure.map_apply hg hs, compProd_prod_apply _ _ _ (hg hs), Measure.compProd_apply hs,
    Measure.lintegral_compProd (Kernel.measurable_kernel_prodMk_left hs)]
  refine lintegral_congr fun a => ?_
  have hsa : MeasurableSet ((fun q : EuclideanSpace ℝ p × EuclideanSpace ℝ n =>
      ((a, q.1), q.2)) ⁻¹' s) := hs.preimage (by fun_prop)
  rw [noiseKernel_multivariateGaussian_apply, noiseKernel_multivariateGaussian_apply,
    show (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ p => ((a, q.1), q.2)) ⁻¹'
        ((fun q : (α × EuclideanSpace ℝ n) × EuclideanSpace ℝ p =>
          ((q.1.1, toEuclideanLin H q.1.2 + q.2), q.1.2)) ⁻¹' s) =
      (fun q : EuclideanSpace ℝ n × EuclideanSpace ℝ p => (toEuclideanLin H q.1 + q.2, q.1)) ⁻¹'
        ((fun q : EuclideanSpace ℝ p × EuclideanSpace ℝ n => ((a, q.1), q.2)) ⁻¹' s) from rfl,
    ← Measure.map_apply hφ hsa, map_prod_multivariateGaussian_update (f a) hS hR H hinv,
    Measure.compProd_apply hsa]
  refine lintegral_congr fun y => ?_
  rw [noiseKernel_multivariateGaussian_apply, noiseKernel_multivariateGaussian_apply]
  rfl

private theorem measurable_init_last {k : ℕ} {E : Type*} [MeasurableSpace E] :
    Measurable fun ζ : Fin (k + 1) → E => (Fin.init ζ, ζ (Fin.last k)) :=
  (measurable_pi_iff.2 fun i => measurable_pi_apply (Fin.castSucc i)).prodMk
    (measurable_pi_apply _)

private theorem measurable_snoc {k : ℕ} {E : Type*} [MeasurableSpace E] :
    Measurable fun q : (Fin k → E) × E => (Fin.snoc q.1 q.2 : Fin (k + 1) → E) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last]
    exact measurable_snd
  · simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply i).comp measurable_fst

private theorem map_snoc_compProd {k : ℕ} {E β : Type*} [MeasurableSpace E] [MeasurableSpace β]
    (ν : Measure ((Fin k → E) × E)) [SFinite ν] (η : Kernel ((Fin k → E) × E) β)
    [IsSFiniteKernel η] :
    (ν ⊗ₘ η).map (fun q => (Fin.snoc q.1.1 q.1.2, q.2)) =
      ν.map (fun q => Fin.snoc q.1 q.2) ⊗ₘ η.comap _ measurable_init_last := by
  have hm : Measurable fun q : ((Fin k → E) × E) × β =>
      ((Fin.snoc q.1.1 q.1.2 : Fin (k + 1) → E), q.2) :=
    (measurable_snoc.comp measurable_fst).prodMk measurable_snd
  ext s hs
  rw [Measure.map_apply hm hs, Measure.compProd_apply (hm hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_snoc]
  refine lintegral_congr fun q => ?_
  rw [Kernel.comap_apply, Fin.init_snoc, Fin.snoc_last]
  rfl

private theorem indepFun_prodMk_comp {Ω β γ δ ε : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [MeasurableSpace ε] {X : Ω → β} {Y : Ω → γ} (hX : Measurable X)
    (hY : Measurable Y) (hXY : IndepFun X Y P) {f : γ → δ} {g : γ → ε} (hf : Measurable f)
    (hg : Measurable g) (hfg : IndepFun (fun ω => f (Y ω)) (fun ω => g (Y ω)) P) :
    IndepFun (fun ω => (X ω, f (Y ω))) (fun ω => g (Y ω)) P := by
  have hfY : Measurable fun ω => f (Y ω) := hf.comp hY
  have hgY : Measurable fun ω => g (Y ω) := hg.comp hY
  have h1 : IndepFun X (fun ω => (f (Y ω), g (Y ω))) P := hXY.comp measurable_id (hf.prodMk hg)
  have h2 : IndepFun X (fun ω => f (Y ω)) P := hXY.comp measurable_id hf
  have h3 := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
    (hfY.prodMk hgY).aemeasurable).1 h1
  rw [(indepFun_iff_map_prod_eq_prod_map_map hfY.aemeasurable hgY.aemeasurable).1 hfg] at h3
  rw [indepFun_iff_map_prod_eq_prod_map_map (hX.prodMk hfY).aemeasurable hgY.aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hfY.aemeasurable).1 h2]
  calc P.map (fun ω => ((X ω, f (Y ω)), g (Y ω)))
      = (P.map fun ω => (X ω, (f (Y ω), g (Y ω)))).map MeasurableEquiv.prodAssoc.symm := by
        rw [Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
          (hX.prodMk (hfY.prodMk hgY))]
        rfl
    _ = _ := by
        rw [h3, ← Measure.prodAssoc_prod, Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
          MeasurableEquiv.prodAssoc.measurable, MeasurableEquiv.symm_comp_self, Measure.map_id]

/-- The squared distance to a point, integrated against a centred Gaussian, as a real integral. -/
private theorem lintegral_enorm_add_sq_multivariateGaussian (S : Matrix n n ℝ)
    (d : EuclideanSpace ℝ n) :
    ∫⁻ u, ‖u + d‖ₑ ^ 2 ∂multivariateGaussian 0 S =
      ENNReal.ofReal (∫ u, ‖u + d‖ ^ 2 ∂multivariateGaussian 0 S) := by
  have hL2 : MemLp (fun u : EuclideanSpace ℝ n => u + d) 2 (multivariateGaussian 0 S) :=
    (IsGaussian.memLp_two_id (μ := multivariateGaussian 0 S)).add (memLp_const d)
  rw [ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2)
    (ae_of_all _ fun _ => by positivity)]
  refine lintegral_congr fun u => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **Bias–variance decomposition for a Gaussian.** -/
private theorem lintegral_enorm_sub_sq_multivariateGaussian (m c : EuclideanSpace ℝ n)
    (S : Matrix n n ℝ) :
    ∫⁻ y, ‖y - c‖ₑ ^ 2 ∂multivariateGaussian m S =
      ∫⁻ u, ‖u‖ₑ ^ 2 ∂multivariateGaussian 0 S + ‖m - c‖ₑ ^ 2 := by
  let ν := multivariateGaussian (0 : EuclideanSpace ℝ n) S
  have hν : multivariateGaussian m S = ν.map (m + ·) := by
    rw [map_add_multivariateGaussian, add_zero]
  rw [hν, lintegral_map (by fun_prop) (by fun_prop)]
  have h0 := lintegral_enorm_add_sq_multivariateGaussian S 0
  simp_rw [add_zero] at h0
  simp_rw [show ∀ u : EuclideanSpace ℝ n, m + u - c = u + (m - c) from fun u => by abel]
  rw [lintegral_enorm_add_sq_multivariateGaussian, h0]
  have hint : Integrable (fun u : EuclideanSpace ℝ n => u) ν :=
    IsGaussian.integrable_id (μ := ν)
  have hcross : ∫ u, ⟪u, m - c⟫ ∂ν = 0 := by
    simp_rw [real_inner_comm (m - c)]
    rw [integral_inner hint, integral_id_multivariateGaussian, inner_zero_right]
  have hL2 : MemLp (fun u : EuclideanSpace ℝ n => u) 2 ν := IsGaussian.memLp_two_id (μ := ν)
  have hsq : Integrable (fun u : EuclideanSpace ℝ n => ‖u‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  have hlin : Integrable (fun u : EuclideanSpace ℝ n => 2 * ⟪u, m - c⟫) ν :=
    (hint.inner_const (m - c)).const_mul 2
  have h12 : Integrable (fun u : EuclideanSpace ℝ n => ‖u‖ ^ 2 + 2 * ⟪u, m - c⟫) ν := hsq.add hlin
  simp_rw [norm_add_sq_real]
  rw [integral_add h12 (integrable_const _), integral_add hsq hlin, integral_const_mul,
    hcross, integral_const, probReal_univ, one_smul, mul_zero, add_zero,
    ENNReal.ofReal_add (integral_nonneg fun _ => by positivity) (by positivity),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end StepLemmas

/-! ### The filter over an observation history -/

section History

variable {r : Type*} [Fintype r]

/-- **Predicted beliefs of the Kalman filter.** For $j \in \mathbb{N}$ let $F_j$ be real
$n \times n$ matrices, $G_j$ real $n \times r$ matrices, $Q_j$ real $r \times r$ matrices, $H_j$
real $n \times p$ matrices and $R_j$ real $p \times p$ matrices, and let $b_0$ be a belief with mean
$\bar x_0$ and covariance $P_0$. For observations $z_0, \dots, z_{k-1} \in \mathbb{R}^p$, the
predicted belief $(\hat x_{k|k-1}, \Sigma_{k|k-1})$ is defined by recursion on $k$. It is
$(\bar x_0, P_0)$ for $k = 0$, and
$$\hat x_{k+1|k} = F_k \hat x_{k|k}, \qquad
\Sigma_{k+1|k} = F_k \Sigma_{k|k} F_k^\top + G_k Q_k G_k^\top,$$
where $(\hat x_{k|k}, \Sigma_{k|k})$ is the update of $(\hat x_{k|k-1}, \Sigma_{k|k-1})$ with
observation matrix $H_k^\top$, noise covariance $R_k$ and observation $z_k$:
$\hat x_{k|k} = \hat x_{k|k-1} + K_k (z_k - H_k^\top \hat x_{k|k-1})$ and
$\Sigma_{k|k} = (I - K_k H_k^\top) \Sigma_{k|k-1}$ with the gain
$K_k = \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1}$, where the inverse is taken to
be $0$ when the matrix is singular.

In the linear Gaussian signal model with horizon $N \ge k$, $x_{j+1} = F_j x_j + G_j w_j$ for
$j < N$ and $z_j = H_j^\top x_j + v_j$ for $j \le N$, with mutually independent
$x_0 \sim N(\bar x_0, P_0)$, $w_j \sim N(0, Q_j)$ and $v_j \sim N(0, R_j)$, $P_0$ and $Q_j$
positive semidefinite and $R_j$ positive definite, $N(\hat x_{k|k-1}, \Sigma_{k|k-1})$ is the
conditional law of $x_k$ given $z_0, \dots, z_{k-1}$ for almost every history under its law
(`condDistrib_observationHistory`). When one of the inverted matrices is singular, the zero
inverse is only a convention, and the predicted belief need not be that conditional law. -/
noncomputable def predictedBelief (F : ℕ → Matrix n n ℝ) (G : ℕ → Matrix n r ℝ)
    (Q : ℕ → Matrix r r ℝ) (H : ℕ → Matrix n p ℝ) (R : ℕ → Matrix p p ℝ) (b₀ : Belief n) :
    (k : ℕ) → (Fin k → EuclideanSpace ℝ p) → Belief n
  | 0, _ => b₀
  | k + 1, ζ => predict (F k) (G k * Q k * (G k)ᵀ)
      (update (H k)ᵀ (R k) (ζ (Fin.last k)) (predictedBelief F G Q H R b₀ k (Fin.init ζ)))

/-- **Filtered beliefs of the Kalman filter.** For $j \in \mathbb{N}$ let $F_j$ be real
$n \times n$ matrices, $G_j$ real $n \times r$ matrices, $Q_j$ real $r \times r$ matrices, $H_j$
real $n \times p$ matrices and $R_j$ real $p \times p$ matrices, and let $b_0$ be a belief with mean
$\bar x_0$ and covariance $P_0$. For observations $z_0, \dots, z_k \in \mathbb{R}^p$, the filtered
belief $(\hat x_{k|k}, \Sigma_{k|k})$ is
$$\hat x_{k|k} = \hat x_{k|k-1} + K_k (z_k - H_k^\top \hat x_{k|k-1}), \qquad
\Sigma_{k|k} = (I - K_k H_k^\top) \Sigma_{k|k-1},$$
with the gain $K_k = \Sigma_{k|k-1} H_k (H_k^\top \Sigma_{k|k-1} H_k + R_k)^{-1}$, where
$(\hat x_{k|k-1}, \Sigma_{k|k-1})$ is the predicted belief of the Kalman filter with these matrices
and $b_0$ after $z_0, \dots, z_{k-1}$, and the inverse is taken to be $0$ when the matrix is
singular.

In the linear Gaussian signal model with horizon $N \ge k$, $x_{j+1} = F_j x_j + G_j w_j$ for
$j < N$ and $z_j = H_j^\top x_j + v_j$ for $j \le N$, with mutually independent
$x_0 \sim N(\bar x_0, P_0)$, $w_j \sim N(0, Q_j)$ and $v_j \sim N(0, R_j)$, $P_0$ and $Q_j$
positive semidefinite and $R_j$ positive definite, $N(\hat x_{k|k}, \Sigma_{k|k})$ is the
conditional law of $x_k$ given $z_0, \dots, z_k$ for almost every history under its law
(`condDistrib_observationHistory`). When one of the inverted matrices is singular, the zero
inverse is only a convention, and the filtered belief need not be that conditional law. -/
noncomputable def filteredBelief (F : ℕ → Matrix n n ℝ) (G : ℕ → Matrix n r ℝ)
    (Q : ℕ → Matrix r r ℝ) (H : ℕ → Matrix n p ℝ) (R : ℕ → Matrix p p ℝ) (b₀ : Belief n)
    (k : ℕ) (ζ : Fin (k + 1) → EuclideanSpace ℝ p) : Belief n :=
  update (H k)ᵀ (R k) (ζ (Fin.last k)) (predictedBelief F G Q H R b₀ k (Fin.init ζ))

section Lemmas

variable {F : ℕ → Matrix n n ℝ} {G : ℕ → Matrix n r ℝ} {Q : ℕ → Matrix r r ℝ}
  {H : ℕ → Matrix n p ℝ} {R : ℕ → Matrix p p ℝ} {b₀ : Belief n}

private theorem update_cov_congr (H : Matrix p n ℝ) (R : Matrix p p ℝ)
    (y y' : EuclideanSpace ℝ p) {b b' : Belief n} (h : b.cov = b'.cov) :
    (update H R y b).cov = (update H R y' b').cov := by
  simp only [update, gain, h]

private theorem predictedBelief_cov_eq :
    ∀ (k : ℕ) (ζ ζ' : Fin k → EuclideanSpace ℝ p),
      (predictedBelief F G Q H R b₀ k ζ).cov = (predictedBelief F G Q H R b₀ k ζ').cov
  | 0, _, _ => rfl
  | k + 1, ζ, ζ' => by
    simp only [predictedBelief, predict]
    rw [update_cov_congr _ _ _ (ζ' (Fin.last k)) (predictedBelief_cov_eq k _ (Fin.init ζ'))]

private theorem filteredBelief_cov_eq (k : ℕ) (ζ ζ' : Fin (k + 1) → EuclideanSpace ℝ p) :
    (filteredBelief F G Q H R b₀ k ζ).cov = (filteredBelief F G Q H R b₀ k ζ').cov :=
  update_cov_congr _ _ _ _ (predictedBelief_cov_eq k _ _)

omit [DecidableEq n] in
/-- The gain only depends on the covariance. -/
private theorem gain_congr (H : Matrix p n ℝ) (R : Matrix p p ℝ) {b b' : Belief n}
    (h : b.cov = b'.cov) : gain H R b = gain H R b' := by
  simp only [gain, h]

private theorem continuous_update_mean (H : Matrix p n ℝ) (R : Matrix p p ℝ) {α : Type*}
    [TopologicalSpace α] {f : α → Belief n} {y : α → EuclideanSpace ℝ p}
    (hf : Continuous fun a => (f a).mean) (hy : Continuous y) {c : Belief n}
    (hc : ∀ a, (f a).cov = c.cov) : Continuous fun a => (update H R (y a) (f a)).mean := by
  simp only [update, gain_congr H R (hc _)]
  exact hf.add ((continuous_toEuclideanLin _).comp (hy.sub ((continuous_toEuclideanLin _).comp hf)))

private theorem continuous_predictedBelief_mean :
    ∀ k : ℕ, Continuous fun ζ : Fin k → EuclideanSpace ℝ p =>
      (predictedBelief F G Q H R b₀ k ζ).mean
  | 0 => by simp only [predictedBelief]; exact continuous_const
  | k + 1 => by
    simp only [predictedBelief, predict]
    exact (continuous_toEuclideanLin _).comp (continuous_update_mean _ _
      ((continuous_predictedBelief_mean k).comp (by fun_prop)) (continuous_apply _)
      (c := predictedBelief F G Q H R b₀ k 0) fun ζ => predictedBelief_cov_eq k _ _)

private theorem continuous_filteredBelief_mean (k : ℕ) :
    Continuous fun ζ : Fin (k + 1) → EuclideanSpace ℝ p =>
      (filteredBelief F G Q H R b₀ k ζ).mean :=
  continuous_update_mean _ _ ((continuous_predictedBelief_mean k).comp (by fun_prop))
    (continuous_apply _) (c := predictedBelief F G Q H R b₀ k 0)
    fun ζ => predictedBelief_cov_eq k _ _

end Lemmas

variable [DecidableEq r] in
/-- **The Kalman filter gives the conditional law given the whole observation history.** Fix a
horizon $N$. For $j \in \mathbb{N}$ let $F_j$ be real $n \times n$ matrices, $G_j$ real
$n \times r$ matrices, $Q_j$ real $r \times r$ matrices, positive semidefinite for $j < N$, $H_j$
real $n \times p$ matrices and $R_j$ real $p \times p$ matrices, positive definite for $j \le N$,
and let $b_0$ be a belief with mean $\bar x_0$ and positive semidefinite covariance $P_0$. On a
probability space let $x_j$, $w_j$, $v_j$ and $z_j$ be random vectors in $\mathbb{R}^n$,
$\mathbb{R}^r$, $\mathbb{R}^p$ and $\mathbb{R}^p$, with $x_0$, $w_j$ ($j < N$) and $v_j$
($j \le N$) measurable, satisfying the linear Gaussian signal model
$x_{j+1} = F_j x_j + G_j w_j$ for $j < N$ and $z_j = H_j^\top x_j + v_j$ for $j \le N$, where
$x_0, w_0, \dots, w_{N-1}, v_0, \dots, v_N$ are mutually independent with
$x_0 \sim N(\bar x_0, P_0)$, $w_j \sim N(0, Q_j)$ and $v_j \sim N(0, R_j)$ (their joint law is
the product of these laws). Write $Z_{k-1} = (z_0, \dots, z_{k-1})$ and $Z_k = (z_0, \dots, z_k)$,
and let $(\hat x_{k|k-1}, \Sigma_{k|k-1})$ and $(\hat x_{k|k}, \Sigma_{k|k})$ be the predicted and
filtered beliefs of the Kalman filter. Then for every $k \le N$:

* for almost every value of $Z_{k-1}$ under its law, the conditional distribution of $x_k$ given
  $Z_{k-1}$ is $N(\hat x_{k|k-1}(Z_{k-1}), \Sigma_{k|k-1})$, and for almost every value of $Z_k$,
  the conditional distribution of $x_k$ given $Z_k$ is $N(\hat x_{k|k}(Z_k), \Sigma_{k|k})$;
* $\Sigma_{k|k}$ does not depend on the observations;
* $\hat x_{k|k}(Z_k) = E[x_k \mid Z_k]$ almost surely;
* for every measurable $g$, $E\|x_k - \hat x_{k|k}(Z_k)\|^2 \le E\|x_k - g(Z_k)\|^2$, with
  equality if and only if $g(Z_k) = \hat x_{k|k}(Z_k)$ almost surely; the mean squared errors are
  expectations in $[0, \infty]$.

(Anderson and Moore, *Optimal Filtering*, Prentice-Hall (1979), Section 3.1, equations
(1.6)–(1.12) and property 5.) -/
theorem condDistrib_observationHistory {N : ℕ} {F : ℕ → Matrix n n ℝ} {G : ℕ → Matrix n r ℝ}
    {Q : ℕ → Matrix r r ℝ} {H : ℕ → Matrix n p ℝ} {R : ℕ → Matrix p p ℝ} {b₀ : Belief n}
    (hP₀ : b₀.Valid) (hQ : ∀ k < N, (Q k).PosSemidef) (hR : ∀ k ≤ N, (R k).PosDef)
    {x : ℕ → Ω → EuclideanSpace ℝ n} {w : ℕ → Ω → EuclideanSpace ℝ r}
    {v z : ℕ → Ω → EuclideanSpace ℝ p} (hx₀ : Measurable (x 0))
    (hw : ∀ k < N, Measurable (w k)) (hv : ∀ k ≤ N, Measurable (v k))
    (hx : ∀ k < N, ∀ ω,
      x (k + 1) ω = toEuclideanLin (F k) (x k ω) + toEuclideanLin (G k) (w k ω))
    (hz : ∀ k ≤ N, ∀ ω, z k ω = toEuclideanLin (H k)ᵀ (x k ω) + v k ω)
    (hlaw : P.map (fun ω => (x 0 ω, (fun i : Fin N => w i ω), fun i : Fin (N + 1) => v i ω)) =
      b₀.law.prod ((Measure.pi fun i : Fin N => multivariateGaussian 0 (Q i)).prod
        (Measure.pi fun i : Fin (N + 1) => multivariateGaussian 0 (R i))))
    {k : ℕ} (hk : k ≤ N) :
    (∀ᵐ ζ ∂P.map (fun ω (i : Fin k) => z i ω),
      condDistrib (x k) (fun ω (i : Fin k) => z i ω) P ζ =
        (predictedBelief F G Q H R b₀ k ζ).law) ∧
    (∀ᵐ ζ ∂P.map (fun ω (i : Fin (k + 1)) => z i ω),
      condDistrib (x k) (fun ω (i : Fin (k + 1)) => z i ω) P ζ =
        (filteredBelief F G Q H R b₀ k ζ).law) ∧
    (∀ ζ ζ', (filteredBelief F G Q H R b₀ k ζ).cov = (filteredBelief F G Q H R b₀ k ζ').cov) ∧
    P[x k | MeasurableSpace.comap (fun ω (i : Fin (k + 1)) => z i ω) inferInstance] =ᵐ[P]
      (fun ω => (filteredBelief F G Q H R b₀ k fun i => z i ω).mean) ∧
    ∀ g : (Fin (k + 1) → EuclideanSpace ℝ p) → EuclideanSpace ℝ n, Measurable g →
      ∫⁻ ω, ‖x k ω - (filteredBelief F G Q H R b₀ k fun i => z i ω).mean‖ₑ ^ 2 ∂P ≤
          ∫⁻ ω, ‖x k ω - g fun i => z i ω‖ₑ ^ 2 ∂P ∧
        (∫⁻ ω, ‖x k ω - g fun i => z i ω‖ₑ ^ 2 ∂P =
            ∫⁻ ω, ‖x k ω - (filteredBelief F G Q H R b₀ k fun i => z i ω).mean‖ₑ ^ 2 ∂P ↔
          (fun ω => g fun i => z i ω) =ᵐ[P]
            fun ω => (filteredBelief F G Q H R b₀ k fun i => z i ω).mean) := by
  let Z : (j : ℕ) → Ω → Fin j → EuclideanSpace ℝ p := fun j ω i => z i ω
  /- The noise blocks: laws and independence. -/
  have : IsProbabilityMeasure b₀.law := by rw [Belief.law]; infer_instance
  have hWm : Measurable fun ω (i : Fin N) => w i ω := measurable_pi_iff.2 fun i : Fin N => hw i i.2
  have hVm : Measurable fun ω (i : Fin (N + 1)) => v i ω :=
    measurable_pi_iff.2 fun i : Fin (N + 1) => hv i (Nat.lt_succ_iff.1 i.2)
  have hWVm := hWm.prodMk hVm
  have hξ := hx₀.prodMk hWVm
  have hlaw0 : P.map (x 0) = b₀.law := by
    have h := congrArg (Measure.map Prod.fst) hlaw
    rwa [Measure.map_map measurable_fst hξ, Measure.map_fst_prod, measure_univ, one_smul] at h
  have hlawWV : P.map (fun ω => ((fun i : Fin N => w i ω), fun i : Fin (N + 1) => v i ω)) =
      (Measure.pi fun i : Fin N => multivariateGaussian 0 (Q i)).prod
        (Measure.pi fun i : Fin (N + 1) => multivariateGaussian 0 (R i)) := by
    have h := congrArg (Measure.map Prod.snd) hlaw
    rwa [Measure.map_map measurable_snd hξ, Measure.map_snd_prod, measure_univ, one_smul] at h
  have hlawW : P.map (fun ω (i : Fin N) => w i ω) =
      Measure.pi fun i : Fin N => multivariateGaussian 0 (Q i) := by
    have h := congrArg (Measure.map Prod.fst) hlawWV
    rwa [Measure.map_map measurable_fst hWVm, Measure.map_fst_prod, measure_univ, one_smul] at h
  have hlawV : P.map (fun ω (i : Fin (N + 1)) => v i ω) =
      Measure.pi fun i : Fin (N + 1) => multivariateGaussian 0 (R i) := by
    have h := congrArg (Measure.map Prod.snd) hlawWV
    rwa [Measure.map_map measurable_snd hWVm, Measure.map_snd_prod, measure_univ, one_smul] at h
  have hind0 : IndepFun (x 0)
      (fun ω => ((fun i : Fin N => w i ω), fun i : Fin (N + 1) => v i ω)) P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hx₀.aemeasurable hWVm.aemeasurable, hlaw0, hlawWV]
    exact hlaw
  have hindWV : IndepFun (fun ω (i : Fin N) => w i ω) (fun ω (i : Fin (N + 1)) => v i ω) P := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable hVm.aemeasurable, hlawW, hlawV]
    exact hlawWV
  have hlawvF : ∀ i : Fin (N + 1), P.map (v i) = multivariateGaussian 0 (R i) := fun i => by
    have h := congrArg (Measure.map (Function.eval i)) hlawV
    rw [Measure.map_map (measurable_pi_apply i) hVm, Measure.pi_map_eval] at h
    simpa [Function.comp_def] using h
  have hlawwF : ∀ i : Fin N, P.map (w i) = multivariateGaussian 0 (Q i) := fun i => by
    have h := congrArg (Measure.map (Function.eval i)) hlawW
    rw [Measure.map_map (measurable_pi_apply i) hWm, Measure.pi_map_eval] at h
    simpa [Function.comp_def] using h
  have hlawv : ∀ i ≤ N, P.map (v i) = multivariateGaussian 0 (R i) := fun i hi =>
    hlawvF ⟨i, Nat.lt_succ_of_le hi⟩
  have hlaww : ∀ i < N, P.map (w i) = multivariateGaussian 0 (Q i) := fun i hi => hlawwF ⟨i, hi⟩
  have hiv : iIndepFun (fun i : Fin (N + 1) => v i) P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map
      fun i : Fin (N + 1) => (hv i (Nat.lt_succ_iff.1 i.2)).aemeasurable, hlawV]
    simp_rw [hlawvF]
  have hiw : iIndepFun (fun i : Fin N => w i) P := by
    rw [iIndepFun_iff_map_fun_eq_pi_map fun i : Fin N => (hw i i.2).aemeasurable, hlawW]
    simp_rw [hlawwF]
  /- Measurability and integrability of the state and the observations. -/
  have hxmi : ∀ j ≤ N, Measurable (x j) ∧ Integrable (x j) P := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨hx₀, ?_⟩
      have h : Integrable id (P.map (x 0)) := by
        rw [hlaw0, Belief.law]; exact IsGaussian.integrable_id
      exact (integrable_map_measure aestronglyMeasurable_id hx₀.aemeasurable).1 h
    | succ j ih =>
      intro hj
      obtain ⟨hm, hi⟩ := ih (by omega)
      have hwj := hw j (by omega)
      have hwi : Integrable (w j) P := by
        have h : Integrable id (P.map (w j)) := by
          rw [hlaww j (by omega)]; exact IsGaussian.integrable_id
        exact (integrable_map_measure aestronglyMeasurable_id hwj.aemeasurable).1 h
      rw [show x (j + 1) = fun ω => toEuclideanLin (F j) (x j ω) + toEuclideanLin (G j) (w j ω)
        from funext (hx j (by omega))]
      exact ⟨((continuous_toEuclideanLin _).measurable.comp hm).add
          ((continuous_toEuclideanLin _).measurable.comp hwj),
        ((LinearMap.toContinuousLinearMap (toEuclideanLin (F j))).integrable_comp hi).add
          ((LinearMap.toContinuousLinearMap (toEuclideanLin (G j))).integrable_comp hwi)⟩
  have hzm : ∀ j ≤ N, Measurable (z j) := fun j hj => by
    rw [show z j = fun ω => toEuclideanLin (H j)ᵀ (x j ω) + v j ω from funext (hz j hj)]
    exact ((continuous_toEuclideanLin _).measurable.comp (hxmi j hj).1).add (hv j hj)
  have hZm : ∀ j ≤ N + 1, Measurable (Z j) := fun j hj =>
    measurable_pi_iff.2 fun i : Fin j => hzm i (by omega)
  /- The state is measurable for any σ-algebra that makes the initial state and the process
  noise up to the previous time measurable. -/
  have hxcomap : ∀ (m : MeasurableSpace Ω) (j : ℕ), j ≤ N → Measurable[m] (x 0) →
      (∀ i < j, Measurable[m] (w i)) → Measurable[m] (x j) := by
    intro m j
    induction j with
    | zero => intro _ h0 _; exact h0
    | succ j ih =>
      intro hj h0 hwm
      rw [show x (j + 1) = fun ω => toEuclideanLin (F j) (x j ω) + toEuclideanLin (G j) (w j ω)
        from funext (hx j (by omega))]
      exact ((continuous_toEuclideanLin _).measurable.comp
          (ih (by omega) h0 fun i hi => hwm i (by omega))).add
        ((continuous_toEuclideanLin _).measurable.comp (hwm j (by omega)))
  /- The current noises are independent of the past. -/
  have hindv : ∀ j ≤ N, IndepFun (fun ω => (Z j ω, x j ω)) (v j) P := by
    intro j hj
    let j' : Fin (N + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    have h1 := hiv.indepFun_finset (Finset.univ.erase j') {j'} (by simp)
      fun i : Fin (N + 1) => hv i (Nat.lt_succ_iff.1 i.2)
    have h2 : IndepFun (fun ω (i : Finset.univ.erase j') => v i ω) (v j) P :=
      h1.comp measurable_id (measurable_pi_apply
        (⟨j', Finset.mem_singleton_self j'⟩ : ({j'} : Finset (Fin (N + 1)))))
    have h3 := indepFun_prodMk_comp hWm hVm hindWV
      (f := fun g (i : Finset.univ.erase j') => g i) (g := fun g => g j') (by fun_prop)
      (measurable_pi_apply j') h2
    have h4 := indepFun_prodMk_comp hx₀ hWVm hind0
      (f := fun q => (q.1, fun i : Finset.univ.erase j' => q.2 i)) (g := fun q => q.2 j')
      (by fun_prop) (by fun_prop) h3
    rw [IndepFun_iff_Indep] at h4 ⊢
    refine indep_of_indep_of_le_left h4 (Measurable.comap_le ?_)
    let m := MeasurableSpace.comap (fun ω => (x 0 ω, ((fun i : Fin N => w i ω),
      fun i : Finset.univ.erase j' => v i ω))) inferInstance
    have hA : Measurable[m] (fun ω => (x 0 ω, ((fun i : Fin N => w i ω),
        fun i : Finset.univ.erase j' => v i ω))) := measurable_iff_comap_le.2 le_rfl
    have h0 : Measurable[m] (x 0) := measurable_fst.comp hA
    have hwm : ∀ i < j, Measurable[m] (w i) := fun i hi =>
      (measurable_pi_apply (⟨i, by omega⟩ : Fin N)).comp (measurable_fst.comp
        (measurable_snd.comp hA))
    have hvm : ∀ i < j, Measurable[m] (v i) := fun i hi =>
      (measurable_pi_apply (⟨⟨i, by omega⟩, Finset.mem_erase.2 ⟨fun h => by
        simp [j', Fin.ext_iff] at h; omega, Finset.mem_univ _⟩⟩ : Finset.univ.erase j')).comp
        (measurable_snd.comp (measurable_snd.comp hA))
    have hzj : ∀ i < j, Measurable[m] (z i) := fun i hi => by
      rw [show z i = fun ω => toEuclideanLin (H i)ᵀ (x i ω) + v i ω from funext (hz i (by omega))]
      exact ((continuous_toEuclideanLin _).measurable.comp
        (hxcomap m i (by omega) h0 fun l hl => hwm l (by omega))).add (hvm i hi)
    exact (measurable_pi_iff.2 fun i : Fin j => hzj i i.2).prodMk (hxcomap m j hj h0 hwm)
  have hindw : ∀ j < N, IndepFun (fun ω => (Z (j + 1) ω, x j ω)) (w j) P := by
    intro j hj
    let j' : Fin N := ⟨j, hj⟩
    have h1 := hiw.indepFun_finset (Finset.univ.erase j') {j'} (by simp) fun i : Fin N => hw i i.2
    have h2 : IndepFun (fun ω (i : Finset.univ.erase j') => w i ω) (w j) P :=
      h1.comp measurable_id (measurable_pi_apply
        (⟨j', Finset.mem_singleton_self j'⟩ : ({j'} : Finset (Fin N))))
    have h3 := indepFun_prodMk_comp hVm hWm hindWV.symm
      (f := fun g (i : Finset.univ.erase j') => g i) (g := fun g => g j') (by fun_prop)
      (measurable_pi_apply j') h2
    have h4 := indepFun_prodMk_comp hx₀ hWVm hind0
      (f := fun q => (q.2, fun i : Finset.univ.erase j' => q.1 i)) (g := fun q => q.1 j')
      (by fun_prop) (by fun_prop) h3
    rw [IndepFun_iff_Indep] at h4 ⊢
    refine indep_of_indep_of_le_left h4 (Measurable.comap_le ?_)
    let m := MeasurableSpace.comap (fun ω => (x 0 ω, ((fun i : Fin (N + 1) => v i ω),
      fun i : Finset.univ.erase j' => w i ω))) inferInstance
    have hA : Measurable[m] (fun ω => (x 0 ω, ((fun i : Fin (N + 1) => v i ω),
        fun i : Finset.univ.erase j' => w i ω))) := measurable_iff_comap_le.2 le_rfl
    have h0 : Measurable[m] (x 0) := measurable_fst.comp hA
    have hwm : ∀ i < j, Measurable[m] (w i) := fun i hi =>
      (measurable_pi_apply (⟨⟨i, by omega⟩, Finset.mem_erase.2 ⟨fun h => by
        simp [j', Fin.ext_iff] at h; omega, Finset.mem_univ _⟩⟩ : Finset.univ.erase j')).comp
        (measurable_snd.comp (measurable_snd.comp hA))
    have hvm : ∀ i ≤ j, Measurable[m] (v i) := fun i hi =>
      (measurable_pi_apply (⟨i, by omega⟩ : Fin (N + 1))).comp (measurable_fst.comp
        (measurable_snd.comp hA))
    have hzj : ∀ i ≤ j, Measurable[m] (z i) := fun i hi => by
      rw [show z i = fun ω => toEuclideanLin (H i)ᵀ (x i ω) + v i ω from funext (hz i (by omega))]
      exact ((continuous_toEuclideanLin _).measurable.comp
        (hxcomap m i (by omega) h0 fun l hl => hwm l (by omega))).add (hvm i hi)
    exact (measurable_pi_iff.2 fun i : Fin (j + 1) => hzj i (Nat.lt_succ_iff.1 i.2)).prodMk
      (hxcomap m j hj.le h0 hwm)
  /- Validity of the beliefs and invertibility of the innovation covariances. -/
  have hpred : ∀ j ≤ N, ∀ ζ, (predictedBelief F G Q H R b₀ j ζ).Valid := by
    intro j
    induction j with
    | zero => intro _ _; exact hP₀
    | succ j ih =>
      intro hj ζ
      have hGQ : (G j * Q j * (G j)ᵀ).PosSemidef := by
        simpa [conjTranspose_eq_transpose_of_trivial] using
          (hQ j (by omega)).mul_mul_conjTranspose_same (G j)
      exact predict_valid _ _ (update_valid _ _ (ih (by omega) _) (hR j (by omega))) hGQ
  have hfilt : ∀ j ≤ N, ∀ ζ, (filteredBelief F G Q H R b₀ j ζ).Valid := fun j hj ζ =>
    update_valid _ _ (hpred j hj _) (hR j hj)
  have hinv : ∀ j ≤ N, ∀ ζ, IsUnit ((H j)ᵀ * (predictedBelief F G Q H R b₀ j ζ).cov *
      (H j)ᵀᵀ + R j).det := by
    intro j hj ζ
    have hHS : ((H j)ᵀ * (predictedBelief F G Q H R b₀ j ζ).cov * (H j)ᵀᵀ).PosSemidef := by
      simpa [conjTranspose_eq_transpose_of_trivial] using
        (hpred j hj ζ).mul_mul_conjTranspose_same (H j)ᵀ
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.posSemidef_add hHS (hR j hj)).isUnit
  /- The conditional laws, as kernels. -/
  let priorK : (j : ℕ) → Kernel (Fin j → EuclideanSpace ℝ p) (EuclideanSpace ℝ n) := fun j =>
    noiseKernel (fun ζ => (predictedBelief F G Q H R b₀ j ζ).mean)
      (continuous_predictedBelief_mean j).measurable
      (multivariateGaussian 0 (predictedBelief F G Q H R b₀ j 0).cov)
  let postK : (j : ℕ) → Kernel (Fin (j + 1) → EuclideanSpace ℝ p) (EuclideanSpace ℝ n) :=
    fun j => noiseKernel (fun ζ => (filteredBelief F G Q H R b₀ j ζ).mean)
      (continuous_filteredBelief_mean j).measurable
      (multivariateGaussian 0 (filteredBelief F G Q H R b₀ j 0).cov)
  have hpriorK : ∀ j ζ, priorK j ζ = (predictedBelief F G Q H R b₀ j ζ).law := fun j ζ => by
    simp only [priorK]
    rw [noiseKernel_multivariateGaussian_apply, Belief.law, predictedBelief_cov_eq j ζ 0]
  have hpostK : ∀ j ζ, postK j ζ = (filteredBelief F G Q H R b₀ j ζ).law := fun j ζ => by
    simp only [postK]
    rw [noiseKernel_multivariateGaussian_apply, Belief.law, filteredBelief_cov_eq j ζ 0]
  /- The induction: predict and update steps. -/
  have hA0 : P.map (fun ω => (Z 0 ω, x 0 ω)) = P.map (Z 0) ⊗ₘ priorK 0 := by
    have hc : Z 0 = fun (_ : Ω) (i : Fin 0) => (Fin.elim0 i : EuclideanSpace ℝ p) :=
      funext fun ω => funext fun i => Fin.elim0 i
    have hind : IndepFun (Z 0) (x 0) P := by rw [hc]; exact indepFun_const_left _ _
    rw [(indepFun_iff_map_prod_eq_prod_map_map (hZm 0 (by omega)).aemeasurable
      hx₀.aemeasurable).1 hind, hlaw0, ← Measure.compProd_const]
    congr 1
    exact Kernel.ext fun ζ => by rw [Kernel.const_apply, hpriorK]; rfl
  have hAB : ∀ j ≤ N, P.map (fun ω => (Z j ω, x j ω)) = P.map (Z j) ⊗ₘ priorK j →
      P.map (fun ω => (Z (j + 1) ω, x j ω)) = P.map (Z (j + 1)) ⊗ₘ postK j := by
    intro j hj hA
    have hZj := hZm j (by omega)
    have hxj := (hxmi j hj).1
    have h1 : P.map (fun ω => ((Z j ω, x j ω), v j ω)) =
        (P.map (Z j) ⊗ₘ priorK j).prod (multivariateGaussian 0 (R j)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map (hZj.prodMk hxj).aemeasurable
        (hv j hj).aemeasurable).1 (hindv j hj), hA, hlawv j hj]
    have h2 := map_compProd_prod_update (P.map (Z j))
      (fun ζ => (predictedBelief F G Q H R b₀ j ζ).mean)
      (continuous_predictedBelief_mean j).measurable (hpred j hj 0) (hR j hj).posSemidef
      (H j)ᵀ (hinv j hj 0)
    rw [← h1, Measure.map_map (by fun_prop) ((hZj.prodMk hxj).prodMk (hv j hj))] at h2
    have h3 := (show P.map (fun ω => ((Z j ω, z j ω), x j ω)) =
        P.map ((fun q => ((q.1.1, toEuclideanLin (H j)ᵀ q.1.2 + q.2), q.1.2)) ∘
          fun ω => ((Z j ω, x j ω), v j ω)) by
      congr 1
      funext ω
      simp only [Function.comp_apply, hz j hj ω]).trans h2
    have hmarg := congrArg Measure.fst h3
    rw [Measure.fst_compProd, Measure.fst_map_prodMk (hZj.prodMk (hzm j hj)) hxj] at hmarg
    have hsnoc : ∀ ω, (Fin.snoc (Z j ω) (z j ω) : Fin (j + 1) → EuclideanSpace ℝ p) =
        Z (j + 1) ω := fun ω => by
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i <;> simp [Z]
    calc P.map (fun ω => (Z (j + 1) ω, x j ω))
        = (P.map fun ω => ((Z j ω, z j ω), x j ω)).map
            (fun q => (Fin.snoc q.1.1 q.1.2, q.2)) := by
          have hsn : Measurable fun q : ((Fin j → EuclideanSpace ℝ p) × EuclideanSpace ℝ p) ×
              EuclideanSpace ℝ n => ((Fin.snoc q.1.1 q.1.2 : Fin (j + 1) → _), q.2) :=
            (measurable_snoc.comp measurable_fst).prodMk measurable_snd
          rw [Measure.map_map hsn ((hZj.prodMk (hzm j hj)).prodMk hxj)]
          congr 1
          funext ω
          simp only [Function.comp_apply, hsnoc]
      _ = (P.map fun ω => (Z j ω, z j ω)).map (fun q => Fin.snoc q.1 q.2) ⊗ₘ
            Kernel.comap _ _ measurable_init_last := by
          rw [h3, ← hmarg, map_snoc_compProd]
      _ = P.map (Z (j + 1)) ⊗ₘ postK j := by
          rw [Measure.map_map measurable_snoc (hZj.prodMk (hzm j hj))]
          congr 1
          · congr 1
            funext ω
            exact hsnoc ω
          · refine Kernel.ext fun ζ => ?_
            simp only [postK]
            rw [Kernel.comap_apply, noiseKernel_multivariateGaussian_apply,
              noiseKernel_multivariateGaussian_apply]
            congr 1
            · simp only [filteredBelief, update, gain, predictedBelief_cov_eq j (Fin.init ζ) 0]
            · rw [filteredBelief, update_cov_eq,
                predictedBelief_cov_eq j (Fin.init (0 : Fin (j + 1) → EuclideanSpace ℝ p)) 0]
  have hBA : ∀ j < N, P.map (fun ω => (Z (j + 1) ω, x j ω)) = P.map (Z (j + 1)) ⊗ₘ postK j →
      P.map (fun ω => (Z (j + 1) ω, x (j + 1) ω)) = P.map (Z (j + 1)) ⊗ₘ priorK (j + 1) := by
    intro j hj hB
    have hZj := hZm (j + 1) (by omega)
    have hxj := (hxmi j hj.le).1
    have h1 : P.map (fun ω => ((Z (j + 1) ω, x j ω), w j ω)) =
        (P.map (Z (j + 1)) ⊗ₘ postK j).prod (multivariateGaussian 0 (Q j)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map (hZj.prodMk hxj).aemeasurable
        (hw j hj).aemeasurable).1 (hindw j hj), hB, hlaww j hj]
    have h2 := map_compProd_prod_predict (P.map (Z (j + 1)))
      (fun ζ => (filteredBelief F G Q H R b₀ j ζ).mean)
      (continuous_filteredBelief_mean j).measurable (hfilt j hj.le 0) (hQ j hj) (F j) (G j)
    rw [← h1, Measure.map_map (by fun_prop) ((hZj.prodMk hxj).prodMk (hw j hj))] at h2
    refine ((show P.map (fun ω => (Z (j + 1) ω, x (j + 1) ω)) =
        P.map ((fun q => (q.1.1, toEuclideanLin (F j) q.1.2 + toEuclideanLin (G j) q.2)) ∘
          fun ω => ((Z (j + 1) ω, x j ω), w j ω)) by
      congr 1
      funext ω
      simp only [Function.comp_apply, hx j hj ω]).trans h2).trans ?_
    congr 1
  have key : ∀ j ≤ N, P.map (fun ω => (Z j ω, x j ω)) = P.map (Z j) ⊗ₘ priorK j ∧
      P.map (fun ω => (Z (j + 1) ω, x j ω)) = P.map (Z (j + 1)) ⊗ₘ postK j := by
    intro j
    induction j with
    | zero => intro h0; exact ⟨hA0, hAB 0 h0 hA0⟩
    | succ j ih =>
      intro hj
      have hA := hBA j (by omega) (ih (by omega)).2
      exact ⟨hA, hAB (j + 1) hj hA⟩
  /- The conclusions. -/
  obtain ⟨hA, hB⟩ := key k hk
  have hZk := hZm k (by omega)
  have hZk1 := hZm (k + 1) (by omega)
  have hxk := hxmi k hk
  have h1a : condDistrib (x k) (Z k) P =ᵐ[P.map (Z k)] priorK k :=
    condDistrib_ae_eq_of_measure_eq_compProd hZk.aemeasurable hxk.1.aemeasurable hA
  have h1b : condDistrib (x k) (Z (k + 1)) P =ᵐ[P.map (Z (k + 1))] postK k :=
    condDistrib_ae_eq_of_measure_eq_compProd hZk1.aemeasurable hxk.1.aemeasurable hB
  refine ⟨?_, ?_, filteredBelief_cov_eq k, ?_, ?_⟩
  · filter_upwards [h1a] with ζ hζ
    exact hζ.trans (hpriorK k ζ)
  · filter_upwards [h1b] with ζ hζ
    exact hζ.trans (hpostK k ζ)
  · have hce := condExp_ae_eq_integral_condDistrib' hZk1 hxk.2
    filter_upwards [hce, ae_of_ae_map hZk1.aemeasurable h1b] with ω h1 h2
    rw [h1, h2, hpostK, Belief.law, integral_id_multivariateGaussian]
  · intro g hg
    have : IsProbabilityMeasure (P.map (Z (k + 1))) :=
      (Measure.isProbabilityMeasure_map_iff hZk1.aemeasurable).2 inferInstance
    let mF := fun ζ => (filteredBelief F G Q H R b₀ k ζ).mean
    have hmF : Measurable mF := (continuous_filteredBelief_mean k).measurable
    let C := ∫⁻ u, ‖u‖ₑ ^ 2 ∂multivariateGaussian (0 : EuclideanSpace ℝ n)
      (filteredBelief F G Q H R b₀ k 0).cov
    have hC : C ≠ ⊤ := by
      have h := lintegral_enorm_add_sq_multivariateGaussian
        (filteredBelief F G Q H R b₀ k 0).cov 0
      simp_rw [add_zero] at h
      simp only [C]
      rw [h]
      exact ENNReal.ofReal_ne_top
    have hcost : ∀ h : (Fin (k + 1) → EuclideanSpace ℝ p) → EuclideanSpace ℝ n, Measurable h →
        ∫⁻ ω, ‖x k ω - h (Z (k + 1) ω)‖ₑ ^ 2 ∂P =
          C + ∫⁻ ω, ‖mF (Z (k + 1) ω) - h (Z (k + 1) ω)‖ₑ ^ 2 ∂P := by
      intro h hh
      have hf : Measurable fun q : (Fin (k + 1) → EuclideanSpace ℝ p) × EuclideanSpace ℝ n =>
          ‖q.2 - h q.1‖ₑ ^ 2 := (measurable_snd.sub (hh.comp measurable_fst)).eNorm.pow_const 2
      have hD : Measurable fun ζ => ‖mF ζ - h ζ‖ₑ ^ 2 := (hmF.sub hh).eNorm.pow_const 2
      have e1 : ∫⁻ ω, ‖x k ω - h (Z (k + 1) ω)‖ₑ ^ 2 ∂P =
          ∫⁻ q, ‖q.2 - h q.1‖ₑ ^ 2 ∂(P.map fun ω => (Z (k + 1) ω, x k ω)) :=
        (lintegral_map hf (hZk1.prodMk hxk.1)).symm
      have e2 : ∫⁻ ω, ‖mF (Z (k + 1) ω) - h (Z (k + 1) ω)‖ₑ ^ 2 ∂P =
          ∫⁻ ζ, ‖mF ζ - h ζ‖ₑ ^ 2 ∂(P.map (Z (k + 1))) :=
        (lintegral_map hD hZk1).symm
      rw [e1, e2, hB, Measure.lintegral_compProd hf]
      simp only [postK, noiseKernel_multivariateGaussian_apply,
        lintegral_enorm_sub_sq_multivariateGaussian]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    have hcostF := hcost mF hmF
    simp only [sub_self, eNorm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      lintegral_zero, add_zero] at hcostF
    change ∫⁻ ω, ‖x k ω - mF (Z (k + 1) ω)‖ₑ ^ 2 ∂P ≤ ∫⁻ ω, ‖x k ω - g (Z (k + 1) ω)‖ₑ ^ 2 ∂P ∧
      (∫⁻ ω, ‖x k ω - g (Z (k + 1) ω)‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖x k ω - mF (Z (k + 1) ω)‖ₑ ^ 2 ∂P ↔
        (fun ω => g (Z (k + 1) ω)) =ᵐ[P] fun ω => mF (Z (k + 1) ω))
    rw [hcost g hg, hcostF]
    refine ⟨le_self_add, ?_⟩
    rw [← add_zero C, add_assoc, zero_add, ENNReal.add_right_inj hC,
      lintegral_eq_zero_iff (f := fun ω => ‖mF (Z (k + 1) ω) - g (Z (k + 1) ω)‖ₑ ^ 2)
        (((hmF.comp hZk1).sub (hg.comp hZk1)).eNorm.pow_const 2)]
    constructor
    · intro h0
      filter_upwards [h0] with ω hω
      have h' : ‖mF (Z (k + 1) ω) - g (Z (k + 1) ω)‖ₑ ^ 2 = 0 := hω
      rw [pow_eq_zero_iff two_ne_zero, eNorm_eq_zero, sub_eq_zero] at h'
      exact h'.symm
    · intro h0
      filter_upwards [h0] with ω hω
      simp [hω]

end History

end Cslib.MachineLearning.Sequence.KalmanFilter
