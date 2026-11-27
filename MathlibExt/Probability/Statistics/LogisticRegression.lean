/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import MathlibExt.Analysis.Convex.GradientDescent
public import MathlibExt.Probability.Statistics.GLM.Canonical
import MathlibExt.Analysis.SpecialFunctions.Softplus

/-!
# Logistic negative log-likelihood: convexity, gradient, and descent rate

For a design matrix `X`, outcomes `y`, and coefficients `β`, the summed
logistic negative log-likelihood
`∑ i, [log (1 + exp (x_i ⬝ β)) - y_i (x_i ⬝ β)]` is convex in `β` on
the whole coefficient space. Each summand is the scalar softplus
composed with the linear map `β ↦ x_i ⬝ β`, minus a linear term
(Atlas roadmap ST09.T02). The scalar fact is the shared softplus
convexity `Real.convexOn_softplus`.

The summed NLL is also identified with the negative canonical logistic
GLM log-likelihood at zero offset. Negating the GLM gradient gives
`Xᵀ (σ(Xβ) - y)` on Euclidean coefficient space. Since
`σ(t)(1 - σ(t)) ≤ 1 / 4`, this gradient is Lipschitz with constant
`‖X‖op² / 4`, for the Euclidean operator norm of the design map, and the
existing smooth-convex gradient-descent rate applies whenever a minimizer
is attained. The zero-design and strictly separable cases are treated
separately: the first has constant objective, and the second has no finite
unregularized minimizer.
-/

@[expose] public section


open Finset

namespace MathlibExt.Probability.Statistics.LogisticRegression

/-- The logistic negative log-likelihood (NLL) of binary outcomes `y`
against a design matrix `X` at coefficients `β`:
`∑ i, [log (1 + exp (x_i ⬝ β)) - y_i (x_i ⬝ β)]`.
For binary outcomes `y_i ∈ {0, 1}` this is the usual logistic NLL;
convexity below holds for arbitrary real `y`, since the second term is
linear in `β`. -/
noncomputable def logisticNLL {n m : ℕ} (X : Fin n → Fin m → ℝ) (y : Fin n → ℝ)
    (β : Fin m → ℝ) : ℝ :=
  ∑ i, (Real.log (1 + Real.exp (∑ j, X i j * β j)) - y i * ∑ j, X i j * β j)

/-- **Logistic NLL is convex in the coefficients (ST09.T02).** Each
summand is the scalar softplus composed with the linear map
`β ↦ x_i ⬝ β`, minus a linear term; a sum of convex functions is convex. -/
theorem convexOn_logisticNLL {n m : ℕ} (X : Fin n → Fin m → ℝ) (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ (logisticNLL X y) := by
  set L : Fin n → ((Fin m → ℝ) →ₗ[ℝ] ℝ) :=
    fun i => ∑ j : Fin m, X i j • LinearMap.proj j with hLdef
  have hL : ∀ (i : Fin n) (β : Fin m → ℝ), (L i) β = ∑ j, X i j * β j := by
    intro i β
    simp [hLdef]
  have hsoft : ∀ i : Fin n, ConvexOn ℝ Set.univ
      (fun β : Fin m → ℝ => Real.log (1 + Real.exp ((L i) β))) := by
    intro i
    have h := Real.convexOn_softplus.comp_linearMap (L i)
    rw [Set.preimage_univ] at h
    exact h.congr (fun β _ => rfl)
  have hlinmap : ∀ i : Fin n, ConcaveOn ℝ Set.univ
      (fun β : Fin m → ℝ => y i * ((L i) β)) := by
    intro i
    have h := ((y i) • (L i)).concaveOn convex_univ
    refine h.congr (fun β _ => ?_)
    simp [smul_eq_mul]
  have hsummand : ∀ i : Fin n, ConvexOn ℝ Set.univ
      (fun β : Fin m → ℝ => Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β)) := by
    intro i
    exact ((hsoft i).sub (hlinmap i)).congr (fun β _ => rfl)
  have hsum : ∀ s : Finset (Fin n), ConvexOn ℝ Set.univ
      (fun β : Fin m → ℝ => ∑ i ∈ s,
        (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) := by
    intro s
    refine Finset.induction ?_ ?_ s
    · have hfun : (fun β : Fin m → ℝ => ∑ i ∈ (∅ : Finset (Fin n)),
          (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) = fun _ => 0 := by
        funext β
        simp
      rw [hfun]
      exact convexOn_const 0 convex_univ
    · intro a s has ih
      have hfun : (fun β : Fin m → ℝ => ∑ i ∈ insert a s,
            (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β)))
          = (fun β : Fin m → ℝ => Real.log (1 + Real.exp ((L a) β)) - y a * ((L a) β))
            + (fun β : Fin m → ℝ => ∑ i ∈ s,
              (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) := by
        funext β
        simp only [Finset.sum_insert has, Pi.add_apply]
      rw [hfun]
      exact (hsummand a).add ih
  have h := hsum Finset.univ
  have hfun : logisticNLL X y = (fun β : Fin m → ℝ => ∑ i ∈ Finset.univ,
      (Real.log (1 + Real.exp ((L i) β)) - y i * ((L i) β))) := by
    funext β
    simp only [logisticNLL]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hL i β]
  rw [hfun]
  exact h

/-- The summed logistic NLL is the negative canonical logistic GLM
log-likelihood at zero offset. This is the summed convention: no division
by the number of observations. -/
theorem logisticNLL_eq_neg_logisticLogLik {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (β : Fin m → ℝ) :
    logisticNLL X y β =
      -MathlibExt.Probability.Statistics.GLM.logisticLogLik X 0 y β := by
  rw [MathlibExt.Probability.Statistics.GLM.logisticLogLik_eq_sum,
    ← Finset.sum_neg_distrib]
  unfold logisticNLL
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [MathlibExt.Probability.Statistics.GLM.glmPredictor_apply, Matrix.mulVec,
    dotProduct]

/-- The Euclidean gradient of the summed logistic NLL is
`Xᵀ (σ(Xβ) - y)`, obtained by negating the canonical GLM score. -/
theorem hasGradientAt_logisticNLL {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (β : Fin m → ℝ) :
    HasGradientAt (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp)
      (WithLp.toLp 2
        (X.transpose.mulVec
          ((Real.sigmoid ∘
              MathlibExt.Probability.Statistics.GLM.glmPredictor X 0 β) - y)))
      (WithLp.toLp 2 β) := by
  have hlog :=
    MathlibExt.Probability.Statistics.GLM.hasFDerivAt_logisticLogLik X 0 y β
  have hfun : logisticNLL X y =
      (-MathlibExt.Probability.Statistics.GLM.logisticLogLik X 0 y) := by
    funext b
    exact logisticNLL_eq_neg_logisticLogLik X y b
  have hscore :
      -(X.transpose.mulVec
          (y - Real.sigmoid ∘
            MathlibExt.Probability.Statistics.GLM.glmPredictor X 0 β)) =
        X.transpose.mulVec
          ((Real.sigmoid ∘
              MathlibExt.Probability.Statistics.GLM.glmPredictor X 0 β) - y) := by
    rw [← Matrix.mulVec_neg, neg_sub]
  have hderiv : HasFDerivAt (logisticNLL X y)
      (Real.dotL
        (X.transpose.mulVec
          ((Real.sigmoid ∘
              MathlibExt.Probability.Statistics.GLM.glmPredictor X 0 β) - y))) β := by
    rw [hfun]
    convert hlog.neg using 1
    ext v
    rw [← hscore]
    simp [Real.dotL_apply]
  exact Real.hasGradientAt_ofLp hderiv

/-- Pointwise Euclidean gradient formula for the summed logistic NLL. -/
theorem gradient_logisticNLL {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    (β : EuclideanSpace ℝ (Fin m)) :
    gradient (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp) β =
      WithLp.toLp 2
        (X.transpose.mulVec
          ((Real.sigmoid ∘
              MathlibExt.Probability.Statistics.GLM.glmPredictor X 0 β.ofLp) - y)) := by
  have h := (hasGradientAt_logisticNLL X y β.ofLp).gradient
  simpa using h

private theorem differentiable_logisticNLL_euclidean {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) :
    Differentiable ℝ
      (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp) := by
  intro b
  exact ((hasGradientAt_logisticNLL X y b.ofLp).hasFDerivAt).differentiableAt

private theorem convexOn_logisticNLL_euclidean {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) :
    ConvexOn ℝ Set.univ
      (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have h := (convexOn_logisticNLL X y).2 (Set.mem_univ u.ofLp)
    (Set.mem_univ v.ofLp) ha hb hab
  have hof : (a • u + b • v).ofLp = a • u.ofLp + b • v.ofLp := by
    ext i
    simp [PiLp.add_apply, PiLp.smul_apply, Pi.add_apply, Pi.smul_apply]
  simpa [hof] using h

private theorem sigmoid_mul_one_sub_le (t : ℝ) :
    Real.sigmoid t * (1 - Real.sigmoid t) ≤ 1 / 4 := by
  have h0 := Real.sigmoid_pos t
  have h1 := Real.sigmoid_lt_one t
  nlinarith [sq_nonneg (Real.sigmoid t - 1 / 2), h0, h1]

private theorem norm_sigmoid_sub_le (a b : ℝ) :
    ‖Real.sigmoid a - Real.sigmoid b‖ ≤ (1 / 4 : ℝ) * ‖a - b‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
    (s := Set.univ) (f := Real.sigmoid) (C := (1 / 4 : ℝ))
    (fun x _ => (Real.hasDerivAt_sigmoid x).differentiableAt)
    (fun x _ => by
      rw [Real.deriv_sigmoid]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (Real.sigmoid_pos x).le
          (sub_nonneg.mpr (Real.sigmoid_lt_one x).le))]
      exact sigmoid_mul_one_sub_le x)
    convex_univ (Set.mem_univ b) (Set.mem_univ a)
  simpa [norm_sub_rev] using h

private theorem norm_toEuclideanLin_transpose {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) :
    ‖(Matrix.toEuclideanLin X.transpose).toContinuousLinearMap‖ =
      ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ := by
  have h := Matrix.l2_opNorm_conjTranspose (𝕜 := ℝ) X
  rwa [Matrix.l2_opNorm_def, Matrix.l2_opNorm_def,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The summed logistic NLL has an `‖X‖op² / 4`-Lipschitz Euclidean
gradient, where `‖X‖op` is the Euclidean operator norm of the design map. -/
theorem lipschitzWith_gradient_logisticNLL {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) :
    LipschitzWith
      (⟨‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ ^ 2 / 4,
        by positivity⟩ : NNReal)
      (gradient (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp)) := by
  apply LipschitzWith.of_dist_le_mul
  intro β γ
  have hgrad :
      gradient (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp) β -
          gradient (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp) γ =
        (Matrix.toEuclideanLin X.transpose).toContinuousLinearMap
          (WithLp.toLp 2
            (fun i => Real.sigmoid ((X.mulVec β.ofLp) i) -
              Real.sigmoid ((X.mulVec γ.ofLp) i))) := by
    rw [gradient_logisticNLL, gradient_logisticNLL, ← WithLp.toLp_sub]
    congr 1
    rw [← Matrix.mulVec_sub]
    congr 1
    ext i
    simp [MathlibExt.Probability.Statistics.GLM.glmPredictor_apply,
      Function.comp_apply]
  have hσ :
      ‖WithLp.toLp 2
          (fun i => Real.sigmoid ((X.mulVec β.ofLp) i) -
            Real.sigmoid ((X.mulVec γ.ofLp) i))‖ ≤
        (1 / 4 : ℝ) *
          ‖(Matrix.toEuclideanLin X).toContinuousLinearMap (β - γ)‖ := by
    have hσsq :
        ‖WithLp.toLp 2
            (fun i => Real.sigmoid ((X.mulVec β.ofLp) i) -
              Real.sigmoid ((X.mulVec γ.ofLp) i))‖ ^ 2 ≤
          ((1 / 4 : ℝ) *
            ‖(Matrix.toEuclideanLin X).toContinuousLinearMap (β - γ)‖) ^ 2 := by
      calc
        ‖WithLp.toLp 2
            (fun i => Real.sigmoid ((X.mulVec β.ofLp) i) -
              Real.sigmoid ((X.mulVec γ.ofLp) i))‖ ^ 2 =
            ∑ i, ‖Real.sigmoid ((X.mulVec β.ofLp) i) -
              Real.sigmoid ((X.mulVec γ.ofLp) i)‖ ^ 2 := by
          rw [EuclideanSpace.norm_sq_eq]
        _ ≤ ∑ i, (1 / 16 : ℝ) *
            ‖(X.mulVec β.ofLp) i - (X.mulVec γ.ofLp) i‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc
            ‖Real.sigmoid ((X.mulVec β.ofLp) i) -
                Real.sigmoid ((X.mulVec γ.ofLp) i)‖ ^ 2 ≤
                ((1 / 4 : ℝ) *
                  ‖(X.mulVec β.ofLp) i - (X.mulVec γ.ofLp) i‖) ^ 2 :=
              (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
                (norm_sigmoid_sub_le _ _)
            _ = (1 / 16 : ℝ) *
                ‖(X.mulVec β.ofLp) i - (X.mulVec γ.ofLp) i‖ ^ 2 := by ring
        _ = (1 / 16 : ℝ) * ∑ i,
            ‖(X.mulVec β.ofLp) i - (X.mulVec γ.ofLp) i‖ ^ 2 := by
          rw [Finset.mul_sum]
        _ = ((1 / 4 : ℝ) *
            ‖(Matrix.toEuclideanLin X).toContinuousLinearMap (β - γ)‖) ^ 2 := by
          rw [mul_pow]
          congr 1
          · norm_num
          · rw [EuclideanSpace.norm_sq_eq]
            refine Finset.sum_congr rfl fun i _ => ?_
            have hi :
                (((Matrix.toEuclideanLin X).toContinuousLinearMap (β - γ)).ofLp) i =
                  (X.mulVec β.ofLp) i - (X.mulVec γ.ofLp) i := by
              change (X.mulVec (β - γ).ofLp) i = _
              rw [WithLp.ofLp_sub, Matrix.mulVec_sub]
              rfl
            rw [hi]
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hσsq
  rw [dist_eq_norm, dist_eq_norm, hgrad]
  calc
    ‖(Matrix.toEuclideanLin X.transpose).toContinuousLinearMap
        (WithLp.toLp 2
          (fun i => Real.sigmoid ((X.mulVec β.ofLp) i) -
            Real.sigmoid ((X.mulVec γ.ofLp) i)))‖ ≤
        ‖(Matrix.toEuclideanLin X.transpose).toContinuousLinearMap‖ *
          ‖WithLp.toLp 2
            (fun i => Real.sigmoid ((X.mulVec β.ofLp) i) -
              Real.sigmoid ((X.mulVec γ.ofLp) i))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ *
          ‖WithLp.toLp 2
            (fun i => Real.sigmoid ((X.mulVec β.ofLp) i) -
              Real.sigmoid ((X.mulVec γ.ofLp) i))‖ := by
      rw [norm_toEuclideanLin_transpose]
    _ ≤ ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ *
          ((1 / 4 : ℝ) *
            ‖(Matrix.toEuclideanLin X).toContinuousLinearMap (β - γ)‖) :=
      mul_le_mul_of_nonneg_left hσ (norm_nonneg _)
    _ ≤ ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ *
          ((1 / 4 : ℝ) *
            (‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ * ‖β - γ‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm _ _) (by norm_num)) (norm_nonneg _)
    _ = ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ ^ 2 / 4 *
          ‖β - γ‖ := by ring

/-- Gradient-descent rate for summed logistic NLL at an attained minimizer.
The step-size range is stated for the positive smoothness constant
`‖X‖op² / 4`; the zero-design case is separate. -/
theorem gd_logisticNLL_rate {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    {βstar : EuclideanSpace ℝ (Fin m)}
    (hmin : ∀ b : EuclideanSpace ℝ (Fin m),
      logisticNLL X y βstar.ofLp ≤ logisticNLL X y b.ofLp)
    {η : ℝ}
    (hL : 0 < ‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ ^ 2 / 4)
    (hη : η ∈ Set.Ioc 0
      (1 / (‖(Matrix.toEuclideanLin X).toContinuousLinearMap‖ ^ 2 / 4)))
    {βseq : ℕ → EuclideanSpace ℝ (Fin m)}
    (hβseq : ∀ k, βseq (k + 1) = βseq k -
      η • gradient (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp)
        (βseq k)) :
    ∀ k : ℕ, 0 < k →
      logisticNLL X y (βseq k).ofLp - logisticNLL X y βstar.ofLp ≤
        ‖βseq 0 - βstar‖ ^ 2 / (2 * η * (k : ℝ)) := by
  intro k hk
  exact MetaMathlibExt.gradient_descent_convex_sublinear_rate hL
    (convexOn_logisticNLL_euclidean X y)
    (differentiable_logisticNLL_euclidean X y)
    (lipschitzWith_gradient_logisticNLL X y) hmin hη hβseq k hk

/-- With zero design, summed logistic NLL does not depend on coefficients. -/
theorem logisticNLL_eq_of_X_eq_zero {n m : ℕ}
    {X : Matrix (Fin n) (Fin m) ℝ} (hX : X = 0) (y : Fin n → ℝ)
    (β γ : Fin m → ℝ) :
    logisticNLL X y β = logisticNLL X y γ := by
  simp [logisticNLL, hX]

/-- With zero design, the Euclidean gradient of summed logistic NLL is zero. -/
theorem gradient_logisticNLL_of_X_eq_zero {n m : ℕ}
    {X : Matrix (Fin n) (Fin m) ℝ} (hX : X = 0) (y : Fin n → ℝ)
    (β : EuclideanSpace ℝ (Fin m)) :
    gradient (fun b : EuclideanSpace ℝ (Fin m) => logisticNLL X y b.ofLp) β = 0 := by
  rw [gradient_logisticNLL]
  simp [hX]

/-- With zero design, every Euclidean objective gap for summed logistic NLL
is zero. This is the `L = 0` counterpart of `gd_logisticNLL_rate`. -/
theorem logisticNLL_gap_eq_zero_of_X_eq_zero {n m : ℕ}
    {X : Matrix (Fin n) (Fin m) ℝ} (hX : X = 0) (y : Fin n → ℝ)
    (β βstar : EuclideanSpace ℝ (Fin m)) :
    logisticNLL X y β.ofLp - logisticNLL X y βstar.ofLp = 0 := by
  rw [logisticNLL_eq_of_X_eq_zero hX y β.ofLp βstar.ofLp]
  exact sub_self _

private theorem log_one_add_exp_sub (t : ℝ) :
    Real.log (1 + Real.exp t) - t = Real.log (1 + Real.exp (-t)) := by
  have hpos : 0 < 1 + Real.exp (-t) := by positivity
  have e : 1 + Real.exp t = Real.exp t * (1 + Real.exp (-t)) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    simp [add_comm]
  rw [e, Real.log_mul (Real.exp_pos t).ne' hpos.ne', Real.log_exp]
  ring

/-- Strictly separable binary data have no finite unregularized logistic
NLL minimizer. The separator hypothesis is
`(2yᵢ - 1)(xᵢ ⬝ βsep) > 0` for every observation. -/
theorem not_exists_isMinOn_of_separable {n m : ℕ} [Nonempty (Fin n)]
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ)
    (hy : ∀ i, y i = 0 ∨ y i = 1)
    {βsep : Fin m → ℝ}
    (hsep : ∀ i, 0 < (2 * y i - 1) * ((X.mulVec βsep) i)) :
    ¬ ∃ β, IsMinOn (logisticNLL X y) Set.univ β := by
  rintro ⟨β, hmin⟩
  have hlt : logisticNLL X y (β + βsep) < logisticNLL X y β := by
    unfold logisticNLL
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => ?_
    have hpi : (∑ j, X i j * (β + βsep) j) =
        (X.mulVec β) i + (X.mulVec βsep) i := by
      simp [Matrix.mulVec, dotProduct, Finset.sum_add_distrib, mul_add]
    have hpβ : (∑ j, X i j * β j) = (X.mulVec β) i := by
      simp [Matrix.mulVec, dotProduct]
    rw [hpi, hpβ]
    rcases hy i with h0 | h1
    · have hd : (X.mulVec βsep) i < 0 := by
        have h := hsep i
        rw [h0] at h
        nlinarith
      have hexp : Real.exp ((X.mulVec β) i + (X.mulVec βsep) i) <
          Real.exp ((X.mulVec β) i) :=
        Real.exp_lt_exp.mpr (by linarith)
      have hlog : Real.log (1 + Real.exp ((X.mulVec β) i + (X.mulVec βsep) i)) <
          Real.log (1 + Real.exp ((X.mulVec β) i)) :=
        Real.log_lt_log (by positivity) (by linarith [hexp])
      rw [h0]
      simpa using hlog
    · have hd : 0 < (X.mulVec βsep) i := by
        have h := hsep i
        rw [h1] at h
        nlinarith
      have hexp : Real.exp (-((X.mulVec β) i + (X.mulVec βsep) i)) <
          Real.exp (-(X.mulVec β) i) :=
        Real.exp_lt_exp.mpr (by linarith)
      have hlog : Real.log (1 + Real.exp (-((X.mulVec β) i + (X.mulVec βsep) i))) <
          Real.log (1 + Real.exp (-(X.mulVec β) i)) :=
        Real.log_lt_log (by positivity) (by linarith [hexp])
      rw [h1]
      simpa [log_one_add_exp_sub] using hlog
  exact (not_lt_of_ge (hmin (Set.mem_univ (β + βsep)))) hlt

/-- For `0/1` labels, the logistic negative log-likelihood is the sum of the margin losses
`log (1 + exp (-(2yᵢ - 1)(xᵢ ⬝ β)))`. The sign `2yᵢ - 1` converts to `±1` labels. -/
theorem logisticNLL_eq_sum_margin_loss {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ)
    (y : Fin n → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1) (β : Fin m → ℝ) :
    logisticNLL X y β =
      ∑ i, Real.log (1 + Real.exp (-((2 * y i - 1) * (X.mulVec β) i))) := by
  unfold logisticNLL
  refine Finset.sum_congr rfl fun i _ => ?_
  change Real.log (1 + Real.exp ((X.mulVec β) i)) - y i * (X.mulVec β) i = _
  rcases hy i with h | h
  · simp [h, neg_mul]
  · simpa [h, show (2 : ℝ) - 1 = 1 by norm_num] using log_one_add_exp_sub ((X.mulVec β) i)

section SeparableInfimum

open Filter Set Topology

/-- Along a strictly separating ray, the binary logistic negative log-likelihood tends to zero.
The scalar multiplying the separator tends to `+∞`; no assumption on an optimization algorithm
is needed. -/
theorem tendsto_logisticNLL_smul_of_separable {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    {βsep : Fin m → ℝ} (hsep : ∀ i, 0 < (2 * y i - 1) * (X.mulVec βsep) i) :
    Tendsto (fun c : ℝ => logisticNLL X y (c • βsep)) atTop (𝓝 0) := by
  have hterm (a : ℝ) (ha : 0 < a) :
      Tendsto (fun c : ℝ => Real.log (1 + Real.exp (-(c * a)))) atTop (𝓝 0) := by
    have hneg : Tendsto (fun c : ℝ => -(c * a)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const ha)
    have he : Tendsto (fun c : ℝ => Real.exp (-(c * a))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hneg
    have hadd : Tendsto (fun c : ℝ => 1 + Real.exp (-(c * a))) atTop (𝓝 1) := by
      simpa only [add_zero] using he.const_add 1
    rw [← Real.log_one]
    exact (Real.continuousAt_log (x := (1 : ℝ)) one_ne_zero).tendsto.comp hadd
  have heq (i : Fin n) (c : ℝ) :
      (2 * y i - 1) * (c * (X.mulVec βsep) i) = c * ((2 * y i - 1) * (X.mulVec βsep) i) :=
    mul_left_comm _ _ _
  simp_rw [logisticNLL_eq_sum_margin_loss X y hy, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul, heq]
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum Finset.univ (fun i _ => hterm _ (hsep i))

/-- On strictly separable binary data, zero is the greatest lower bound of the logistic loss.
This also holds for empty data, where the sum is identically zero. -/
theorem isGLB_logisticNLL_of_separable {n m : ℕ}
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    {βsep : Fin m → ℝ} (hsep : ∀ i, 0 < (2 * y i - 1) * (X.mulVec βsep) i) :
    IsGLB (Set.range (logisticNLL X y)) 0 := by
  constructor
  · rintro _ ⟨β, rfl⟩
    rw [logisticNLL_eq_sum_margin_loss X y hy]
    exact Finset.sum_nonneg fun i _ => Real.log_nonneg (le_add_of_nonneg_right (Real.exp_nonneg _))
  · intro b hb
    exact ge_of_tendsto (tendsto_logisticNLL_smul_of_separable X y hy hsep)
      (Filter.Eventually.of_forall fun c => hb (Set.mem_range_self (c • βsep)))

/-- **Logistic loss has no minimizer on separable data.** On a nonempty strictly separable
binary sample, the unregularized logistic loss has infimum zero and does not attain it.
The label sign in the separation condition is `2yᵢ - 1` for the `0/1` labels `yᵢ`.

Background: Soudry et al., *The implicit bias of gradient descent on separable data*,
JMLR 19 (2018), §2. The statement here concerns the loss, not the iterates. -/
lemma logisticNLL_infimum_zero_not_attained_of_separable {n m : ℕ} [Nonempty (Fin n)]
    (X : Matrix (Fin n) (Fin m) ℝ) (y : Fin n → ℝ) (hy : ∀ i, y i = 0 ∨ y i = 1)
    {βsep : Fin m → ℝ} (hsep : ∀ i, 0 < (2 * y i - 1) * (X.mulVec βsep) i) :
    sInf (Set.range (logisticNLL X y)) = 0 ∧ ¬ ∃ β, IsMinOn (logisticNLL X y) Set.univ β :=
  ⟨(isGLB_logisticNLL_of_separable X y hy hsep).csInf_eq (Set.range_nonempty _),
    not_exists_isMinOn_of_separable X y hy hsep⟩

end SeparableInfimum

end MathlibExt.Probability.Statistics.LogisticRegression
