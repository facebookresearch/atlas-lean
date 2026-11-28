/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Matrix.InverseLogDetDerivative
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic.NoncommRing

/-!
# Derivatives of the Gaussian restricted log likelihood

For a full-column-rank design and covariance positive definite at the evaluation point, the
restricted log likelihood is the sum of two log-determinant terms and a residual quadratic term,
with a common factor of `−1/2`, up to a parameter-independent constant (Zhu and Wathen,
arXiv:1805.05188, Theorem 2, equations (25)–(27)). We differentiate this full-design expression
directly. Its directional derivative along a raw covariance component gives the score.

The matrix-curve formulas themselves only require differentiability and invertibility of the
covariance and weighted design Gram matrix at the point. They retain both quadratic terms in
the score derivative, so do not require commutation or symmetry.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.LinearModel.AverageInformation

open Matrix
open scoped Matrix.Norms.Operator

variable {n p : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]

/-- The matrix `P = W − W X (Xᵀ W X)⁻¹ Xᵀ W`, with `W = V⁻¹`, is defined using total matrix
inversion. When `V` is positive definite and `X` has full column rank it is the residual
precision: `P X = 0` and `P V P = P`. It can be singular even under these hypotheses. -/
noncomputable def precision (X : Matrix n p ℝ) (V : Matrix n n ℝ) : Matrix n n ℝ :=
  V⁻¹ - V⁻¹ * (X * (Xᵀ * V⁻¹ * X)⁻¹ * Xᵀ) * V⁻¹

/-- Gaussian restricted log likelihood with the parameter-independent additive constant omitted.
Its two log determinants account for covariance and estimation of the fixed effects respectively.
It is a likelihood criterion only for positive definite covariance and full column rank design. -/
noncomputable def logLikelihood (X : Matrix n p ℝ) (V : Matrix n n ℝ) (y : n → ℝ) : ℝ :=
  -(Real.log V.det + Real.log (Xᵀ * V⁻¹ * X).det + y ⬝ᵥ precision X V *ᵥ y) / 2

omit [DecidableEq n] [DecidableEq p] [Fintype p] in
private theorem sandwichDeriv [Finite p] {f : ℝ → Matrix n n ℝ} {H : Matrix n n ℝ} {t : ℝ}
    (hf : HasDerivAt f H t) (L : Matrix p n ℝ) (R : Matrix n p ℝ) :
    HasDerivAt (fun s => L * f s * R) (L * H * R) t := by
  classical
  let := Fintype.ofFinite p
  let g : Matrix n n ℝ →ₗ[ℝ] Matrix p p ℝ :=
    { toFun := fun Z => L * Z * R
      map_add' := by intros; simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp }
  exact g.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

omit [DecidableEq n] in
private theorem quadDeriv {f : ℝ → Matrix n n ℝ} {H : Matrix n n ℝ} {t : ℝ}
    (hf : HasDerivAt f H t) (y : n → ℝ) :
    HasDerivAt (fun s => y ⬝ᵥ f s *ᵥ y) (y ⬝ᵥ H *ᵥ y) t := by
  let g : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun Z => y ⬝ᵥ Z *ᵥ y
      map_add' := by intros; simp [add_mulVec, dotProduct_add]
      map_smul' := by intros; simp [smul_mulVec, dotProduct_smul] }
  exact g.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

omit [DecidableEq n] in
private theorem trDeriv {f : ℝ → Matrix n n ℝ} {H : Matrix n n ℝ} {t : ℝ}
    (hf : HasDerivAt f H t) : HasDerivAt (fun s => (f s).trace) H.trace t :=
  (Matrix.traceLinearMap n ℝ ℝ).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hf

variable (X : Matrix n p ℝ) {V : ℝ → Matrix n n ℝ} {H : Matrix n n ℝ} {t : ℝ}

/-- Along a differentiable covariance curve with velocity `H`, residual precision has derivative
`-P H P` at every point where the covariance and the weighted design Gram matrix are invertible
(Zhu and Wathen, equation (37)). The order of factors matters. -/
theorem hasDerivAt_precision (h : HasDerivAt V H t) (hv : IsUnit (V t))
    (hx : IsUnit (Xᵀ * (V t)⁻¹ * X)) :
    HasDerivAt (fun s => precision X (V s)) (-(precision X (V t)) * H * precision X (V t)) t := by
  let W := (V t)⁻¹
  let G := (Xᵀ * W * X)⁻¹
  let T := X * G * Xᵀ
  have hw := Matrix.hasDerivAt_nonsingInv_curve h hv
  have hg := Matrix.hasDerivAt_nonsingInv_curve (sandwichDeriv hw Xᵀ X) hx
  have ht := sandwichDeriv hg X Xᵀ
  convert! hw.sub ((hw.mul ht).mul hw) using 1
  change -(W - W * T * W) * H * (W - W * T * W) = _
  have he : X * (-G * (Xᵀ * (-W * H * W) * X) * G) * Xᵀ = T * W * H * W * T := by
    simp [T, Matrix.mul_assoc]
  change _ = -W * H * W - ((-W * H * W * T + W * _) * W + W * T * (-W * H * W))
  rw [he]; noncomm_ring

/-- If `V` is differentiable at `t` with velocity `H` and both `V t` and `Xᵀ (V t)⁻¹ X`
are invertible, the derivative of the restricted log-likelihood expression is
`(yᵀ P H P y − tr(P H))/2`, where `P` is the residual precision at `t` (Zhu and Wathen,
equation (34)). This calculus identity needs no symmetry of `H`. -/
theorem hasDerivAt_logLikelihood (h : HasDerivAt V H t) (hv : IsUnit (V t))
    (hx : IsUnit (Xᵀ * (V t)⁻¹ * X)) (y : n → ℝ) :
    HasDerivAt (fun s => logLikelihood X (V s) y)
      ((y ⬝ᵥ (precision X (V t) * H * precision X (V t)) *ᵥ y -
        (precision X (V t) * H).trace) / 2) t := by
  let W := (V t)⁻¹
  let G := (Xᵀ * W * X)⁻¹
  have hw := Matrix.hasDerivAt_nonsingInv_curve h hv
  have h1 := Matrix.hasDerivAt_logDet_curve h hv
  have h2 := Matrix.hasDerivAt_logDet_curve (sandwichDeriv hw Xᵀ X) hx
  have h3 := quadDeriv (hasDerivAt_precision X h hv hx) y
  convert! (((h1.add h2).add h3).neg.div_const 2) using 1
  have cyc : (G * (Xᵀ * (W * H * W) * X)).trace = (W * (X * G * Xᵀ) * W * H).trace := by
    calc _ = ((G * Xᵀ * W * H) * (W * X)).trace := by simp only [Matrix.mul_assoc]
         _ = _ := by rw [trace_mul_comm]; simp only [Matrix.mul_assoc]
  simp only [neg_mul, Matrix.neg_mul, Matrix.mul_neg, trace_neg, neg_mulVec, dotProduct_neg]
  rw [show (precision X (V t) * H).trace = (W * H).trace - (W * (X * G * Xᵀ) * W * H).trace by
    simp only [precision, W, G, Matrix.sub_mul, trace_sub]]
  rw [cyc]; ring

/-- Along a differentiable matrix curve `V` with velocity `H`, hold `A` fixed and
differentiate the expression `(yᵀ P A P y − tr(P A))/2`. If `V t` and `Xᵀ (V t)⁻¹ X` are
invertible, the derivative is `(tr(P H P A) − yᵀ P H P A P y − yᵀ P A P H P y)/2`. This
calculus identity retains both quadratic orders and needs no symmetry. The differentiated
expression is a Gaussian restricted-likelihood score when `X` has full column rank, `V` is a
locally positive definite covariance curve and `A` is a covariance direction there (for example,
a symmetric raw component). Units alone do not give this interpretation. -/
theorem hasDerivAt_score (h : HasDerivAt V H t) (hv : IsUnit (V t))
    (hx : IsUnit (Xᵀ * (V t)⁻¹ * X)) (A : Matrix n n ℝ) (y : n → ℝ) :
    let P := precision X (V t)
    HasDerivAt (fun s => let Q := precision X (V s)
      (y ⬝ᵥ (Q * A * Q) *ᵥ y - (Q * A).trace) / 2)
      (((P * H * P * A).trace - y ⬝ᵥ (P * H * P * A * P) *ᵥ y -
        y ⬝ᵥ (P * A * P * H * P) *ᵥ y) / 2) t := by
  dsimp only
  have hp := hasDerivAt_precision X h hv hx
  have hq := quadDeriv ((hp.mul_const A).mul hp) y
  have hh := trDeriv (hp.mul_const A)
  convert (hq.sub hh).div_const 2 using 1
  simp [neg_mul, neg_mulVec, dotProduct_neg, add_mulVec, dotProduct_add, Matrix.mul_assoc]
  ring

end MathlibExt.Probability.Statistics.LinearModel.AverageInformation
