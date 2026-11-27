/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Statistics.RestrictedLikelihood.Derivatives
public import MathlibExt.Probability.Distributions.GaussianQuadratic

/-!
# Average information for the Gaussian restricted log likelihood

Let the design `X` have full column rank and let the covariance be linear in raw variance
parameters, with symmetric components `Aᵢ` and positive definite sum `V` at the evaluation point.
The observed information is the negative mixed Hessian of the restricted log likelihood. Its
expectation under `N(X b, V)` is the Fisher information. Symmetry identifies the two quadratic
orders in the mixed derivative without requiring the components to commute.

The arithmetic mean of these two information matrices is a positive semidefinite half Gram
matrix, computable without traces. It can be singular. At a nonsingular iterate the ordinary
inverse gives a scoring increment, with no convergence or feasibility guarantee. See Zhu and
Wathen, arXiv:1805.05188, §§4.1–4.4 and Algorithm 3.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.LinearModel.AverageInformation

open Matrix MeasureTheory ProbabilityTheory WithLp Filter Topology
open scoped Matrix.Norms.Operator

variable {n p r : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
  [Fintype r] [DecidableEq r]

/-- Covariance linear in the raw parameters. Individual components need not be invertible
or commute; positive definiteness is required of the sum at the parameter being studied. -/
noncomputable def covarianceAt (A : r → Matrix n n ℝ) (σ : r → ℝ) : Matrix n n ℝ :=
  ∑ i, σ i • A i

omit [Fintype n] [DecidableEq n] in
private theorem shift (A : r → Matrix n n ℝ) (σ : r → ℝ) (i : r) (s : ℝ) :
    covarianceAt A (σ + Pi.single i s) = covarianceAt A σ + s • A i := by
  classical
  simp [covarianceAt, add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]

/-- The coordinate derivative of the full-design expression `logLikelihood`, varying only
`σᵢ`. This uses Lean's total `deriv`. For full-column-rank `X` and positive definite `V` at
the point, it is a Gaussian REML score when the coordinate stays in the covariance model
locally, as it does for symmetric `Aᵢ`. Off such a path it has no such interpretation. -/
noncomputable def score (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (y : n → ℝ) (i : r) : ℝ :=
  deriv (fun s => logLikelihood X (covarianceAt A (σ + Pi.single i s)) y) 0

/-- Minus the coordinate derivative in `σⱼ` of the total expression `score … i`. For a
full-column-rank design and a raw linear covariance family with symmetric components and
positive definite sum at the point, this is the observed information: the negative mixed
partial derivative of the Gaussian restricted log likelihood. The definition uses `deriv`
without imposing these model conditions. -/
noncomputable def observed (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (y : n → ℝ) (i j : r) : ℝ :=
  -deriv (fun s => score X A (σ + Pi.single j s) y i) 0

omit [Fintype n] [DecidableEq n] in
private theorem lineDeriv [Finite n] (V H : Matrix n n ℝ) :
    HasDerivAt (fun s : ℝ => V + s • H) H 0 := by
  let := Fintype.ofFinite n
  simpa only [one_smul, id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add V

private theorem scoreOfUnits (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (hv : IsUnit (covarianceAt A σ)) (hx : IsUnit (Xᵀ * (covarianceAt A σ)⁻¹ * X))
    (y : n → ℝ) (i : r) : let P := precision X (covarianceAt A σ)
    score X A σ y i = (y ⬝ᵥ (P * A i * P) *ᵥ y - (P * A i).trace) / 2 := by
  simp only [score, shift]
  simpa using (hasDerivAt_logLikelihood X (lineDeriv (covarianceAt A σ) (A i))
    (by simpa) (by simpa) y).deriv

private theorem scoreAtValue (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    {V : Matrix n n ℝ} (h : covarianceAt A σ = V) (hv : IsUnit V) (hx : IsUnit (Xᵀ * V⁻¹ * X))
    (y : n → ℝ) (i : r) : let P := precision X V
    score X A σ y i = (y ⬝ᵥ (P * A i * P) *ᵥ y - (P * A i).trace) / 2 := by
  subst V; exact scoreOfUnits X A σ hv hx y i

omit [DecidableEq p] in
private theorem gramPD {X : Matrix n p ℝ} {V : Matrix n n ℝ} (hv : V.PosDef)
    (hx : Function.Injective X.mulVec) : (Xᵀ * V⁻¹ * X).PosDef := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hv.inv.conjTranspose_mul_mul_same hx

private theorem properties {X : Matrix n p ℝ} {V : Matrix n n ℝ} (hv : V.PosDef)
    (hx : Function.Injective X.mulVec) : let P := precision X V
    Pᵀ = P ∧ P * X = 0 ∧ P * V * P = P ∧ P.PosSemidef := by
  let P := precision X V
  let W := V⁻¹
  let G := (Xᵀ * W * X)⁻¹
  have hg := gramPD hv hx
  have wT : Wᵀ = W := by
    simpa [W, conjTranspose_eq_transpose_of_trivial] using hv.inv.isHermitian.eq
  have gT : Gᵀ = G := by
    simpa [G, W, conjTranspose_eq_transpose_of_trivial] using hg.inv.isHermitian.eq
  have pT : Pᵀ = P := by
    change (W - W * (X * G * Xᵀ) * W)ᵀ = W - W * (X * G * Xᵀ) * W
    simp only [transpose_sub, transpose_mul, transpose_transpose, wT, gT,
      Matrix.mul_assoc]
  have px : P * X = 0 := by
    change (W - W * (X * G * Xᵀ) * W) * X = _
    rw [Matrix.sub_mul, show W * (X * G * Xᵀ) * W * X = W * X * (G * (Xᵀ * W * X)) by
      simp only [Matrix.mul_assoc], nonsing_inv_mul _ ((isUnit_iff_isUnit_det _).mp hg.isUnit)]
    simp
  have pv : P * V * W = P := by
    rw [Matrix.mul_assoc, mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).mp hv.isUnit),
      Matrix.mul_one]
  have pvp : P * V * P = P := by
    change P * V * (W - W * (X * G * Xᵀ) * W) = P
    rw [Matrix.mul_sub, pv,
      show P * V * (W * (X * G * Xᵀ) * W) = (P * V * W) * X * G * Xᵀ * W by
        simp only [Matrix.mul_assoc], pv, px]; simp
  refine ⟨pT, px, pvp, ?_⟩
  simpa [conjTranspose_eq_transpose_of_trivial, pT, pvp] using
    hv.posSemidef.conjTranspose_mul_mul_same P

/-- With full-column-rank `X` and positive definite `V = ∑ σᵢ Aᵢ` at the point, the raw
coordinate derivative of the full-design expression is `½(yᵀ P Aᵢ P y − tr(P Aᵢ))`. The
calculus identity needs no symmetry of `Aᵢ`. To interpret it as a Gaussian REML score, the
coordinate must stay in the covariance model locally; a symmetric `Aᵢ` gives such a path here. -/
theorem score_eq (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (hv : (covarianceAt A σ).PosDef) (hx : Function.Injective X.mulVec) (y : n → ℝ) (i : r) :
    let P := precision X (covarianceAt A σ)
    score X A σ y i = (y ⬝ᵥ (P * A i * P) *ᵥ y - (P * A i).trace) / 2 :=
  scoreOfUnits X A σ hv.isUnit (gramPD hv hx).isUnit y i

omit [DecidableEq n] in
private theorem quadT (L : Matrix n n ℝ) (y : n → ℝ) : y ⬝ᵥ Lᵀ *ᵥ y = y ⬝ᵥ L *ᵥ y := by
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

private theorem eventuallyUnit {F : ℝ → Matrix n n ℝ} {t : ℝ} (hf : ContinuousAt F t)
    (hu : IsUnit (F t)) : ∀ᶠ s in 𝓝 t, IsUnit (F s) := by
  have hc := (continuous_id : Continuous (fun M : Matrix n n ℝ => M)).matrix_det
  filter_upwards [(hc.continuousAt.comp hf).eventually_ne
    ((isUnit_iff_isUnit_det _).mp hu).ne_zero] with s h
  exact (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)

/-- For full-column-rank `X`, symmetric components `Aᵢ` and positive definite `V = ∑ σᵢ Aᵢ`
at the point, the negative mixed Hessian entry of the restricted log likelihood is
`yᵀ P Aᵢ P Aⱼ P y − tr(P Aᵢ P Aⱼ)/2`. Symmetry identifies the two scalar quadratic terms
without interchanging matrix factors (Zhu and Wathen, equation (41)). -/
theorem observed_eq (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (hv : (covarianceAt A σ).PosDef) (hx : Function.Injective X.mulVec)
    (hs : ∀ i, (A i)ᵀ = A i) (y : n → ℝ) (i j : r) :
    let P := precision X (covarianceAt A σ)
    observed X A σ y i j = y ⬝ᵥ (P * A i * P * A j * P) *ᵥ y - (P * A i * P * A j).trace / 2 := by
  let V := covarianceAt A σ
  let P := precision X V
  let f := fun t : ℝ => V + t • A j
  have hf : HasDerivAt f (A j) 0 := lineDeriv V (A j)
  have h0 : f 0 = V := by simp [f]
  have hu : IsUnit (f 0) := by rw [h0]; exact hv.isUnit
  have hg : IsUnit (Xᵀ * (f 0)⁻¹ * X) := by rw [h0]; exact (gramPD hv hx).isUnit
  have hW := Matrix.hasDerivAt_nonsingInv_curve hf hu
  have hvN := eventuallyUnit (show ContinuousAt f 0 from hf.continuousAt) hu
  have hc : Continuous (fun M : Matrix n n ℝ => Xᵀ * M * X) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hgN : ∀ᶠ s in 𝓝 0, IsUnit (Xᵀ * (f s)⁻¹ * X) := eventuallyUnit (hc.continuousAt.comp
    (show ContinuousAt (fun s => (f s)⁻¹) 0 from hW.continuousAt)) hg
  have hd := hasDerivAt_score X hf hu hg (A i) y
  have he : (fun s => score X A (σ + Pi.single j s) y i) =ᶠ[𝓝 0]
      (fun s => let Q := precision X (f s); (y ⬝ᵥ (Q * A i * Q) *ᵥ y - (Q * A i).trace) / 2) := by
    filter_upwards [hvN, hgN] with s h1 h2
    have hcv : covarianceAt A (σ + Pi.single j s) = f s := shift A σ j s
    have val := scoreAtValue X A (σ + Pi.single j s) (V := f s) hcv h1 h2 y i
    dsimp only at val ⊢
    exact val
  have pp := (properties hv hx).1
  have q : y ⬝ᵥ (P * A j * P * A i * P) *ᵥ y = y ⬝ᵥ (P * A i * P * A j * P) *ᵥ y := by
    rw [← quadT (P * A j * P * A i * P)]
    simp only [transpose_mul, show Pᵀ = P from pp, hs, Matrix.mul_assoc]
  have tr : (P * A j * P * A i).trace = (P * A i * P * A j).trace := by
    rw [Matrix.mul_assoc (P * A j), trace_mul_comm]; simp only [Matrix.mul_assoc]
  change -deriv _ 0 = y ⬝ᵥ (P * A i * P * A j * P) *ᵥ y - _
  rw [he.deriv_eq, hd.deriv, h0]
  change -(((P * A j * P * A i).trace - _ - _) / 2) = _
  rw [q, tr]; ring

/-- The integral of `observed` against `multivariateGaussian` with mean argument `X b` and
matrix argument `V = ∑ σᵢ Aᵢ`. For full-column-rank `X`, symmetric components and positive
definite `V` at the point, this is the Fisher information: the expectation under `N(X b, V)`
of the negative mixed Hessian of the restricted log likelihood. The integral and the Gaussian
constructor are total; their use alone does not make `V` a covariance or the result Fisher
information. -/
noncomputable def fisher (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (b : p → ℝ) (i j : r) : ℝ :=
  ∫ y, observed X A σ (ofLp y) i j ∂multivariateGaussian (toLp 2 (X *ᵥ b)) (covarianceAt A σ)

/-- For full-column-rank `X`, symmetric components and positive definite covariance
`V = ∑ σᵢ Aᵢ` at the point, the expectation under `N(X b, V)` of the negative mixed Hessian
of the restricted log likelihood is `tr(P Aᵢ P Aⱼ)/2`. The fixed-effect mean drops out because
`P X = 0` (Zhu and Wathen, equations (42) and (45)). -/
theorem fisher_eq (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (hv : (covarianceAt A σ).PosDef) (hx : Function.Injective X.mulVec)
    (hs : ∀ i, (A i)ᵀ = A i) (b : p → ℝ) (i j : r) : let P := precision X (covarianceAt A σ)
    fisher X A σ b i j = (P * A i * P * A j).trace / 2 := by
  let V := covarianceAt A σ
  let P := precision X V
  let T := P * A i * P * A j
  obtain ⟨_, px, pvp, _⟩ := properties hv hx
  change P * V * P = P at pvp
  have ht : ((T * P) * V).trace = T.trace := by
    calc _ = ((A i * P * A j) * (P * V) * P).trace := by
               rw [trace_mul_comm _ P]; simp only [T, Matrix.mul_assoc]
         _ = T.trace := by
           rw [Matrix.mul_assoc, pvp, trace_mul_comm]; simp only [T, Matrix.mul_assoc]
  have hm : (T * P) *ᵥ (X *ᵥ b) = 0 := by
    rw [mulVec_mulVec, Matrix.mul_assoc, px, Matrix.mul_zero, zero_mulVec]
  obtain ⟨hint, hq⟩ :=
    integral_quadratic_multivariateGaussian (toLp 2 (X *ᵥ b)) hv.posSemidef (T * P)
  simp only [fisher, observed_eq X A σ hv hx hs]
  rw [integral_sub hint (integrable_const _), hq, integral_const]
  change (T * P * V).trace + (X *ᵥ b) ⬝ᵥ (T * P) *ᵥ (X *ᵥ b) - _ =
    T.trace / 2
  rw [ht, hm, dotProduct_zero]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul, add_zero]
  change T.trace - T.trace / 2 = T.trace / 2; ring

/-- The arithmetic mean of the observed and Fisher information, before any simplification. -/
noncomputable def average (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (y : n → ℝ) (b : p → ℝ) : Matrix r r ℝ :=
  Matrix.of fun i j => (observed X A σ y i j + fisher X A σ b i j) / 2

/-- For full-column-rank `X`, symmetric raw covariance components and positive definite total
covariance at the point, the mean of the observed negative Hessian of the restricted log
likelihood and its Gaussian expectation has entries `½ uᵢᵀ P uⱼ`, where `uᵢ = Aᵢ P y`.
Storing `uᵢ` as the rows of `U` gives the positive semidefinite matrix `½ U P Uᵀ`, not
necessarily an invertible matrix (Zhu and Wathen, equation (46)). -/
theorem average_eq_gram (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (hv : (covarianceAt A σ).PosDef) (hx : Function.Injective X.mulVec)
    (hs : ∀ i, (A i)ᵀ = A i) (y : n → ℝ) (b : p → ℝ) :
    let P := precision X (covarianceAt A σ)
    let U : Matrix r n ℝ := Matrix.of fun i => A i *ᵥ (P *ᵥ y)
    average X A σ y b = (1 / 2 : ℝ) • (U * P * Uᵀ) ∧ (average X A σ y b).PosSemidef := by
  intro P U
  obtain ⟨pp, _, _, hp⟩ := properties hv hx
  have eqm : average X A σ y b = (1 / 2 : ℝ) • (U * P * Uᵀ) := by
    ext i j
    have he : (U * P * Uᵀ) i j = y ⬝ᵥ (P * A i * P * A j * P) *ᵥ y := by
      change ((U i) ᵥ* P) ⬝ᵥ (U j) = _
      rw [← dotProduct_mulVec]
      change (A i *ᵥ (P *ᵥ y)) ⬝ᵥ P *ᵥ (A j *ᵥ (P *ᵥ y)) = _
      have move (M : Matrix n n ℝ) (x z : n → ℝ) :
          (M *ᵥ x) ⬝ᵥ z = x ⬝ᵥ Mᵀ *ᵥ z := by rw [dotProduct_transpose_mulVec, dotProduct_comm]
      rw [move, move, hs, show Pᵀ = P from pp]
      simp only [mulVec_mulVec, Matrix.mul_assoc]
    change (observed X A σ y i j + fisher X A σ b i j) / 2 = 1 / 2 * _
    rw [observed_eq X A σ hv hx hs, fisher_eq X A σ hv hx hs, he]; ring
  refine ⟨eqm, eqm ▸ ?_⟩
  exact (by simpa [conjTranspose_eq_transpose_of_trivial] using hp.mul_mul_conjTranspose_same U :
    (U * P * Uᵀ).PosSemidef).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- When average information is nonsingular, adding its inverse times the score is the
unique step whose increment solves the scoring equations. No feasibility or convergence
claim is made for the updated raw parameters (Zhu and Wathen, Algorithm 3). -/
theorem scoring_step_iff (X : Matrix n p ℝ) (A : r → Matrix n n ℝ) (σ : r → ℝ)
    (y : n → ℝ) (b : p → ℝ) (hn : IsUnit (average X A σ y b).det) (next : r → ℝ) :
    average X A σ y b *ᵥ (next - σ) = score X A σ y ↔
      next = σ + (average X A σ y b)⁻¹ *ᵥ score X A σ y := by
  constructor
  · intro h
    have hh := congrArg ((average X A σ y b)⁻¹ *ᵥ ·) h
    rw [mulVec_mulVec, nonsing_inv_mul _ hn, one_mulVec] at hh
    rw [← hh]; abel
  · intro h; rw [h, add_sub_cancel_left, mulVec_mulVec, mul_nonsing_inv _ hn, one_mulVec]

end MathlibExt.Probability.Statistics.LinearModel.AverageInformation
