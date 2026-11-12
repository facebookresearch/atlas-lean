/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Newton–Raphson as iteratively reweighted least squares for canonical GLMs

Consider a generalized linear model with design matrix `X`, responses `y`, linear predictor
`η = X β`, mean function `mean = b'` and variance function `weight = b''` of a natural
exponential family with dispersion `1`. With the *canonical link* (natural parameter `θ = η`),
the log-likelihood `ℓ(β) = ∑ᵢ (yᵢ ηᵢ - b(ηᵢ))` has

* score `∇ℓ(β) = Xᵀ (y - μ(β))`, where `μᵢ(β) = mean (X β)ᵢ`, and
* Hessian `∇²ℓ(β) = -Xᵀ W(β) X`, where `W(β) = diag (weight (X β)ᵢ)`.

The Hessian does not depend on `y`: for canonical links the observed and Fisher information
coincide. This file does not define the GLM log-likelihood; the two displayed identities are
taken as explicit hypotheses (`IsCanonicalScoreHessian`). The one analytic input of the
canonical link, `mean' = weight`, is shown to produce the Hessian identity from the score
identity (`hasFDerivAt_canonicalScore`).

Under these hypotheses the Newton–Raphson update `β - (∇²ℓ)⁻¹ ∇ℓ` is a weighted least-squares
fit of the *working response* `zᵢ = ηᵢ + (yᵢ - μᵢ) / wᵢ` on `X` with weights `wᵢ`. Iterating
it is the IRLS algorithm of Nelder and Wedderburn, and its fixed points are exactly the score
roots.

## Main definitions

* `weightedGram X w`: the weighted Gram matrix `Xᵀ diag(w) X`.
* `wlsEstimate X w z`: the weighted least-squares estimate, i.e. the GLS estimate with
  covariance `diag(w)⁻¹` (reusing `GeneralizedLeastSquares.glsMatrix`).
* `newtonStep score hess β`: the Newton–Raphson update `β - (hess β)⁻¹ score β`.
* `irlsWeights`, `workingResponse`, `irlsStep`, `irlsIterate`: the IRLS weights, working
  response, one IRLS update, and the iteration.
* `IsCanonicalScoreHessian`: the canonical-link score and Hessian identities, as hypotheses.

## Main results

* `wlsEstimate_eq`: closed form `(Xᵀ W X)⁻¹ Xᵀ W z` of the weighted least-squares estimate.
* `normal_eq_iff_eq_wlsEstimate`: the WLS estimate is the unique solution of the weighted
  normal equations `Xᵀ W (z - X b) = 0`.
* `wrss_wlsEstimate_le`: with nonnegative weights the WLS estimate minimizes the weighted
  residual sum of squares.
* `newtonStep_eq_irlsStep`: the Newton step equals the IRLS (weighted least-squares) step.
* `newtonIterate_eq_irlsIterate`: Newton–Raphson and IRLS produce the same iterates.
* `irlsStep_eq_self_iff`: `β` is a fixed point of IRLS iff the score vanishes at `β`.
* `hasFDerivAt_canonicalScore`: if `mean` has derivative `weight`, the canonical score
  `β ↦ Xᵀ (y - μ(β))` has derivative `-Xᵀ W(β) X`.

## References

* J. A. Nelder and R. W. M. Wedderburn, *Generalized linear models*, J. Roy. Statist. Soc.
  Ser. A 135 (1972), 370–384.
* P. McCullagh and J. A. Nelder, *Generalized Linear Models*, 2nd ed., Chapman & Hall, 1989,
  §2.5.
-/

@[expose] public section

open Matrix
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares

namespace MathlibExt.Probability.Statistics.GLM.IRLS

variable {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

/-! ### Weighted least squares -/

/-- The weighted Gram matrix `Xᵀ diag(w) X`. -/
def weightedGram (X : Matrix m k ℝ) (w : m → ℝ) : Matrix k k ℝ :=
  Xᵀ * diagonal w * X

/-- The weighted least-squares estimate of `b` in `z ≈ X b` with weights `w`: the generalized
least-squares estimate with covariance `diag(w)⁻¹`. For nonzero weights it equals
`(Xᵀ W X)⁻¹ Xᵀ W z` (`wlsEstimate_eq`). -/
noncomputable def wlsEstimate (X : Matrix m k ℝ) (w z : m → ℝ) : k → ℝ :=
  glsMatrix X (diagonal w⁻¹) *ᵥ z

/-- The weighted residual sum of squares `∑ᵢ wᵢ (zᵢ - (X b)ᵢ)²`. -/
def wrss (X : Matrix m k ℝ) (w z : m → ℝ) (b : k → ℝ) : ℝ :=
  ∑ i, w i * (z i - (X *ᵥ b) i) ^ 2

variable {X : Matrix m k ℝ} {w : m → ℝ}

private theorem inv_diagonal_inv (hw : ∀ i, w i ≠ 0) : (diagonal w⁻¹)⁻¹ = diagonal w := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  simp [hw i]

private theorem diagonal_mulVec_eq (v : m → ℝ) : diagonal w *ᵥ v = w * v := by
  funext i
  simp [mulVec_diagonal]

omit [DecidableEq k] in
private theorem transpose_mulVec_mul_mulVec (b : k → ℝ) :
    Xᵀ *ᵥ (w * (X *ᵥ b)) = weightedGram X w *ᵥ b := by
  rw [weightedGram, ← diagonal_mulVec_eq, mulVec_mulVec, mulVec_mulVec]

/-- For nonzero weights the WLS estimate is `(Xᵀ W X)⁻¹ Xᵀ W z`. -/
theorem wlsEstimate_eq (hw : ∀ i, w i ≠ 0) (z : m → ℝ) :
    wlsEstimate X w z = (weightedGram X w)⁻¹ *ᵥ (Xᵀ *ᵥ (w * z)) := by
  rw [wlsEstimate, glsMatrix, inv_diagonal_inv hw, ← weightedGram, ← diagonal_mulVec_eq,
    mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

/-- With nonzero weights and an invertible weighted Gram matrix, `b` solves the weighted normal
equations `Xᵀ W (z - X b) = 0` iff `b` is the WLS estimate. -/
theorem normal_eq_iff_eq_wlsEstimate (hw : ∀ i, w i ≠ 0) (hG : IsUnit (weightedGram X w))
    (z : m → ℝ) (b : k → ℝ) :
    Xᵀ *ᵥ (w * (z - X *ᵥ b)) = 0 ↔ b = wlsEstimate X w z := by
  have hdet : IsUnit (weightedGram X w).det := (isUnit_iff_isUnit_det _).mp hG
  rw [mul_sub, mulVec_sub, transpose_mulVec_mul_mulVec, sub_eq_zero, wlsEstimate_eq hw]
  constructor
  · intro h
    rw [h, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]
  · intro h
    rw [h, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]

/-- The WLS estimate solves the weighted normal equations. -/
theorem normal_eq_wlsEstimate (hw : ∀ i, w i ≠ 0) (hG : IsUnit (weightedGram X w))
    (z : m → ℝ) : Xᵀ *ᵥ (w * (z - X *ᵥ wlsEstimate X w z)) = 0 :=
  (normal_eq_iff_eq_wlsEstimate hw hG z _).mpr rfl

/-- With nonzero, nonnegative weights and an invertible weighted Gram matrix, the WLS estimate
minimizes the weighted residual sum of squares. -/
theorem wrss_wlsEstimate_le (hw : ∀ i, w i ≠ 0) (hw0 : ∀ i, 0 ≤ w i)
    (hG : IsUnit (weightedGram X w)) (z : m → ℝ) (b : k → ℝ) :
    wrss X w z (wlsEstimate X w z) ≤ wrss X w z b := by
  set b₀ := wlsEstimate X w z
  set r := z - X *ᵥ b₀
  set d := X *ᵥ (b₀ - b)
  have hnormal : Xᵀ *ᵥ (w * r) = 0 := normal_eq_wlsEstimate hw hG z
  have hcross : ∑ i, w i * r i * d i = 0 := by
    have : (w * r) ⬝ᵥ d = 0 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hnormal, zero_dotProduct]
    simpa [dotProduct] using this
  have hsplit : ∀ i, z i - (X *ᵥ b) i = r i + d i := by
    intro i
    simp only [r, d, mulVec_sub, Pi.sub_apply]
    ring
  have hexp : wrss X w z b = wrss X w z b₀ + 2 * ∑ i, w i * r i * d i + ∑ i, w i * d i ^ 2 := by
    simp only [wrss, hsplit, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [r, Pi.sub_apply]
    ring
  rw [hexp, hcross, mul_zero, add_zero, le_add_iff_nonneg_right]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hw0 i) (sq_nonneg _)

/-! ### Newton–Raphson and IRLS -/

/-- The Newton–Raphson update `β - (hess β)⁻¹ (score β)` for a stationary point of a function
with gradient `score` and Hessian `hess`. -/
noncomputable def newtonStep (score : (k → ℝ) → k → ℝ) (hess : (k → ℝ) → Matrix k k ℝ)
    (β : k → ℝ) : k → ℝ :=
  β - (hess β)⁻¹ *ᵥ score β

/-- The IRLS weights `wᵢ = weight ((X β)ᵢ)`; for a canonical GLM, `weight = b''` is the variance
function evaluated at the linear predictor. -/
def irlsWeights (weight : ℝ → ℝ) (X : Matrix m k ℝ) (β : k → ℝ) : m → ℝ :=
  fun i => weight ((X *ᵥ β) i)

/-- The working response `zᵢ = ηᵢ + (yᵢ - mean ηᵢ) / weight ηᵢ` at `η = X β`. -/
noncomputable def workingResponse (X : Matrix m k ℝ) (y : m → ℝ) (mean weight : ℝ → ℝ)
    (β : k → ℝ) : m → ℝ :=
  fun i => (X *ᵥ β) i + (y i - mean ((X *ᵥ β) i)) / weight ((X *ᵥ β) i)

/-- One IRLS update: the weighted least-squares fit of the working response on `X` with the
IRLS weights. -/
noncomputable def irlsStep (X : Matrix m k ℝ) (y : m → ℝ) (mean weight : ℝ → ℝ)
    (β : k → ℝ) : k → ℝ :=
  wlsEstimate X (irlsWeights weight X β) (workingResponse X y mean weight β)

/-- The `n`-th IRLS iterate from the starting value `β₀`. -/
noncomputable def irlsIterate (X : Matrix m k ℝ) (y : m → ℝ) (mean weight : ℝ → ℝ)
    (β₀ : k → ℝ) (n : ℕ) : k → ℝ :=
  (irlsStep X y mean weight)^[n] β₀

/-- The canonical-link GLM hypotheses on a score `score` and Hessian `hess`, with mean function
`mean = b'`, variance function `weight = b''` and dispersion `1`:
`score β = Xᵀ (y - μ(β))` and `hess β = -Xᵀ W(β) X`, where `μᵢ(β) = mean (X β)ᵢ` and
`W(β) = diag (weight (X β)ᵢ)`. The Hessian identity, with no dependence on `y`, is where the
canonical link enters: observed and Fisher information coincide. -/
structure IsCanonicalScoreHessian (X : Matrix m k ℝ) (y : m → ℝ) (mean weight : ℝ → ℝ)
    (score : (k → ℝ) → k → ℝ) (hess : (k → ℝ) → Matrix k k ℝ) : Prop where
  /-- The score is `Xᵀ (y - μ(β))`. -/
  score_eq : ∀ β, score β = Xᵀ *ᵥ (y - fun i => mean ((X *ᵥ β) i))
  /-- The Hessian is `-Xᵀ W(β) X`. -/
  hess_eq : ∀ β, hess β = -weightedGram X (irlsWeights weight X β)

variable {y : m → ℝ} {mean weight : ℝ → ℝ}

omit [Fintype m] [DecidableEq m] [DecidableEq k] in
private theorem weights_mul_workingResponse (β : k → ℝ)
    (hw : ∀ i, irlsWeights weight X β i ≠ 0) :
    irlsWeights weight X β * workingResponse X y mean weight β =
      irlsWeights weight X β * (X *ᵥ β) + (y - fun i => mean ((X *ᵥ β) i)) := by
  funext i
  have := hw i
  simp only [irlsWeights] at this
  simp only [workingResponse, irlsWeights, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  field_simp

/-- The IRLS step is `β + (Xᵀ W X)⁻¹ Xᵀ (y - μ(β))` for nonzero weights and an invertible
weighted Gram matrix. -/
theorem irlsStep_eq (β : k → ℝ) (hw : ∀ i, irlsWeights weight X β i ≠ 0)
    (hG : IsUnit (weightedGram X (irlsWeights weight X β))) :
    irlsStep X y mean weight β =
      β + (weightedGram X (irlsWeights weight X β))⁻¹ *ᵥ
        (Xᵀ *ᵥ (y - fun i => mean ((X *ᵥ β) i))) := by
  have hdet := (isUnit_iff_isUnit_det _).mp hG
  rw [irlsStep, wlsEstimate_eq hw, weights_mul_workingResponse β hw, mulVec_add,
    transpose_mulVec_mul_mulVec, mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hdet, one_mulVec]

/-- **Newton–Raphson is IRLS.** Under the canonical-link score and Hessian identities, with
nonzero weights and an invertible weighted Gram matrix at `β`, the Newton–Raphson update equals
the weighted least-squares fit of the working response with the IRLS weights. -/
theorem newtonStep_eq_irlsStep {score : (k → ℝ) → k → ℝ} {hess : (k → ℝ) → Matrix k k ℝ}
    (h : IsCanonicalScoreHessian X y mean weight score hess) (β : k → ℝ)
    (hw : ∀ i, irlsWeights weight X β i ≠ 0)
    (hG : IsUnit (weightedGram X (irlsWeights weight X β))) :
    newtonStep score hess β = irlsStep X y mean weight β := by
  have hdet := (isUnit_iff_isUnit_det _).mp hG
  have hinv : (-weightedGram X (irlsWeights weight X β))⁻¹ =
      -(weightedGram X (irlsWeights weight X β))⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, nonsing_inv_mul _ hdet])
  rw [irlsStep_eq β hw hG, newtonStep, h.score_eq, h.hess_eq, hinv, neg_mulVec,
    sub_neg_eq_add]

/-- Newton–Raphson and IRLS generate the same iterates when the weights are nonzero and the
weighted Gram matrix is invertible at every point. -/
theorem newtonIterate_eq_irlsIterate {score : (k → ℝ) → k → ℝ}
    {hess : (k → ℝ) → Matrix k k ℝ} (h : IsCanonicalScoreHessian X y mean weight score hess)
    (hw : ∀ β i, irlsWeights weight X β i ≠ 0)
    (hG : ∀ β, IsUnit (weightedGram X (irlsWeights weight X β))) (β₀ : k → ℝ) (n : ℕ) :
    (newtonStep score hess)^[n] β₀ = irlsIterate X y mean weight β₀ n := by
  have : newtonStep score hess = irlsStep X y mean weight :=
    funext fun β => newtonStep_eq_irlsStep h β (hw β) (hG β)
  rw [this, irlsIterate]

/-- **Fixed points of IRLS are score roots.** With nonzero weights and an invertible weighted
Gram matrix at `β`, the IRLS step fixes `β` iff the canonical score `Xᵀ (y - μ(β))` vanishes. -/
theorem irlsStep_eq_self_iff (β : k → ℝ) (hw : ∀ i, irlsWeights weight X β i ≠ 0)
    (hG : IsUnit (weightedGram X (irlsWeights weight X β))) :
    irlsStep X y mean weight β = β ↔ Xᵀ *ᵥ (y - fun i => mean ((X *ᵥ β) i)) = 0 := by
  rw [irlsStep, eq_comm, ← normal_eq_iff_eq_wlsEstimate hw hG, mul_sub,
    weights_mul_workingResponse β hw, add_sub_cancel_left]

/-- Fixed points of IRLS are exactly the zeros of the score under the canonical-link
hypotheses. -/
theorem irlsStep_eq_self_iff_score_eq_zero {score : (k → ℝ) → k → ℝ}
    {hess : (k → ℝ) → Matrix k k ℝ} (h : IsCanonicalScoreHessian X y mean weight score hess)
    (β : k → ℝ) (hw : ∀ i, irlsWeights weight X β i ≠ 0)
    (hG : IsUnit (weightedGram X (irlsWeights weight X β))) :
    irlsStep X y mean weight β = β ↔ score β = 0 := by
  rw [irlsStep_eq_self_iff β hw hG, h.score_eq]

/-! ### The canonical link produces the Hessian identity -/

/-- **Canonical link ⇒ Hessian identity.** If `mean` has derivative `weight` at every linear
predictor value (for a canonical link, `mean = b'` and `weight = b''`), then the canonical score
`β ↦ Xᵀ (y - μ(β))` has derivative `-Xᵀ W(β) X` at `β`, which is `hess_eq` of
`IsCanonicalScoreHessian`. -/
theorem hasFDerivAt_canonicalScore (β : k → ℝ)
    (hmean : ∀ i, HasDerivAt mean (weight ((X *ᵥ β) i)) ((X *ᵥ β) i)) :
    HasFDerivAt (fun β' => Xᵀ *ᵥ (y - fun i => mean ((X *ᵥ β') i)))
      (LinearMap.toContinuousLinearMap
        (Matrix.toLin' (-weightedGram X (irlsWeights weight X β)))) β := by
  set L : (k → ℝ) →L[ℝ] (m → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' X)
  set T : (m → ℝ) →L[ℝ] (k → ℝ) := LinearMap.toContinuousLinearMap (Matrix.toLin' Xᵀ)
  have hL : ∀ i, HasFDerivAt (fun β' => (X *ᵥ β') i)
      ((ContinuousLinearMap.proj i).comp L) β := fun i =>
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : m => ℝ) i).comp L).hasFDerivAt
  have hg : HasFDerivAt (fun β' i => mean ((X *ᵥ β') i))
      (ContinuousLinearMap.pi fun i =>
        weight ((X *ᵥ β) i) • (ContinuousLinearMap.proj i).comp L) β :=
    hasFDerivAt_pi.mpr fun i => (hmean i).comp_hasFDerivAt β (hL i)
  have hT := T.hasFDerivAt.comp β (hg.const_sub y)
  refine hT.congr_fderiv ?_
  ext v j
  simp only [T, L, ContinuousLinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, neg_mulVec]
  change (Xᵀ *ᵥ -(irlsWeights weight X β * (X *ᵥ v))) j = _
  rw [mulVec_neg, transpose_mulVec_mul_mulVec]

end MathlibExt.Probability.Statistics.GLM.IRLS
