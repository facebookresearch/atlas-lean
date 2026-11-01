/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScore
public import MathlibExt.LinearAlgebra.Matrix.FrischWaughLovell
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Signed LD profile regression: the first-moment identity and unbiasedness

Signed LD profile (SLDP) regression (Reshef et al. 2018) detects a directional effect of a
signed functional annotation `v ∈ ℝ^M` on a trait. Its model (Methods, Equations 2–3) is a linear
phenotype `y = X β + ε` on `N` individuals and `M` standardized markers, with true effects whose
mean is proportional to the annotation, `𝔼 β = μ v` (other moments are unrestricted). The vector
of marginal correlations `α̂ = Xᵀ y / N` then satisfies (Methods, Equation 5, first moment)

  `𝔼 α̂ = μ R v`,

where `R v` is the *signed LD profile* of `v`. The paper states this with the population LD
matrix `R` as an approximate identity. Conditional on the genotype matrix it holds **exactly**
with the in-sample LD matrix `R̂ = Xᵀ X / N` (`Model.integral_alphaHat`,
`Model.integral_alphaHat_of_mean`); replacing `R̂` by the population `R` is the paper's
approximation and is not formalized.

SLDP estimates `μ` by generalized least squares of `α̂` on `R v` with inverse weight matrix
`Ω = σ² R² + R / N`. For any weight matrix `W` with `⟪s, s⟫_W ≠ 0`, `s = R̂ v`, the estimator
`⟪s, α̂⟫_W / ⟪s, s⟫_W` is unbiased for `μ` (`Model.integral_gls_estimator`). Covariates, in
particular the paper's signed background model, are handled by regressing `R̂ u` out of both
`α̂` and `R̂ v` by the same weighted least squares and regressing residual on residual
(Methods, "Controlling for covariates"); if `𝔼 β = μ v + U γ` for background annotations `U`,
that residualized estimator is unbiased for `μ` whatever `γ` is
(`Model.integral_gls_estimator_of_background`), and by `Matrix.frischWaughLovell` it is the
coefficient of `R̂ v` in the joint regression.

## Main results

* `Model`, `Model.alphaHat`, `ldMatrix`.
* `Model.integral_alphaHat`: `𝔼 α̂ = R̂ 𝔼 β` exactly.
* `Model.integral_alphaHat_of_mean`: `𝔼 α̂ = μ R̂ v` when `𝔼 β = μ v`.
* `Model.integral_gls_estimator`, `Model.integral_gls_estimator_of_background`: unbiasedness.

## References

* Y. A. Reshef, H. K. Finucane, D. R. Kelley, A. Gusev, D. Kotliar, J. C. Ulirsch, et al.,
  *Detecting genome-wide directional effects of transcription factor binding on polygenic
  disease risk*, Nat. Genet. 50 (2018), 1483–1493.
-/

@[expose] public section

open MeasureTheory Matrix

namespace MathlibExt.Biology.StatisticalGenetics.SignedLDProfile

open LDScore

variable {N M : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

/-- The in-sample LD matrix `R̂ = Xᵀ X / N`, with entries `ldCorr X j k`. -/
noncomputable def ldMatrix (X : Matrix (Fin N) (Fin M) ℝ) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of (ldCorr X)

/-- The linear phenotype model of SLDP regression at the level of first moments: integrable
random effects `β` with means `meanBeta` and integrable noise `ε` of mean zero. (SLDP's model
takes `meanBeta = μ v` for a signed annotation `v`; second moments are not needed for the
first-moment identity.) -/
structure Model (P : Measure Ω) (N M : ℕ) where
  /-- The mean `𝔼 β` of the true effects. -/
  meanBeta : Fin M → ℝ
  /-- Random per-marker effects. -/
  beta : Fin M → Ω → ℝ
  /-- Random environmental noise. -/
  eps : Fin N → Ω → ℝ
  /-- Effects are integrable. -/
  integrable_beta : ∀ k, Integrable (beta k) P
  /-- Noise terms are integrable. -/
  integrable_eps : ∀ i, Integrable (eps i) P
  /-- The effects have mean `meanBeta`. -/
  integral_beta : ∀ k, ∫ ω, beta k ω ∂P = meanBeta k
  /-- The noise has mean zero. -/
  integral_eps : ∀ i, ∫ ω, eps i ω ∂P = 0

namespace Model

variable {P : Measure Ω} (D : Model P N M) (X : Matrix (Fin N) (Fin M) ℝ)

/-- The phenotype `y = X β + ε`. -/
def pheno (i : Fin N) (ω : Ω) : ℝ := ∑ k, X i k * D.beta k ω + D.eps i ω

/-- The vector `α̂ = Xᵀ y / N` of marginal correlations between the (standardized) markers and
the phenotype. -/
noncomputable def alphaHat (ω : Ω) (j : Fin M) : ℝ := (∑ i, X i j * D.pheno X i ω) / N

private theorem alphaHat_eq_sum (j : Fin M) (ω : Ω) :
    D.alphaHat X ω j =
      ∑ k, ldCorr X j k * D.beta k ω + ∑ i, (X i j / N) * D.eps i ω := by
  unfold alphaHat pheno ldCorr
  simp_rw [mul_add, Finset.sum_add_distrib, add_div, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, div_mul_eq_mul_div, Finset.sum_div]

private theorem integrable_alphaHat (j : Fin M) : Integrable (fun ω => D.alphaHat X ω j) P := by
  simp_rw [alphaHat_eq_sum]
  exact (integrable_finsetSum _ fun k _ => (D.integrable_beta k).const_mul _).add
    (integrable_finsetSum _ fun i _ => (D.integrable_eps i).const_mul _)

/-- **First-moment identity, exact in-sample form**: conditional on the genotype matrix,
`𝔼 α̂ = R̂ 𝔼 β` with `R̂ = Xᵀ X / N`. -/
theorem integral_alphaHat (j : Fin M) :
    ∫ ω, D.alphaHat X ω j ∂P = (ldMatrix X *ᵥ D.meanBeta) j := by
  simp_rw [alphaHat_eq_sum]
  rw [integral_add (integrable_finsetSum _ fun k _ => (D.integrable_beta k).const_mul _)
    (integrable_finsetSum _ fun i _ => (D.integrable_eps i).const_mul _),
    integral_finsetSum _ fun k _ => (D.integrable_beta k).const_mul _,
    integral_finsetSum _ fun i _ => (D.integrable_eps i).const_mul _]
  simp [integral_const_mul, D.integral_beta, D.integral_eps, mulVec, dotProduct, ldMatrix]

/-- **SLDP first-moment identity** (Reshef et al. 2018, Methods, Equation 5): if the true effects
have mean `μ v`, then `𝔼 α̂ = μ R̂ v`, a multiple of the signed LD profile `R̂ v` of `v`. -/
theorem integral_alphaHat_of_mean {mu : ℝ} {v : Fin M → ℝ}
    (hmean : D.meanBeta = mu • v) (j : Fin M) :
    ∫ ω, D.alphaHat X ω j ∂P = mu * (ldMatrix X *ᵥ v) j := by
  rw [D.integral_alphaHat X j, hmean, mulVec_smul, Pi.smul_apply, smul_eq_mul]

private theorem integral_dotProduct_alphaHat (c : Fin M → ℝ) :
    ∫ ω, c ⬝ᵥ D.alphaHat X ω ∂P = c ⬝ᵥ (ldMatrix X *ᵥ D.meanBeta) := by
  unfold dotProduct
  rw [integral_finsetSum _ fun j _ => (D.integrable_alphaHat X j).const_mul _]
  simp_rw [integral_const_mul, D.integral_alphaHat X]

/-- **Unbiasedness of the weighted least-squares estimator**: for any weight matrix `W` and
signed LD profile `s = R̂ v` with `⟪s, s⟫_W = sᵀ W s ≠ 0`, if `𝔼 β = μ v` then
`𝔼 [⟪s, α̂⟫_W / ⟪s, s⟫_W] = μ`, where `⟪a, b⟫_W = aᵀ W b`. SLDP uses the inverse of
`Ω = σ² R² + R / N` as `W`. -/
theorem integral_gls_estimator {mu : ℝ} {v : Fin M → ℝ} (hmean : D.meanBeta = mu • v)
    (W : Matrix (Fin M) (Fin M) ℝ)
    (hne : (ldMatrix X *ᵥ v) ⬝ᵥ (W *ᵥ (ldMatrix X *ᵥ v)) ≠ 0) :
    ∫ ω, (ldMatrix X *ᵥ v) ⬝ᵥ (W *ᵥ D.alphaHat X ω) /
        ((ldMatrix X *ᵥ v) ⬝ᵥ (W *ᵥ (ldMatrix X *ᵥ v))) ∂P = mu := by
  have key (ω : Ω) : (ldMatrix X *ᵥ v) ⬝ᵥ (W *ᵥ D.alphaHat X ω) =
      ((ldMatrix X *ᵥ v) ᵥ* W) ⬝ᵥ D.alphaHat X ω := dotProduct_mulVec _ _ _
  simp_rw [key]
  rw [integral_div, D.integral_dotProduct_alphaHat X, ← dotProduct_mulVec, hmean, mulVec_smul,
    mulVec_smul, dotProduct_smul, smul_eq_mul, mul_div_assoc, div_self hne, mul_one]

/-- **Unbiasedness with covariates** (the signed background model): suppose the true effects
have mean `μ v + U γ` for background annotations `U` (columns `u_b`) with arbitrary coefficients
`γ`, let `A = R̂ U` be their signed LD profiles, and let `z⊥ = R̂ v - A w` be the weighted residual
of the signed LD profile of `v` on `A` (`Aᵀ W z⊥ = 0`) for a symmetric weight matrix `W`. If
`⟪z⊥, z⊥⟫_W ≠ 0`, then `𝔼 [⟪z⊥, α̂⟫_W / ⟪z⊥, z⊥⟫_W] = μ`. By `Matrix.frischWaughLovell` this
estimator equals the coefficient of `R̂ v` in the joint weighted regression of `α̂` on
`[A | R̂ v]`, and the same as regressing the residualized `α̂` on `z⊥`. -/
theorem integral_gls_estimator_of_background {κ : Type*} [Fintype κ] {mu : ℝ} {v : Fin M → ℝ}
    (U : Matrix (Fin M) κ ℝ) (γ : κ → ℝ) (hmean : D.meanBeta = mu • v + U *ᵥ γ)
    {W : Matrix (Fin M) (Fin M) ℝ} (hW : Wᵀ = W) (w : κ → ℝ)
    (hres : (ldMatrix X * U)ᵀ *ᵥ (W *ᵥ (ldMatrix X *ᵥ v - (ldMatrix X * U) *ᵥ w)) = 0)
    (hne : (ldMatrix X *ᵥ v - (ldMatrix X * U) *ᵥ w) ⬝ᵥ
      (W *ᵥ (ldMatrix X *ᵥ v - (ldMatrix X * U) *ᵥ w)) ≠ 0) :
    ∫ ω, (ldMatrix X *ᵥ v - (ldMatrix X * U) *ᵥ w) ⬝ᵥ (W *ᵥ D.alphaHat X ω) /
        ((ldMatrix X *ᵥ v - (ldMatrix X * U) *ᵥ w) ⬝ᵥ
          (W *ᵥ (ldMatrix X *ᵥ v - (ldMatrix X * U) *ᵥ w))) ∂P = mu := by
  set R := ldMatrix X
  set A := R * U
  set zp := R *ᵥ v - A *ᵥ w
  -- `z⊥` is `W`-orthogonal to every vector `A x`
  have horth (x : κ → ℝ) : zp ⬝ᵥ (W *ᵥ (A *ᵥ x)) = 0 := by
    have hsymm : zp ⬝ᵥ (W *ᵥ (A *ᵥ x)) = (A *ᵥ x) ⬝ᵥ (W *ᵥ zp) := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]
    have hadj : (A *ᵥ x) ⬝ᵥ (W *ᵥ zp) = x ⬝ᵥ (Aᵀ *ᵥ (W *ᵥ zp)) := by
      rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
    rw [hsymm, hadj, hres, dotProduct_zero]
  have key (ω : Ω) : zp ⬝ᵥ (W *ᵥ D.alphaHat X ω) = (zp ᵥ* W) ⬝ᵥ D.alphaHat X ω :=
    dotProduct_mulVec _ _ _
  simp_rw [key]
  rw [integral_div, D.integral_dotProduct_alphaHat X, ← dotProduct_mulVec, hmean, mulVec_add,
    mulVec_smul, mulVec_mulVec, mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul,
    horth γ, add_zero, smul_eq_mul]
  have hz : R *ᵥ v = zp + A *ᵥ w := by simp [zp]
  rw [hz, mulVec_add, dotProduct_add, horth w, add_zero, mul_div_assoc, div_self hne, mul_one]

end Model

end MathlibExt.Biology.StatisticalGenetics.SignedLDProfile
