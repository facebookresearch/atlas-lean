/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.GaussianConditioning
public import MathlibExt.Probability.Statistics.GeneralizedLeastSquares
public import MathlibExt.Biology.StatisticalGenetics.LDScore
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Mixed models: Henderson's equations, BLUP, and the LDpred-inf posterior

**The linear mixed model** `y = X b + Z u + e` has fixed effects `b`, random effects `u` with
covariance `G` (for example `G = σ²_g A` with a relationship matrix `A`, see
`MathlibExt.Biology.StatisticalGenetics.Relatedness` and
`MathlibExt.Biology.StatisticalGenetics.Kinship`), and residuals `e` with covariance `R`;
the phenotypic covariance is `V = Z G Zᵀ + R` (`phenCov`). Henderson's mixed-model equations
(MME) avoid inverting `V`:

  `[Xᵀ R⁻¹ X, Xᵀ R⁻¹ Z; Zᵀ R⁻¹ X, Zᵀ R⁻¹ Z + G⁻¹] [b; u] = [Xᵀ R⁻¹ y; Zᵀ R⁻¹ y]`.

For positive definite `G` and `R`, `(b, u)` solves them exactly when `b` solves the generalized
least-squares (GLS) normal equations `Xᵀ V⁻¹ X b = Xᵀ V⁻¹ y` and `u = G Zᵀ V⁻¹ (y - X b)`
(`isMMESolution_iff`); with `Xᵀ V⁻¹ X` invertible the solution is unique, `b̂` is the GLS
estimate, the best linear unbiased estimator by Aitken's theorem
(`MathlibExt.Probability.Statistics.GeneralizedLeastSquares.aitken`), and `û` is the BLUP
(`isMMESolution_iff_gls`). In the Gaussian model, `G Zᵀ V⁻¹ (y - X b)` is the conditional
expectation of `u` given `y` when `b` is known (`condDistrib_mixedModel`,
`condExp_mixedModel`); the BLUP plugs in `b̂`. The best-linear-unbiased-prediction optimality of
`û` among all linear unbiased predictors is not formalized here.

**LDpred-inf.** For `M` markers with LD matrix `R` and `N` individuals, the marginal estimates
`β̂_j = X_jᵀ y / N` of `y = X β + ε` have mean `R β` under mean-zero noise
(`integral_marginalEffect`). Given raw noise second moments `𝔼[ε_i ε_i'] = σ² [i = i']`, their
raw residual-product second moment is `σ² R / N` (`integral_marginalEffect_sub_mul`), with
`R = Xᵀ X / N` (`LDScore.ldCorr`); it is a covariance when the noise is mean-zero. Under the
infinitesimal prior `β ~ N(0, h² / M · I)` and the Gaussian likelihood
`β̂ | β ~ N(R β, R / N)` of Zhu and Stephens (2017), the posterior mean is
`(R + M / (N h²) · I)⁻¹ β̂` (`condDistrib_ldpredInf`), the LDpred-inf estimator of Vilhjálmsson
et al. (2015).

## Main results

* `IsMMESolution`, `isMMESolution_iff`, `isMMESolution_iff_gls`: Henderson's equations give the
  GLS estimate and `û = G Zᵀ V⁻¹ (y - X b̂)`.
* `condDistrib_mixedModel`, `condExp_mixedModel`: in the Gaussian model, given `y`,
  `u ~ N(G Zᵀ V⁻¹ (y - X b), G - G Zᵀ V⁻¹ Z G)` and `𝔼[u | y] = G Zᵀ V⁻¹ (y - X b)`.
* `marginalEffect`, `integral_marginalEffect`, `integral_marginalEffect_sub_mul`: the mean under
  mean-zero noise and the raw residual-product second moment of the marginal estimates.
* `condDistrib_ldpredInf`: the LDpred-inf posterior.

## References

* C. R. Henderson, *Best linear unbiased estimation and prediction under a selection model*,
  Biometrics 31 (1975), 423–447.
* G. K. Robinson, *That BLUP is a good thing: the estimation of random effects*, Stat. Sci. 6
  (1991), 15–32.
* T. H. E. Meuwissen, B. J. Hayes, M. E. Goddard, *Prediction of total genetic value using
  genome-wide dense marker maps*, Genetics 157 (2001), 1819–1829.
* B. J. Vilhjálmsson, J. Yang, H. K. Finucane, et al., *Modeling linkage disequilibrium
  increases accuracy of polygenic risk scores*, Am. J. Hum. Genet. 97 (2015), 576–592.
* X. Zhu, M. Stephens, *Bayesian large-scale multiple regression with summary statistics from
  genome-wide association studies*, Ann. Appl. Stat. 11 (2017), 1561–1592.
-/

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory MetaMathlibExt WithLp
open MathlibExt.Probability.Statistics.GeneralizedLeastSquares
open MathlibExt.Biology.StatisticalGenetics.LDScore
open scoped MatrixOrder

namespace MathlibExt.Biology.StatisticalGenetics.MixedModel

section MME

variable {n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
  [Fintype q] [DecidableEq q]

/-- The phenotypic covariance `V = Z G Zᵀ + R` of the linear mixed model
`y = X b + Z u + e` with `Cov u = G`, `Cov e = R`. -/
def phenCov (Z : Matrix n q ℝ) (G : Matrix q q ℝ) (R : Matrix n n ℝ) : Matrix n n ℝ :=
  Z * G * Zᵀ + R

/-- Henderson's mixed-model equations for `y = X b + Z u + e`, `Cov u = G`, `Cov e = R`:
`[Xᵀ R⁻¹ X, Xᵀ R⁻¹ Z; Zᵀ R⁻¹ X, Zᵀ R⁻¹ Z + G⁻¹] [b; u] = [Xᵀ R⁻¹ y; Zᵀ R⁻¹ y]`. -/
def IsMMESolution (X : Matrix n p ℝ) (Z : Matrix n q ℝ) (G : Matrix q q ℝ) (R : Matrix n n ℝ)
    (y : n → ℝ) (b : p → ℝ) (u : q → ℝ) : Prop :=
  (Xᵀ * R⁻¹ * X) *ᵥ b + (Xᵀ * R⁻¹ * Z) *ᵥ u = (Xᵀ * R⁻¹) *ᵥ y ∧
    (Zᵀ * R⁻¹ * X) *ᵥ b + (Zᵀ * R⁻¹ * Z + G⁻¹) *ᵥ u = (Zᵀ * R⁻¹) *ᵥ y

variable {X : Matrix n p ℝ} {Z : Matrix n q ℝ} {G : Matrix q q ℝ} {R : Matrix n n ℝ}

omit [Fintype n] [DecidableEq n] [DecidableEq q] in
/-- `V = Z G Zᵀ + R` is positive definite. -/
theorem posDef_phenCov [Finite n] (hG : G.PosDef) (hR : R.PosDef) : (phenCov Z G R).PosDef := by
  have h := hG.posSemidef.mul_mul_conjTranspose_same Z
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact Matrix.PosDef.posSemidef_add h hR

private theorem posDef_mmeBlock (hG : G.PosDef) (hR : R.PosDef) :
    (Zᵀ * R⁻¹ * Z + G⁻¹).PosDef := by
  have h := hR.inv.posSemidef.conjTranspose_mul_mul_same Z
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact Matrix.PosDef.posSemidef_add h hG.inv

private theorem isUnit_det_of_posDef {k : Type*} [Fintype k] [DecidableEq k] {A : Matrix k k ℝ}
    (hA : A.PosDef) : IsUnit A.det :=
  (Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit

/-- The key identity behind the mixed-model equations:
`(Zᵀ R⁻¹ Z + G⁻¹) G Zᵀ V⁻¹ = Zᵀ R⁻¹`. -/
private theorem mmeBlock_mul (hG : G.PosDef) (hR : R.PosDef) :
    (Zᵀ * R⁻¹ * Z + G⁻¹) * (G * Zᵀ * (phenCov Z G R)⁻¹) = Zᵀ * R⁻¹ := by
  have hV := isUnit_det_of_posDef (posDef_phenCov (Z := Z) hG hR)
  have h1 : (Zᵀ * R⁻¹ * Z + G⁻¹) * (G * Zᵀ) = Zᵀ * R⁻¹ * phenCov Z G R := by
    rw [phenCov, Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc G⁻¹ G,
      Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hG), Matrix.one_mul,
      Matrix.mul_assoc Zᵀ R⁻¹ R, Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hR),
      Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV, Matrix.mul_one]

omit [DecidableEq q] in
/-- The second identity: `R⁻¹ - R⁻¹ Z G Zᵀ V⁻¹ = V⁻¹`. -/
private theorem inv_sub_eq (hG : G.PosDef) (hR : R.PosDef) :
    R⁻¹ - R⁻¹ * Z * (G * Zᵀ * (phenCov Z G R)⁻¹) = (phenCov Z G R)⁻¹ := by
  have hV := isUnit_det_of_posDef (posDef_phenCov (Z := Z) hG hR)
  have h : R⁻¹ * phenCov Z G R - R⁻¹ * Z * (G * Zᵀ) = 1 := by
    rw [phenCov, Matrix.mul_add, Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef hR)]
    simp only [Matrix.mul_assoc]
    abel
  calc R⁻¹ - R⁻¹ * Z * (G * Zᵀ * (phenCov Z G R)⁻¹)
      = (R⁻¹ * phenCov Z G R - R⁻¹ * Z * (G * Zᵀ)) * (phenCov Z G R)⁻¹ := by
        rw [Matrix.sub_mul, Matrix.mul_assoc R⁻¹ (phenCov Z G R), Matrix.mul_nonsing_inv _ hV,
          Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = (phenCov Z G R)⁻¹ := by rw [h, Matrix.one_mul]

private theorem aux_sub_add_iff {M : Type*} [AddCommGroup M] (a b c : M) :
    a - b + c = a ↔ b - c = 0 := by
  rw [← sub_eq_zero (a := a - b + c), show a - b + c - a = c - b by abel, sub_eq_zero,
    sub_eq_zero, eq_comm]

omit [DecidableEq p] in
/-- **Henderson's mixed-model equations** (Henderson 1975; Robinson 1991): for positive definite
`G` and `R` and `V = Z G Zᵀ + R`, `(b, u)` solves the mixed-model equations if and only if `b`
solves the generalized least-squares normal equations `Xᵀ V⁻¹ X b = Xᵀ V⁻¹ y` and
`u = G Zᵀ V⁻¹ (y - X b)`. -/
theorem isMMESolution_iff (hG : G.PosDef) (hR : R.PosDef) (y : n → ℝ) (b : p → ℝ)
    (u : q → ℝ) :
    IsMMESolution X Z G R y b u ↔
      (Xᵀ * (phenCov Z G R)⁻¹ * X) *ᵥ b = (Xᵀ * (phenCov Z G R)⁻¹) *ᵥ y ∧
        u = (G * Zᵀ * (phenCov Z G R)⁻¹) *ᵥ (y - X *ᵥ b) := by
  set V := phenCov Z G R with hVdef
  set C := Zᵀ * R⁻¹ * Z + G⁻¹ with hC
  set K := G * Zᵀ * V⁻¹ with hK
  have hCd := isUnit_det_of_posDef (posDef_mmeBlock (Z := Z) hG hR)
  have hCK : C * K = Zᵀ * R⁻¹ := mmeBlock_mul hG hR
  have hRK : R⁻¹ - R⁻¹ * Z * K = V⁻¹ := inv_sub_eq hG hR
  -- the second equation is equivalent to `u = K (y - X b)`
  have h2 : (Zᵀ * R⁻¹ * X) *ᵥ b + C *ᵥ u = (Zᵀ * R⁻¹) *ᵥ y ↔ u = K *ᵥ (y - X *ᵥ b) := by
    have e : (Zᵀ * R⁻¹ * X) *ᵥ b + C *ᵥ u = (Zᵀ * R⁻¹) *ᵥ y ↔
        C *ᵥ u = (Zᵀ * R⁻¹) *ᵥ (y - X *ᵥ b) := by
      rw [mulVec_sub, mulVec_mulVec, eq_sub_iff_add_eq, add_comm]
    rw [e, ← hCK, ← mulVec_mulVec]
    constructor
    · intro h
      have := congrArg (C⁻¹ *ᵥ ·) h
      simp only [mulVec_mulVec, ← Matrix.mul_assoc] at this
      rwa [Matrix.nonsing_inv_mul _ hCd, Matrix.one_mul, one_mulVec] at this
    · intro h; rw [h]
  -- given `u = K (y - X b)`, the first equation is the GLS normal equation
  have h1 : ∀ u, u = K *ᵥ (y - X *ᵥ b) →
      ((Xᵀ * R⁻¹ * X) *ᵥ b + (Xᵀ * R⁻¹ * Z) *ᵥ u = (Xᵀ * R⁻¹) *ᵥ y ↔
        (Xᵀ * V⁻¹ * X) *ᵥ b = (Xᵀ * V⁻¹) *ᵥ y) := by
    intro u hu
    subst hu
    have hw : (Xᵀ * R⁻¹ * X) *ᵥ b =
        (Xᵀ * R⁻¹) *ᵥ y - (Xᵀ * R⁻¹) *ᵥ (y - X *ᵥ b) := by
      rw [mulVec_sub, mulVec_mulVec]; abel
    have hv : (Xᵀ * V⁻¹) *ᵥ (y - X *ᵥ b) = (Xᵀ * R⁻¹) *ᵥ (y - X *ᵥ b) -
        (Xᵀ * R⁻¹ * Z) *ᵥ (K *ᵥ (y - X *ᵥ b)) := by
      rw [← hRK, mulVec_mulVec, ← sub_mulVec]
      congr 1
      simp only [Matrix.mul_sub, Matrix.mul_assoc]
    have e1 : (Xᵀ * R⁻¹ * X) *ᵥ b + (Xᵀ * R⁻¹ * Z) *ᵥ (K *ᵥ (y - X *ᵥ b)) =
        (Xᵀ * R⁻¹) *ᵥ y ↔ (Xᵀ * V⁻¹) *ᵥ (y - X *ᵥ b) = 0 := by
      rw [hw, hv, aux_sub_add_iff]
    rw [e1, mulVec_sub, mulVec_mulVec, sub_eq_zero, eq_comm]
  constructor
  · rintro ⟨e1, e2⟩
    have hu := h2.mp e2
    exact ⟨(h1 u hu).mp e1, hu⟩
  · rintro ⟨e1, hu⟩
    exact ⟨(h1 u hu).mpr e1, h2.mpr hu⟩

/-- **The MME solution is the GLS estimate and the BLUP** (Henderson 1975): if moreover
`Xᵀ V⁻¹ X` is invertible, the mixed-model equations have the unique solution
`b̂ = (Xᵀ V⁻¹ X)⁻¹ Xᵀ V⁻¹ y` (the GLS estimate) and `û = G Zᵀ V⁻¹ (y - X b̂)`. -/
theorem isMMESolution_iff_gls (hG : G.PosDef) (hR : R.PosDef)
    (hX : IsUnit (Xᵀ * (phenCov Z G R)⁻¹ * X)) (y : n → ℝ) (b : p → ℝ) (u : q → ℝ) :
    IsMMESolution X Z G R y b u ↔
      b = glsMatrix X (phenCov Z G R) *ᵥ y ∧
        u = (G * Zᵀ * (phenCov Z G R)⁻¹) *ᵥ (y - X *ᵥ b) := by
  rw [isMMESolution_iff hG hR]
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hX
  refine and_congr_left fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · rw [glsMatrix, Matrix.mul_assoc _ Xᵀ, ← mulVec_mulVec, ← h, mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hd, one_mulVec]
  · rw [h, glsMatrix, mulVec_mulVec]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

end MME

section Gaussian

variable {n p q : Type*} [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
  [Fintype q] [DecidableEq q]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **BLUP as a conditional law** (Henderson 1975; Robinson 1991): in the Gaussian mixed model
`y = X b + Z u + e` with fixed effects `b`, random effects `u ~ N(0, G)` and residuals
`e ~ N(0, R)` independent, `G` and `R` positive definite, the conditional law of `u` given `y`
is `N(G Zᵀ V⁻¹ (y - X b), G - G Zᵀ V⁻¹ Z G)` with `V = Z G Zᵀ + R` (for almost every `y`). -/
theorem condDistrib_mixedModel {u : Ω → EuclideanSpace ℝ q} {e : Ω → EuclideanSpace ℝ n}
    (hu : Measurable u) (he : Measurable e) (hind : IndepFun u e P) {G : Matrix q q ℝ}
    {R : Matrix n n ℝ} (hG : G.PosDef) (hR : R.PosDef)
    (hul : P.map u = multivariateGaussian 0 G) (hel : P.map e = multivariateGaussian 0 R)
    (X : Matrix n p ℝ) (Z : Matrix n q ℝ) (b : EuclideanSpace ℝ p) :
    ∀ᵐ y ∂P.map (fun ω => toEuclideanLin X b + toEuclideanLin Z (u ω) + e ω),
      condDistrib u (fun ω => toEuclideanLin X b + toEuclideanLin Z (u ω) + e ω) P y =
        multivariateGaussian
          (toEuclideanLin (G * Zᵀ * (phenCov Z G R)⁻¹) (y - toEuclideanLin X b))
          (G - G * Zᵀ * (phenCov Z G R)⁻¹ * (Z * G)) := by
  set E := (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := q) (κ := n)).symm with hE
  set Mx : Matrix (q ⊕ n) (q ⊕ n) ℝ := fromBlocks 1 0 Z 1 with hM
  set c : EuclideanSpace ℝ (q ⊕ n) := E (0, toEuclideanLin X b) with hc
  set V : Ω → EuclideanSpace ℝ (q ⊕ n) := fun ω => c + toEuclideanLin Mx (E (u ω, e ω))
    with hVdef
  have hcm : Measurable fun ω => E (u ω, e ω) := E.continuous.measurable.comp (hu.prodMk he)
  have hVm : Measurable V :=
    (measurable_const.add ((continuous_toEuclideanLin Mx).measurable.comp hcm))
  have hMe : ∀ a d, toEuclideanLin Mx (E (a, d)) = E (a, toEuclideanLin Z a + d) := fun a d => by
    rw [hM, hE, toEuclideanLin_fromBlocks_sumEquivProd_symm, toEuclideanLin_one_apply,
      toEuclideanLin_one_apply, map_zero, LinearMap.zero_apply, add_zero]
  have hdiag := posSemidef_fromBlocks_zero hG.posSemidef hR.posSemidef
  have hcov : Mx * fromBlocks G 0 0 R * Mxᵀ = fromBlocks G (G * Zᵀ) (Z * G) (Z * G * Zᵀ + R) :=
    fromBlocks_one_zero_mul_mul_transpose G R Z
  have hjoint := posSemidef_fromBlocks_linear hG.posSemidef hR.posSemidef Z
  have hlawV : P.map V = multivariateGaussian (c + E (0, toEuclideanLin Z 0))
      (fromBlocks G (G * Zᵀ) (Z * G) (Z * G * Zᵀ + R)) := by
    rw [show V = (c + ·) ∘ toEuclideanLin Mx ∘ fun ω => E (u ω, e ω) from rfl,
      ← Measure.map_map (by fun_prop) ((continuous_toEuclideanLin _).measurable.comp hcm),
      ← Measure.map_map (continuous_toEuclideanLin _).measurable hcm,
      map_sumEquivProd_symm_of_indepFun hu he hind hG.posSemidef hR.posSemidef hul hel,
      map_toEuclideanLin_multivariateGaussian _ _ hdiag, hcov, hMe, add_zero,
      map_add_multivariateGaussian]
  have hinv : IsUnit (fromBlocks G (G * Zᵀ) (Z * G) (Z * G * Zᵀ + R)).toBlocks₂₂.det := by
    simpa [phenCov] using (Matrix.isUnit_iff_isUnit_det _).mp (posDef_phenCov (Z := Z) hG hR).isUnit
  have h := condDistrib_multivariateGaussian hVm hjoint hlawV hinv
  have hblk1 : ∀ a d, toEuclideanLin (blockRow (1 : Matrix q q ℝ) 0) (E (a, d)) = a :=
    fun a d => by
      rw [hE, toEuclideanLin_blockRow_sumEquivProd_symm, toEuclideanLin_one_apply, map_zero,
        LinearMap.zero_apply, add_zero]
  have hblk2 : ∀ a d, toEuclideanLin (blockRow (0 : Matrix n q ℝ) 1) (E (a, d)) = d :=
    fun a d => by
      rw [hE, toEuclideanLin_blockRow_sumEquivProd_symm, toEuclideanLin_one_apply, map_zero,
        LinearMap.zero_apply, zero_add]
  have hX : (fun ω => toEuclideanLin (blockRow (1 : Matrix q q ℝ) 0) (V ω)) = u := by
    funext ω
    simp only [hVdef, map_add, hMe, hc, hblk1, zero_add]
  have hY : (fun ω => toEuclideanLin (blockRow (0 : Matrix n q ℝ) 1) (V ω)) =
      fun ω => toEuclideanLin X b + toEuclideanLin Z (u ω) + e ω := by
    funext ω
    simp only [hVdef, map_add, hMe, hc, hblk2, add_assoc]
  rw [hX, hY] at h
  simpa [hblk1, hblk2, hc, phenCov, Matrix.mul_assoc] using h

/-- **BLUP is the conditional expectation** in the Gaussian mixed model:
`𝔼[u | y] = G Zᵀ V⁻¹ (y - X b)` almost surely. -/
theorem condExp_mixedModel {u : Ω → EuclideanSpace ℝ q} {e : Ω → EuclideanSpace ℝ n}
    (hu : Measurable u) (he : Measurable e) (hind : IndepFun u e P) {G : Matrix q q ℝ}
    {R : Matrix n n ℝ} (hG : G.PosDef) (hR : R.PosDef)
    (hul : P.map u = multivariateGaussian 0 G) (hel : P.map e = multivariateGaussian 0 R)
    (X : Matrix n p ℝ) (Z : Matrix n q ℝ) (b : EuclideanSpace ℝ p) :
    P[u | MeasurableSpace.comap (fun ω => toEuclideanLin X b + toEuclideanLin Z (u ω) + e ω)
        inferInstance] =ᵐ[P]
      fun ω => toEuclideanLin (G * Zᵀ * (phenCov Z G R)⁻¹)
        (toEuclideanLin Z (u ω) + e ω) := by
  have hum : Integrable u P := by
    have : Integrable id (P.map u) := by rw [hul]; exact IsGaussian.integrable_id
    exact (integrable_map_measure aestronglyMeasurable_id hu.aemeasurable).mp this
  have hym : Measurable fun ω => toEuclideanLin X b + toEuclideanLin Z (u ω) + e ω :=
    (measurable_const.add ((continuous_toEuclideanLin Z).measurable.comp hu)).add he
  have h1 := condExp_ae_eq_integral_condDistrib' hym hum
  have h3 := ae_of_ae_map hym.aemeasurable (condDistrib_mixedModel hu he hind hG hR hul hel X Z b)
  filter_upwards [h1, h3] with ω h1 h3
  rw [h1, h3, integral_id_multivariateGaussian]
  congr 1
  abel

end Gaussian

section LDpred

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

private theorem commute_inv {M : ℕ} {A R : Matrix (Fin M) (Fin M) ℝ} (hA : IsUnit A.det)
    (h : A * R = R * A) : A⁻¹ * R = R * A⁻¹ := by
  calc A⁻¹ * R = A⁻¹ * R * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hA, Matrix.mul_one]
    _ = A⁻¹ * (A * R) * A⁻¹ := by rw [h]; simp only [Matrix.mul_assoc]
    _ = R * A⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

/-- The LDpred-inf gain and posterior covariance (matrix algebra). -/
private theorem ldpred_algebra {M N : ℕ} (hM : 0 < M) (hN : 0 < N) {h2 : ℝ} (hh2 : 0 < h2)
    {R : Matrix (Fin M) (Fin M) ℝ} (hR : R.PosDef) :
    (h2 / M) • (1 : Matrix (Fin M) (Fin M) ℝ) * Rᵀ *
        (R * ((h2 / M) • 1) * Rᵀ + (1 / N : ℝ) • R)⁻¹ = (R + (M / (N * h2) : ℝ) • 1)⁻¹ ∧
      (h2 / M) • (1 : Matrix (Fin M) (Fin M) ℝ) - (h2 / M) • (1 : Matrix (Fin M) (Fin M) ℝ) *
        Rᵀ * (R * ((h2 / M) • 1) * Rᵀ + (1 / N : ℝ) • R)⁻¹ * (R * ((h2 / M) • 1)) =
        (1 / N : ℝ) • (R + (M / (N * h2) : ℝ) • 1)⁻¹ := by
  set a : ℝ := h2 / M with ha
  set c : ℝ := M / (N * h2) with hc
  set A := R + c • (1 : Matrix (Fin M) (Fin M) ℝ) with hAdef
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 < a := div_pos hh2 hMr
  have hc0 : 0 < c := div_pos hMr (mul_pos hNr hh2)
  have hac : a * c = 1 / N := by rw [ha, hc]; field_simp
  have hRt : Rᵀ = R := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hApd : A.PosDef := hR.add (Matrix.PosDef.one.smul hc0)
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).mp hApd.isUnit
  have hRd : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det _).mp hR.isUnit
  have hD : R * (a • 1) * Rᵀ + (1 / N : ℝ) • R = a • (R * A) := by
    rw [hRt, hAdef, Matrix.mul_add, smul_add, ← hac, mul_smul]
    simp
  have hAR : A * R = R * A := by
    rw [hAdef, Matrix.add_mul, Matrix.mul_add]; simp
  have hcomm := commute_inv hAd hAR
  have hDinv : (a • (R * A))⁻¹ = a⁻¹ • (A⁻¹ * R⁻¹) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ ha0.ne', one_smul,
      Matrix.mul_assoc, ← Matrix.mul_assoc R⁻¹, Matrix.nonsing_inv_mul _ hRd, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hAd]
  have hgain : a • (1 : Matrix (Fin M) (Fin M) ℝ) * Rᵀ * (R * (a • 1) * Rᵀ + (1 / N : ℝ) • R)⁻¹ =
      A⁻¹ := by
    rw [hD, hDinv, hRt, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, mul_inv_cancel₀ ha0.ne', one_smul, ← Matrix.mul_assoc, ← hcomm,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRd, Matrix.mul_one]
  refine ⟨hgain, ?_⟩
  rw [hgain]
  have hAR' : A⁻¹ * R = 1 - c • A⁻¹ := by
    have : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hAd
    rw [hAdef, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one] at this
    rw [← this]; abel
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, hAR', smul_sub, smul_smul, hac,
    sub_sub_cancel]

/-- **The LDpred-inf posterior** (Vilhjálmsson et al. 2015; the likelihood
`β̂ | β ~ N(R β, R / N)` of Zhu and Stephens 2017): with `M` markers, `N` individuals,
heritability `h² > 0`, effects `β ~ N(0, h² / M · I)`, an LD matrix `R` that is positive definite,
and marginal estimates `β̂ = R β + ε` with `ε ~ N(0, R / N)` independent of `β`, the posterior law
of `β` given `β̂` is `N((R + M / (N h²) · I)⁻¹ β̂, (1 / N) (R + M / (N h²) · I)⁻¹)`. In particular
`𝔼[β | β̂] = (R + M / (N h²) · I)⁻¹ β̂`. -/
theorem condDistrib_ldpredInf {M N : ℕ} (hM : 0 < M) (hN : 0 < N) {h2 : ℝ} (hh2 : 0 < h2)
    {R : Matrix (Fin M) (Fin M) ℝ} (hR : R.PosDef) {β ε : Ω → EuclideanSpace ℝ (Fin M)}
    (hβ : Measurable β) (hε : Measurable ε) (hind : IndepFun β ε P)
    (hβl : P.map β = multivariateGaussian 0 ((h2 / M) • (1 : Matrix (Fin M) (Fin M) ℝ)))
    (hεl : P.map ε = multivariateGaussian 0 ((1 / N : ℝ) • R)) :
    ∀ᵐ b ∂P.map (fun ω => toEuclideanLin R (β ω) + ε ω),
      condDistrib β (fun ω => toEuclideanLin R (β ω) + ε ω) P b =
        multivariateGaussian (toEuclideanLin (R + (M / (N * h2) : ℝ) • 1)⁻¹ b)
          ((1 / N : ℝ) • (R + (M / (N * h2) : ℝ) • 1)⁻¹) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : ((h2 / M) • (1 : Matrix (Fin M) (Fin M) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (div_pos hh2 hMr)
  have hRN : ((1 / N : ℝ) • R).PosDef := hR.smul (by positivity)
  have hinv : IsUnit (R * ((h2 / M) • 1) * Rᵀ + (1 / N : ℝ) • R).det := by
    have h := hS.posSemidef.mul_mul_conjTranspose_same R
    rw [conjTranspose_eq_transpose_of_trivial] at h
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.posSemidef_add h hRN).isUnit
  have h := condDistrib_linear_add_of_indepFun hβ hε hind hS.posSemidef hRN.posSemidef hβl hεl R
    hinv
  obtain ⟨hgain, hcov⟩ := ldpred_algebra hM hN hh2 hR
  filter_upwards [h] with b hb
  rw [hb, hcov, hgain]
  simp

end LDpred

section MarginalEffects

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N M : ℕ}

/-- The `N`-normalized marginal association estimate `β̂_j = X_jᵀ y / N` of marker `j` for the
phenotype `y = X β + ε` (fixed effects `β`, noise `ε`). -/
noncomputable def marginalEffect (X : Matrix (Fin N) (Fin M) ℝ) (β : Fin M → ℝ)
    (ε : Fin N → Ω → ℝ) (j : Fin M) (ω : Ω) : ℝ :=
  (∑ i, X i j * (∑ k, X i k * β k + ε i ω)) / N

private theorem marginalEffect_eq (X : Matrix (Fin N) (Fin M) ℝ) (β : Fin M → ℝ)
    (ε : Fin N → Ω → ℝ) (j : Fin M) (ω : Ω) :
    marginalEffect X β ε j ω = ∑ k, ldCorr X j k * β k + (∑ i, X i j * ε i ω) / N := by
  simp only [marginalEffect, ldCorr, mul_add, Finset.sum_add_distrib, add_div, Finset.mul_sum]
  congr 1
  simp only [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

variable [IsProbabilityMeasure P]

/-- **The mean of the marginal estimates** (Zhu and Stephens 2017): for fixed effects `β` and
noise with mean zero, `𝔼[X_jᵀ y / N] = (R β)_j` with `R = Xᵀ X / N` (`ldCorr`). -/
theorem integral_marginalEffect (X : Matrix (Fin N) (Fin M) ℝ) (β : Fin M → ℝ)
    {ε : Fin N → Ω → ℝ} (hε : ∀ i, Integrable (ε i) P) (hmean : ∀ i, ∫ ω, ε i ω ∂P = 0)
    (j : Fin M) :
    ∫ ω, marginalEffect X β ε j ω ∂P = ∑ k, ldCorr X j k * β k := by
  simp only [marginalEffect_eq]
  have hi : Integrable (fun ω => ∑ i, X i j * ε i ω) P :=
    integrable_finsetSum _ fun i _ => (hε i).const_mul _
  rw [integral_add (integrable_const _) (hi.div_const _), integral_const, integral_div,
    integral_finsetSum _ fun i _ => (hε i).const_mul _]
  simp [integral_const_mul, hmean]

omit [IsProbabilityMeasure P] in
/-- **The raw residual-product second moment of the marginal estimates** (Zhu and Stephens
2017): if `𝔼[ε_i ε_i'] = σ² [i = i']`, then
`𝔼[(β̂_j - (R β)_j)(β̂_k - (R β)_k)] = σ² / N · R_jk`.

This theorem deliberately assumes neither that `P` is a probability measure nor that the noise
has mean zero, so its conclusion is not by itself a covariance or a Gaussian likelihood. With a
probability measure and mean-zero noise, `integral_marginalEffect` identifies `R β` as the mean,
and this raw second moment is the corresponding covariance. -/
theorem integral_marginalEffect_sub_mul (X : Matrix (Fin N) (Fin M) ℝ) (β : Fin M → ℝ)
    {ε : Fin N → Ω → ℝ} {σ2 : ℝ} (hε : ∀ i i', Integrable (fun ω => ε i ω * ε i' ω) P)
    (hsecondMoment : ∀ i i', ∫ ω, ε i ω * ε i' ω ∂P = if i = i' then σ2 else 0)
    (j k : Fin M) :
    ∫ ω, (marginalEffect X β ε j ω - ∑ l, ldCorr X j l * β l) *
        (marginalEffect X β ε k ω - ∑ l, ldCorr X k l * β l) ∂P = σ2 / N * ldCorr X j k := by
  simp only [marginalEffect_eq, add_sub_cancel_left]
  have h : (fun ω => (∑ i, X i j * ε i ω) / N * ((∑ i, X i k * ε i ω) / N)) =
      fun ω => (∑ i, ∑ i', X i j * X i' k * (ε i ω * ε i' ω)) / N ^ 2 := by
    funext ω
    rw [div_mul_div_comm, Finset.sum_mul_sum, sq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    ring
  rw [h, integral_div, integral_finsetSum _ fun i _ =>
    integrable_finsetSum _ fun i' _ => (hε i i').const_mul _]
  simp_rw [integral_finsetSum _ fun i' _ => (hε _ i').const_mul _, integral_const_mul,
    hsecondMoment]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ldCorr]
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← Finset.sum_mul]
    field_simp

end MarginalEffects

end MathlibExt.Biology.StatisticalGenetics.MixedModel
