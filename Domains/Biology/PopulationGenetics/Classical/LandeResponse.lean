/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Domains.Biology.StatisticalGenetics.SelectionGradientMultivariate
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Lande's multivariate response to selection

Breeding values `A` and phenotypes `Z` are random vectors in `ι → ℝ`, jointly Gaussian,
with cross-covariance `Cov(A, Z) = G` and `Var(Z) = P` positive definite. Selection
weights individuals by `W(Z)`; selected means are `𝔼[W(Z) X] / 𝔼[W(Z)]`, measured from
the pre-selection mean `𝔼[X]`. With faithful additive transmission, the offspring mean
shift is the selected parents' breeding-value shift. The Gaussian regression identity
gives it as `G P⁻¹ S`, where `S` is the selection differential. In the quantitative-genetic
decomposition `Z = A + E` with `Cov(A, E) = 0`, this cross-covariance `G` is also the
additive genetic covariance `Var(A)`; corollaries below record that Lande form explicitly.

The key Gaussian fact is that the residual `A - G P⁻¹ Z` is uncorrelated with, hence
independent of, `Z`.

## Main results

* `LandeResponse.selectedShift_breeding_eq`: the cross-covariance form `Δz̄ = G P⁻¹ S`.
* `LandeResponse.selectedShift_breeding_eq_geneticCov`: Lande's form when moreover
  `Var(A) = G`.
* `LandeResponse.breeding_response_univariate`: the univariate coefficient
  `Cov(A, Z) / Var(Z)`, and `breeding_response_univariate_of_var` for `R = h² S` when
  `Var(A) = V_A`.
* `LandeResponse.selectedShift_breeding_eq_gradient`: `Δz̄ = G ∇_μ log w̄(μ)` for bounded
  measurable fitness when `Z ~ N(μ, P)`, with the genetic-covariance form in
  `selectedShift_breeding_eq_gradient_geneticCov`.

## References

* R. Lande, "Quantitative genetic analysis of multivariate evolution, applied to
  brain:body size allometry", *Evolution* 33 (1979), 402–416.
* R. Lande and S. J. Arnold, "The measurement of selection on correlated characters",
  *Evolution* 37 (1983), 1210–1226.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Finset

namespace MathlibExt.Biology.PopulationGenetics.Classical.LandeResponse

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The shift of the mean of a trait vector `X` caused by fitness weights `W (Z ω)` on the phenotype
`Z`, measured from the pre-selection mean: `𝔼[W(Z) X] / 𝔼[W(Z)] - 𝔼[X]`. With `X = Z` it is the
selection differential `S`; with `X = A` (breeding values) and faithful additive transmission it
is the response `Δz̄`. Each `𝔼` is an integral against the measure `P`, an ordinary mean when
`P` is a probability measure and the integrand is integrable; the fitness-weighted reading
needs `X i` and `W(Z) X i` integrable. Two conventions, not expectations, make the shift total:
`x / 0 = 0`, so it is `-𝔼[X]` when `𝔼[W(Z)] = 0` (excluded by the theorems), and the integral
of a non-integrable function is set to `0`. -/
noncomputable def selectedShift (W : (ι → ℝ) → ℝ) (Z X : Ω → ι → ℝ) (P : Measure Ω) : ι → ℝ :=
  fun i => (∫ ω, W (Z ω) * X ω i ∂P) / (∫ ω, W (Z ω) ∂P) - ∫ ω, X ω i ∂P

/-- **Gaussian cross-covariance response** `Δz̄ = G P⁻¹ S`. Let `(A, Z)` be jointly
Gaussian with cross-covariance `Cov(A_i, Z_j) = G_ij` and `Cov(Z_i, Z_j) = P_ij`, `P`
positive definite, and select with measurable fitness weights `W(Z) ≥ 0` with
`0 < 𝔼[W(Z)]` and `W(Z) Z_j`, `W(Z) A_i` integrable. Then the selected shift of the
breeding values is `G P⁻¹` applied to the selection differential. This is the regression
identity behind Lande's equation; `selectedShift_breeding_eq_geneticCov` records the
form in which `G` is also the additive genetic covariance `Var(A)`. -/
theorem selectedShift_breeding_eq {A Z : Ω → ι → ℝ} {G Pm : Matrix ι ι ℝ} {W : (ι → ℝ) → ℝ}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P)
    (hG : ∀ i j, cov[fun ω => A ω i, fun ω => Z ω j; P] = G i j)
    (hPZ : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P] = Pm i j) (hPd : Pm.PosDef)
    (hWm : Measurable W) (hW0 : ∀ z, 0 ≤ W z) (hw : 0 < ∫ ω, W (Z ω) ∂P)
    (hWZ : ∀ j, Integrable (fun ω => W (Z ω) * Z ω j) P)
    (hWA : ∀ i, Integrable (fun ω => W (Z ω) * A ω i) P) :
    selectedShift W Z A P = (G * Pm⁻¹) *ᵥ selectedShift W Z Z P := by
  have hprob := hAZ.isProbabilityMeasure
  have hA2 : ∀ i, MemLp (fun ω => A ω i) 2 P := fun i =>
    (hAZ.fst.eval (X := fun i ω => A ω i) i).memLp_two
  have hZ2 : ∀ i, MemLp (fun ω => Z ω i) 2 P := fun i =>
    (hAZ.snd.eval (X := fun i ω => Z ω i) i).memLp_two
  set M := G * Pm⁻¹ with hM
  have hMP : M * Pm = G := by
    rw [hM, Matrix.mul_assoc, nonsing_inv_mul _ hPd.det_pos.ne'.isUnit, Matrix.mul_one]
  set R : ι → Ω → ℝ := fun i ω => A ω i - ∑ k, M i k * Z ω k with hR
  -- `(R, Z)` is a linear image of `(A, Z)`, hence jointly Gaussian
  let L : ((ι → ℝ) × (ι → ℝ)) →ₗ[ℝ] ((ι → ℝ) × (ι → ℝ)) :=
    (LinearMap.fst ℝ _ _ - (Matrix.mulVecLin M).comp (LinearMap.snd ℝ _ _)).prod
      (LinearMap.snd ℝ _ _)
  have hRZ : HasGaussianLaw (fun ω => (fun i => R i ω, fun j => Z ω j)) P := by
    refine (hAZ.map_fun (LinearMap.toContinuousLinearMap L)).congr (ae_of_all _ fun ω => ?_)
    refine Prod.ext (funext fun i => ?_) rfl
    simp [L, R, mulVec, dotProduct]
  -- the residual is uncorrelated with `Z`
  have hcov : ∀ i j, cov[R i, fun ω => Z ω j; P] = 0 := by
    intro i j
    have hs : MemLp (fun ω => ∑ k, M i k * Z ω k) 2 P :=
      memLp_finsetSum _ fun k _ => (hZ2 k).const_mul (M i k)
    rw [hR]
    simp only
    rw [covariance_fun_sub_left (hA2 i) hs (hZ2 j),
      covariance_fun_sum_left (fun k => (hZ2 k).const_mul (M i k)) (hZ2 j)]
    simp only [covariance_const_mul_left, hPZ, hG]
    have := congrFun (congrFun hMP i) j
    rw [Matrix.mul_apply] at this
    rw [this, sub_self]
  have hind := hRZ.indepFun_of_covariance_eval hcov
  have hR2 : ∀ i, MemLp (R i) 2 P := fun i => (hRZ.fst.eval (X := R) i).memLp_two
  have hWi : Integrable (fun ω => W (Z ω)) P := by
    by_contra h; exact hw.ne' (integral_undef h)
  have hWmeas : AEStronglyMeasurable (fun ω => W (Z ω)) P :=
    (hWm.comp_aemeasurable hAZ.snd.aemeasurable).aestronglyMeasurable
  ext i
  -- `𝔼[W(Z) R_i] = 𝔼[W(Z)] 𝔼[R_i]` by independence
  have hWR : ∫ ω, W (Z ω) * R i ω ∂P = (∫ ω, W (Z ω) ∂P) * ∫ ω, R i ω ∂P :=
    (hind.symm.comp hWm (measurable_pi_apply i)).integral_fun_mul_eq_mul_integral hWmeas
      (hR2 i).aestronglyMeasurable
  have h1 : ∫ ω, W (Z ω) * A ω i ∂P =
      ∫ ω, W (Z ω) * R i ω ∂P + ∑ k, M i k * ∫ ω, W (Z ω) * Z ω k ∂P := by
    have hsum : Integrable (fun ω => ∑ k, M i k * (W (Z ω) * Z ω k)) P :=
      integrable_finsetSum _ fun k _ => (hWZ k).const_mul (M i k)
    have he : (fun ω => W (Z ω) * R i ω) =
        fun ω => W (Z ω) * A ω i - ∑ k, M i k * (W (Z ω) * Z ω k) := by
      funext ω; simp only [hR, mul_sub, mul_sum]; congr 1; refine sum_congr rfl fun k _ => ?_; ring
    rw [he, integral_sub (hWA i) hsum, integral_finsetSum _ fun k _ => (hWZ k).const_mul (M i k)]
    simp only [integral_const_mul]
    ring
  have h2 : ∫ ω, A ω i ∂P = ∫ ω, R i ω ∂P + ∑ k, M i k * ∫ ω, Z ω k ∂P := by
    have hsum : Integrable (fun ω => ∑ k, M i k * Z ω k) P :=
      integrable_finsetSum _ fun k _ => ((hZ2 k).integrable one_le_two).const_mul (M i k)
    rw [hR]
    simp only
    rw [integral_sub ((hA2 i).integrable one_le_two) hsum,
      integral_finsetSum _ fun k _ => ((hZ2 k).integrable one_le_two).const_mul (M i k)]
    simp only [integral_const_mul]
    ring
  simp only [selectedShift, mulVec, dotProduct, mul_sub, sum_sub_distrib, mul_div_assoc', ← sum_div]
  have hwne : (∫ ω, W (Z ω) ∂P) ≠ 0 := hw.ne'
  rw [h1, h2, hWR]
  field_simp
  ring

/-- **Lande's multivariate response, genetic-covariance form** `Δz̄ = G P⁻¹ S`. This is
`selectedShift_breeding_eq` under the additional identification of `G` as the additive
genetic covariance `Var(A)`, as in the decomposition `Z = A + E` with `Cov(A, E) = 0`. -/
theorem selectedShift_breeding_eq_geneticCov {A Z : Ω → ι → ℝ} {G Pm : Matrix ι ι ℝ}
    {W : (ι → ℝ) → ℝ}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P)
    (hG : ∀ i j, cov[fun ω => A ω i, fun ω => Z ω j; P] = G i j)
    (_hGA : ∀ i j, cov[fun ω => A ω i, fun ω => A ω j; P] = G i j)
    (hPZ : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P] = Pm i j) (hPd : Pm.PosDef)
    (hWm : Measurable W) (hW0 : ∀ z, 0 ≤ W z) (hw : 0 < ∫ ω, W (Z ω) ∂P)
    (hWZ : ∀ j, Integrable (fun ω => W (Z ω) * Z ω j) P)
    (hWA : ∀ i, Integrable (fun ω => W (Z ω) * A ω i) P) :
    selectedShift W Z A P = (G * Pm⁻¹) *ᵥ selectedShift W Z Z P :=
  selectedShift_breeding_eq hAZ hG hPZ hPd hWm hW0 hw hWZ hWA


/-- **Univariate cross-covariance case** with coefficient `Cov(A, Z) / Var(Z)`: for jointly
Gaussian `(A, Z)`, `Var(Z) > 0`, measurable fitness weights `W(Z) ≥ 0` with
`0 < 𝔼[W(Z)]` and `W(Z) Z`, `W(Z) A` integrable. When moreover `Var(A) = Va`, this is the
breeder's equation `R = h² S` with `h² = Va / Vp` (`breeding_response_univariate_of_var`). -/
theorem breeding_response_univariate {A Z : Ω → ℝ} {Va Vp : ℝ} {W : ℝ → ℝ}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P) (hG : cov[A, Z; P] = Va) (hPZ : Var[Z; P] = Vp)
    (hVp : 0 < Vp) (hWm : Measurable W) (hW0 : ∀ z, 0 ≤ W z) (hw : 0 < ∫ ω, W (Z ω) ∂P)
    (hWZ : Integrable (fun ω => W (Z ω) * Z ω) P) (hWA : Integrable (fun ω => W (Z ω) * A ω) P) :
    (∫ ω, W (Z ω) * A ω ∂P) / (∫ ω, W (Z ω) ∂P) - ∫ ω, A ω ∂P =
      Va / Vp * ((∫ ω, W (Z ω) * Z ω ∂P) / (∫ ω, W (Z ω) ∂P) - ∫ ω, Z ω ∂P) := by
  have hprob := hAZ.isProbabilityMeasure
  have hA2 : MemLp A 2 P := hAZ.fst.memLp_two
  have hZ2 : MemLp Z 2 P := hAZ.snd.memLp_two
  set h := Va / Vp with hh
  set R : Ω → ℝ := fun ω => A ω - h * Z ω with hR
  let L : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    (LinearMap.fst ℝ ℝ ℝ - h • LinearMap.snd ℝ ℝ ℝ).prod (LinearMap.snd ℝ ℝ ℝ)
  have hRZ : HasGaussianLaw (fun ω => (R ω, Z ω)) P := by
    refine (hAZ.map_fun (LinearMap.toContinuousLinearMap L)).congr (ae_of_all _ fun ω => ?_)
    refine Prod.ext ?_ rfl
    simp [L, R]
  have hcov : cov[R, Z; P] = 0 := by
    rw [hR, covariance_fun_sub_left hA2 (hZ2.const_mul h) hZ2, covariance_const_mul_left,
      covariance_self hZ2.aemeasurable, hG, hPZ, hh]
    field_simp
    ring
  have hind := hRZ.indepFun_of_covariance_eq_zero hcov
  have hWi : Integrable (fun ω => W (Z ω)) P := by
    by_contra h; exact hw.ne' (integral_undef h)
  have hWR : ∫ ω, W (Z ω) * R ω ∂P = (∫ ω, W (Z ω) ∂P) * ∫ ω, R ω ∂P :=
    (hind.symm.comp hWm measurable_id).integral_fun_mul_eq_mul_integral
      (hWm.comp_aemeasurable hAZ.snd.aemeasurable).aestronglyMeasurable
      hRZ.fst.memLp_two.aestronglyMeasurable
  have h1 : ∫ ω, W (Z ω) * A ω ∂P = ∫ ω, W (Z ω) * R ω ∂P + h * ∫ ω, W (Z ω) * Z ω ∂P := by
    have he : (fun ω => W (Z ω) * R ω) = fun ω => W (Z ω) * A ω - h * (W (Z ω) * Z ω) := by
      funext ω; simp only [hR]; ring
    rw [he, integral_sub hWA (hWZ.const_mul h), integral_const_mul]
    ring
  have h2 : ∫ ω, A ω ∂P = ∫ ω, R ω ∂P + h * ∫ ω, Z ω ∂P := by
    rw [hR]
    simp only
    rw [integral_sub (hA2.integrable one_le_two) ((hZ2.integrable one_le_two).const_mul h),
      integral_const_mul]
    ring
  have hwne : (∫ ω, W (Z ω) ∂P) ≠ 0 := hw.ne'
  rw [h1, h2, hWR]
  field_simp
  ring

/-- **Breeder's equation** `R = h² S` with `h² = V_A / V_P`. This is the univariate
cross-covariance identity under the additional identification `Var(A) = Va`, so `Va` is
the additive genetic variance rather than only the cross-covariance `Cov(A, Z)`. -/
theorem breeding_response_univariate_of_var {A Z : Ω → ℝ} {Va Vp : ℝ} {W : ℝ → ℝ}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P) (hG : cov[A, Z; P] = Va)
    (_hVa : Var[A; P] = Va) (hPZ : Var[Z; P] = Vp)
    (hVp : 0 < Vp) (hWm : Measurable W) (hW0 : ∀ z, 0 ≤ W z) (hw : 0 < ∫ ω, W (Z ω) ∂P)
    (hWZ : Integrable (fun ω => W (Z ω) * Z ω) P) (hWA : Integrable (fun ω => W (Z ω) * A ω) P) :
    (∫ ω, W (Z ω) * A ω ∂P) / (∫ ω, W (Z ω) ∂P) - ∫ ω, A ω ∂P =
      Va / Vp * ((∫ ω, W (Z ω) * Z ω ∂P) / (∫ ω, W (Z ω) ∂P) - ∫ ω, Z ω ∂P) :=
  breeding_response_univariate hAZ hG hPZ hVp hWm hW0 hw hWZ hWA


open MathlibExt.Biology.StatisticalGenetics.SelectionGradient in
/-- **Cross-covariance gradient form** `Δz̄ = G ∇_μ log w̄(μ)`: let `(A, Z)` be jointly Gaussian
with cross-covariance `Cov(A_i, Z_j) = G_ij`, let the law of `Z` be `N(μ, P)` with `P` positive
definite, and let the fitness be bounded, measurable and nonnegative with positive mean fitness
at `μ`. Then with Atlas's mean fitness `meanFitnessMV W P` (as a function of the trait mean), the
response is the cross-covariance `G` applied to the gradient of its logarithm at `μ`. -/
theorem selectedShift_breeding_eq_gradient {A Z : Ω → ι → ℝ} {G Pm : Matrix ι ι ℝ}
    {W : EuclideanSpace ℝ ι → ℝ} {μ : EuclideanSpace ℝ ι}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P)
    (hG : ∀ i j, cov[fun ω => A ω i, fun ω => Z ω j; P] = G i j)
    (hlaw : HasLaw (fun ω => WithLp.toLp 2 (Z ω)) (multivariateGaussian μ Pm) P)
    (hPd : Pm.PosDef) (hWm : Measurable W) (hWb : ∃ C, ∀ z, |W z| ≤ C)
    (hW0 : ∀ z, 0 ≤ W z) (hw : 0 < meanFitnessMV W Pm μ) :
    selectedShift (fun z => W (WithLp.toLp 2 z)) Z A P =
      G *ᵥ ⇑(gradient (fun m => Real.log (meanFitnessMV W Pm m)) μ) := by
  obtain ⟨C, hC⟩ := hWb
  have hprob := hAZ.isProbabilityMeasure
  have hA2 : ∀ i, MemLp (fun ω => A ω i) 2 P := fun i =>
    (hAZ.fst.eval (X := fun i ω => A ω i) i).memLp_two
  have hZ2 : ∀ i, MemLp (fun ω => Z ω i) 2 P := fun i =>
    (hAZ.snd.eval (X := fun i ω => Z ω i) i).memLp_two
  have hWm' : Measurable fun z : ι → ℝ => W (WithLp.toLp 2 z) :=
    hWm.comp (PiLp.continuous_toLp 2 _).measurable
  have hZm : AEMeasurable (fun ω => WithLp.toLp 2 (Z ω)) P := hlaw.aemeasurable
  -- the law of `Z` fixes its covariance and mean
  have hPZ : ∀ i j, cov[fun ω => Z ω i, fun ω => Z ω j; P] = Pm i j := by
    intro i j
    rw [← covariance_eval_multivariateGaussian hPd.posSemidef i j (μ := μ), ← hlaw.map_eq,
      covariance_map (by fun_prop) (by fun_prop) hZm]
    rfl
  have hint : Integrable (fun x : EuclideanSpace ℝ ι => x) (multivariateGaussian μ Pm) :=
    IsGaussian.integrable_id
  have hmean : ∀ j, ∫ ω, Z ω j ∂P = μ j := by
    intro j
    have h := hlaw.integral_comp (f := fun x : EuclideanSpace ℝ ι => x j) (by fun_prop)
    rw [show (∫ x, x j ∂multivariateGaussian μ Pm) = EuclideanSpace.proj j (∫ x, x ∂multivariateGaussian μ Pm) from
      ((EuclideanSpace.proj j).integral_comp_comm hint), integral_id_multivariateGaussian] at h
    simpa using h
  have hwP : ∫ ω, W (WithLp.toLp 2 (Z ω)) ∂P = meanFitnessMV W Pm μ :=
    hlaw.integral_comp (f := W) hWm.aestronglyMeasurable
  have hbd : ∀ ω, ‖W (WithLp.toLp 2 (Z ω))‖ ≤ C := fun ω => by
    simpa [Real.norm_eq_abs] using hC _
  have hWZ : ∀ j, Integrable (fun ω => W (WithLp.toLp 2 (Z ω)) * Z ω j) P := fun j =>
    ((hZ2 j).integrable one_le_two).bdd_mul (hWm.comp_aemeasurable hZm).aestronglyMeasurable
      (ae_of_all _ hbd)
  have hWA : ∀ i, Integrable (fun ω => W (WithLp.toLp 2 (Z ω)) * A ω i) P := fun i =>
    ((hA2 i).integrable one_le_two).bdd_mul (hWm.comp_aemeasurable hZm).aestronglyMeasurable
      (ae_of_all _ hbd)
  have hcore := selectedShift_breeding_eq hAZ hG hPZ hPd hWm' (fun z => hW0 _) (by rw [hwP]; exact hw) hWZ hWA
  -- the selection differential is Atlas's `selectionDifferentialMV`
  have hmoment : Integrable (fun x => W x • (x - μ)) (multivariateGaussian μ Pm) :=
    (hint.sub (integrable_const μ)).bdd_smul C hWm.aestronglyMeasurable
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
  have hS : selectedShift (fun z => W (WithLp.toLp 2 z)) Z Z P = ⇑(selectionDifferentialMV W Pm μ) := by
    funext j
    have hj : (∫ x, W x • (x - μ) ∂multivariateGaussian μ Pm) j =
        ∫ x, W x * x j ∂multivariateGaussian μ Pm - μ j * meanFitnessMV W Pm μ := by
      have hcomm := (EuclideanSpace.proj (𝕜 := ℝ) j).integral_comp_comm hmoment
      simp only [EuclideanSpace.proj, PiLp.proj_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hcomm
      rw [← hcomm]
      have hWint : Integrable W (multivariateGaussian μ Pm) :=
        (integrable_const C).mono' hWm.aestronglyMeasurable
          (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
      have hi1 : Integrable (fun x : EuclideanSpace ℝ ι => W x * x j) (multivariateGaussian μ Pm) :=
        ((EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp hint).bdd_mul hWm.aestronglyMeasurable
          (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hC x)
      rw [show (fun x : EuclideanSpace ℝ ι => W x * (x j - μ j)) =
          fun x => W x * x j - μ j * W x from funext fun x => by ring,
        integral_sub hi1 (hWint.const_mul _), integral_const_mul]
      rfl
    have hWZj : ∫ ω, W (WithLp.toLp 2 (Z ω)) * Z ω j ∂P = ∫ x, W x * x j ∂multivariateGaussian μ Pm :=
      hlaw.integral_comp (f := fun x => W x * x j) (by fun_prop)
    simp only [selectedShift, selectionDifferentialMV, PiLp.smul_apply, smul_eq_mul, hj, hwP, hWZj,
      hmean]
    field_simp
  rw [hcore, hS, selectionDifferentialMV_eq hWm ⟨C, hC⟩ hPd hw.ne', Matrix.ofLp_toEuclideanCLM,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hPd.det_pos.ne'.isUnit,
    Matrix.mul_one]

open MathlibExt.Biology.StatisticalGenetics.SelectionGradient in
/-- **Lande gradient form, genetic-covariance version** `Δz̄ = G ∇_μ log w̄(μ)`. This is
`selectedShift_breeding_eq_gradient` under the additional identification of `G` as the
additive genetic covariance `Var(A)`. -/
theorem selectedShift_breeding_eq_gradient_geneticCov {A Z : Ω → ι → ℝ} {G Pm : Matrix ι ι ℝ}
    {W : EuclideanSpace ℝ ι → ℝ} {μ : EuclideanSpace ℝ ι}
    (hAZ : HasGaussianLaw (fun ω => (A ω, Z ω)) P)
    (hG : ∀ i j, cov[fun ω => A ω i, fun ω => Z ω j; P] = G i j)
    (_hGA : ∀ i j, cov[fun ω => A ω i, fun ω => A ω j; P] = G i j)
    (hlaw : HasLaw (fun ω => WithLp.toLp 2 (Z ω)) (multivariateGaussian μ Pm) P)
    (hPd : Pm.PosDef) (hWm : Measurable W) (hWb : ∃ C, ∀ z, |W z| ≤ C)
    (hW0 : ∀ z, 0 ≤ W z) (hw : 0 < meanFitnessMV W Pm μ) :
    selectedShift (fun z => W (WithLp.toLp 2 z)) Z A P =
      G *ᵥ ⇑(gradient (fun m => Real.log (meanFitnessMV W Pm m)) μ) :=
  selectedShift_breeding_eq_gradient hAZ hG hlaw hPd hWm hWb hW0 hw

end MathlibExt.Biology.PopulationGenetics.Classical.LandeResponse
