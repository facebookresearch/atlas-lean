/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.DeltaMethod
public import MathlibExt.Probability.Statistics.Survival.FineGrayAsymptotics
public import MathlibExt.Probability.Statistics.Survival.SimultaneousBands

/-!
# Simultaneous confidence bands for the Fine–Gray cumulative incidence function

Under the Fine–Gray proportional subdistribution hazards model with a scalar covariate, the
cumulative incidence function of the cause of interest at covariate value `x` is
`F(t; x) = 1 - exp (-exp (β x) Λ₀(t))` (`IsPropSubdistHazards.cif_eq`). On a finite grid of times
`t_j`, `j : ι`, the plug-in estimate is `F̂(t_j; x) = 1 - exp (-exp (β̂ x) Λ̂₀(t_j))`. This file
proves that a band `F̂(t_j; x) ± qhat · ŵ_j / √n` covers the whole CIF curve on the grid with
asymptotic probability `P'(max_j |Y_j| / w_j ≤ q)`, where `Y` is the delta-method image of the
joint limit of `√n (β̂ - β₀, Λ̂₀ - Λ₀)`.

## Source receipt

* **Named result:** Fine and Gray's prediction of the cumulative incidence function for a
  covariate profile, with pointwise intervals and simultaneous confidence bands based on the
  asymptotic Gaussian law of `√n (F̂(·; x) - F(·; x))`, which comes from the joint asymptotics of
  the coefficient estimator and the Breslow-type baseline estimator (J. P. Fine and R. J. Gray,
  *A proportional hazards model for the subdistribution of a competing risk*, J. Amer. Statist.
  Assoc. 94 (1999), 496–509, Section 4).
* **Formalized here:** the finite-grid version. The derivative of the CIF map is
  `hasFDerivAt_fgCif`; the grid limit of the plug-in estimator is `tendstoInDistribution_fgCif`;
  band coverage is `tendsto_coverage_fgCifBand` and its exact-level form
  `tendsto_coverage_fgCifBand_criticalValue`; the covariance of the limit (the plug-in variance)
  is `covariance_fgCifDeriv`. With the baseline known, the coefficient asymptotics of
  `FineGrayAsymptotics` (`tendstoInDistribution_fgMPLE`) give the band directly:
  `tendsto_coverage_fgCifBand_knownBaseline` and `tendsto_coverage_fgCifBand_knownBaseline_abs`.

## Main definitions

* `fgCif x b Λ`: the Fine–Gray CIF curve `j ↦ 1 - exp (-exp (b x) Λ j)` on the grid.
* `fgCifSlope x b Λ j = exp (-exp (b x) Λ j) exp (b x) = (1 - F_j) exp (b x)`.
* `fgCifDeriv x b Λ`: the derivative `(h, H) ↦ (j ↦ fgCifSlope x b Λ j · (x Λ j h + H j))` of
  `(b, Λ) ↦ fgCif x b Λ`.

## Main results

* `cif_eq_fgCif`: under proportional subdistribution hazards with a scalar covariate, the model
  CIF on the grid is `fgCif x (β 0) Λ₀` with `Λ₀ j = ∫₀^{t j} λ₀`.
* `hasFDerivAt_fgCif`: `(b, Λ) ↦ fgCif x b Λ` has Fréchet derivative `fgCifDeriv x b Λ`.
* `tendstoInDistribution_fgCif`: if `√n ((β̂ n, Λ̂ n) - (β₀, Λ₀)) ⟶ Z` then
  `√n (fgCif x (β̂ n) (Λ̂ n) - fgCif x β₀ Λ₀) ⟶ fgCifDeriv x β₀ Λ₀ Z` (delta method).
* `tendsto_coverage_fgCifBand`: with estimated weights `ŵ n → w > 0` and critical values
  `qhat n → q` in probability, and no atom of the limiting weighted sup at `q`, the probability that
  the band covers the CIF at every grid point tends to `P'(weightedSup w Y ≤ q)`.
* `tendsto_coverage_fgCifBand_criticalValue`: with an atomless limiting weighted sup and
  `qhat n` tending to its `(1 - α)`-quantile, coverage tends to `1 - α`.
* `hasGaussianLaw_fgCifDeriv`, `covariance_fgCifDeriv`: a Gaussian joint limit gives a Gaussian
  CIF limit, with covariance
  `s_i s_j (x²Λ_iΛ_j Var Zβ + xΛ_i Cov(Zβ, ZΛ_j) + xΛ_j Cov(ZΛ_i, Zβ) + Cov(ZΛ_i, ZΛ_j))`.
* `tendsto_coverage_fgCifBand_knownBaseline`: from `FineGrayConditions` alone, with the
  baseline `Λ₀` known, the band around `fgCif x (β̂ n) Λ₀` has limiting coverage
  `P'(weightedSup w (j ↦ s_j x Λ₀_j · Z / v) ≤ q)`.
* `tendsto_coverage_fgCifBand_knownBaseline_abs`: with the weights `|s_j x Λ₀_j|` the limit is
  `P'(|Z / v| ≤ q)`: a rank-one limit, so the simultaneous band costs nothing over a pointwise
  interval (`SimultaneousBands.measure_weightedSup_le_eq_of_proportional`).

## Scope

Finite grid, scalar covariate. The baseline estimator (Breslow-type, with censoring weights) is
not defined here, and the joint limit of `√n (β̂ - β₀, Λ̂₀ - Λ₀)` is a hypothesis of the general
theorems; only its coefficient part follows from `FineGrayAsymptotics`. The known-baseline
corollaries need no such hypothesis. No convergence in `D[0, τ]`; absence of atoms of the limiting
weighted sup at the critical value is a hypothesis; no consistent estimator of the limit
covariance is constructed.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.FineGrayBands

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.FineGrayAsymptotics
open MathlibExt.Probability.Statistics.SimultaneousBands

variable {ι : Type*}

/-! ### The CIF map and its derivative -/

/-- The **Fine–Gray cumulative incidence curve** on the grid `ι` at the scalar covariate value
`x`, for coefficient `b` and baseline cumulative subdistribution hazard values `Λ j = Λ₀(t_j)`:
`j ↦ 1 - exp (-exp (b x) Λ j)`. -/
noncomputable def fgCif (x b : ℝ) (Λ : ι → ℝ) : ι → ℝ :=
  fun j => 1 - Real.exp (-(Real.exp (b * x) * Λ j))

/-- The factor `exp (-exp (b x) Λ j) · exp (b x)`, i.e. `(1 - F_j) exp (b x)`, common to both
partial derivatives of the `j`-th CIF value. -/
noncomputable def fgCifSlope (x b : ℝ) (Λ : ι → ℝ) (j : ι) : ℝ :=
  Real.exp (-(Real.exp (b * x) * Λ j)) * Real.exp (b * x)

/-- The **derivative of the CIF map** `(b, Λ) ↦ fgCif x b Λ` at `(b, Λ)`:
`(h, H) ↦ (j ↦ fgCifSlope x b Λ j · (x Λ j h + H j))`. -/
noncomputable def fgCifDeriv (x b : ℝ) (Λ : ι → ℝ) : ℝ × (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun j => fgCifSlope x b Λ j •
    ((x * Λ j) • ContinuousLinearMap.fst ℝ ℝ (ι → ℝ) +
      (ContinuousLinearMap.proj (R := ℝ) j).comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)))

theorem fgCifDeriv_apply (x b : ℝ) (Λ : ι → ℝ) (p : ℝ × (ι → ℝ)) (j : ι) :
    fgCifDeriv x b Λ p j = fgCifSlope x b Λ j * (x * Λ j * p.1 + p.2 j) := by
  simp [fgCifDeriv, smul_eq_mul, mul_add]

theorem fgCifSlope_pos (x b : ℝ) (Λ : ι → ℝ) (j : ι) : 0 < fgCifSlope x b Λ j :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

/-- `fgCifSlope` is `(1 - F_j) exp (b x)`. -/
theorem fgCifSlope_eq (x b : ℝ) (Λ : ι → ℝ) (j : ι) :
    fgCifSlope x b Λ j = (1 - fgCif x b Λ j) * Real.exp (b * x) := by
  simp [fgCifSlope, fgCif]

/-- The CIF map is continuous in `(b, Λ)`. -/
theorem continuous_fgCif (x : ℝ) : Continuous fun p : ℝ × (ι → ℝ) => fgCif x p.1 p.2 :=
  continuous_pi fun j => by unfold fgCif; fun_prop

/-- **The CIF map is differentiable**: `(b, Λ) ↦ fgCif x b Λ` has Fréchet derivative
`fgCifDeriv x b Λ` at `(b, Λ)`. -/
theorem hasFDerivAt_fgCif [Finite ι] (x b : ℝ) (Λ : ι → ℝ) :
    HasFDerivAt (fun p : ℝ × (ι → ℝ) => fgCif x p.1 p.2) (fgCifDeriv x b Λ) (b, Λ) := by
  cases nonempty_fintype ι
  unfold fgCifDeriv
  refine hasFDerivAt_pi.2 fun j => ?_
  have h1 : HasFDerivAt (fun p : ℝ × (ι → ℝ) => p.1 * x)
      (x • ContinuousLinearMap.fst ℝ ℝ (ι → ℝ)) (b, Λ) := hasFDerivAt_fst.mul_const x
  have h3 : HasFDerivAt (fun p : ℝ × (ι → ℝ) => p.2 j)
      ((ContinuousLinearMap.proj (R := ℝ) j).comp (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ)))
      (b, Λ) :=
    ((ContinuousLinearMap.proj (R := ℝ) j).comp
      (ContinuousLinearMap.snd ℝ ℝ (ι → ℝ))).hasFDerivAt
  have h4 := ((h1.exp.mul h3).neg.exp).const_sub 1
  refine h4.congr_fderiv (ContinuousLinearMap.ext fun p => ?_)
  simp [fgCifSlope, smul_eq_mul]
  ring

/-! ### The grid limit and band coverage -/

section Asymptotic

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- **Delta method for the Fine–Gray CIF on a grid.** If the coefficient and baseline estimators
satisfy `√n ((β̂ n, Λ̂ n) - (β₀, Λ₀)) ⟶ Z` jointly, the plug-in CIF estimator satisfies
`√n (fgCif x (β̂ n) (Λ̂ n) - fgCif x β₀ Λ₀) ⟶ fgCifDeriv x β₀ Λ₀ Z`. -/
theorem tendstoInDistribution_fgCif [Finite ι] (x : ℝ) {βhat : ℕ → Ω → ℝ}
    {Λhat : ℕ → Ω → ι → ℝ} {β₀ : ℝ} {Λ₀ : ι → ℝ} {Z : Ω' → ℝ × (ι → ℝ)}
    (hZ : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • ((βhat n ω, Λhat n ω) - (β₀, Λ₀))) atTop Z (fun _ => P) P')
    (hβm : ∀ n, AEMeasurable (βhat n) P) (hΛm : ∀ n, AEMeasurable (Λhat n) P) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (fgCif x (βhat n ω) (Λhat n ω) - fgCif x β₀ Λ₀)) atTop
      (fun ω => fgCifDeriv x β₀ Λ₀ (Z ω)) (fun _ => P) P' := by
  cases nonempty_fintype ι
  exact hZ.delta_method (X := fun n ω => (βhat n ω, Λhat n ω)) (θ := (β₀, Λ₀))
    (g := fun p : ℝ × (ι → ℝ) => fgCif x p.1 p.2)
    (tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) (hasFDerivAt_fgCif x β₀ Λ₀)
    (fun n => (hβm n).prodMk (hΛm n))
    (fun n => (continuous_fgCif x).measurable.comp_aemeasurable ((hβm n).prodMk (hΛm n)))

/-- **Asymptotic coverage of the Fine–Gray CIF band.** Under the joint limit
`√n ((β̂ n, Λ̂ n) - (β₀, Λ₀)) ⟶ Z`, with estimated weights `ŵ n → w > 0` and estimated critical
values `qhat n → q` in probability, if the limiting weighted sup of `Y = fgCifDeriv x β₀ Λ₀ Z`
has no atom at `q`, the band `fgCif x (β̂ n) (Λ̂ n) ± qhat n · ŵ n / √n` covers the CIF curve
`fgCif x β₀ Λ₀` at every grid point with probability tending to `P'(weightedSup w Y ≤ q)`. -/
theorem tendsto_coverage_fgCifBand [Fintype ι] [Nonempty ι] (x : ℝ) {βhat : ℕ → Ω → ℝ}
    {Λhat : ℕ → Ω → ι → ℝ} {β₀ : ℝ} {Λ₀ : ι → ℝ} {Z : Ω' → ℝ × (ι → ℝ)}
    (hZ : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • ((βhat n ω, Λhat n ω) - (β₀, Λ₀))) atTop Z (fun _ => P) P')
    (hβm : ∀ n, AEMeasurable (βhat n) P) (hΛm : ∀ n, AEMeasurable (Λhat n) P)
    {ŵ : ℕ → Ω → ι → ℝ} {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    (hŵ : TendstoInMeasure P ŵ atTop (fun _ => w)) (hŵm : ∀ n, AEMeasurable (ŵ n) P)
    {qhat : ℕ → Ω → ℝ} {q : ℝ} (hqhat : TendstoInMeasure P qhat atTop (fun _ => q))
    (hqhatm : ∀ n, AEMeasurable (qhat n) P)
    (hatom : P' {ω | weightedSup w (fgCifDeriv x β₀ Λ₀ (Z ω)) = q} = 0) :
    Tendsto (fun n => P {ω | fgCif x β₀ Λ₀ ∈
        simultaneousBand (fgCif x (βhat n ω) (Λhat n ω)) (ŵ n ω) (qhat n ω) n}) atTop
      (𝓝 (P' {ω | weightedSup w (fgCifDeriv x β₀ Λ₀ (Z ω)) ≤ q})) :=
  tendsto_coverage_simultaneousBand (tendstoInDistribution_fgCif x hZ hβm hΛm) hw hŵ hŵm hqhat
    hqhatm hatom

/-- **Asymptotically exact coverage of the Fine–Gray CIF band.** Under the hypotheses of
`tendsto_coverage_fgCifBand`, if the limiting weighted sup has an atomless law and `qhat n`
converges in probability to its level-`(1 - α)` critical value, the coverage tends to `1 - α`. -/
theorem tendsto_coverage_fgCifBand_criticalValue [Fintype ι] [Nonempty ι] (x : ℝ)
    {βhat : ℕ → Ω → ℝ} {Λhat : ℕ → Ω → ι → ℝ} {β₀ : ℝ} {Λ₀ : ι → ℝ} {Z : Ω' → ℝ × (ι → ℝ)}
    (hZ : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • ((βhat n ω, Λhat n ω) - (β₀, Λ₀))) atTop Z (fun _ => P) P')
    (hβm : ∀ n, AEMeasurable (βhat n) P) (hΛm : ∀ n, AEMeasurable (Λhat n) P)
    {ŵ : ℕ → Ω → ι → ℝ} {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    (hŵ : TendstoInMeasure P ŵ atTop (fun _ => w)) (hŵm : ∀ n, AEMeasurable (ŵ n) P)
    {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1)
    (hatom : ∀ y, P' {ω | weightedSup w (fgCifDeriv x β₀ Λ₀ (Z ω)) = y} = 0)
    {qhat : ℕ → Ω → ℝ}
    (hqhat : TendstoInMeasure P qhat atTop
      (fun _ => criticalValue (P'.map fun ω => weightedSup w (fgCifDeriv x β₀ Λ₀ (Z ω))) α))
    (hqhatm : ∀ n, AEMeasurable (qhat n) P) :
    Tendsto (fun n => P {ω | fgCif x β₀ Λ₀ ∈
        simultaneousBand (fgCif x (βhat n ω) (Λhat n ω)) (ŵ n ω) (qhat n ω) n}) atTop
      (𝓝 (ENNReal.ofReal (1 - α))) :=
  tendsto_coverage_simultaneousBand_criticalValue (tendstoInDistribution_fgCif x hZ hβm hΛm) hw
    hŵ hŵm hα hatom hqhat hqhatm

end Asymptotic

/-! ### The Gaussian limit -/

section Gaussian

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}

/-- A Gaussian joint limit gives a Gaussian CIF grid limit. -/
theorem hasGaussianLaw_fgCifDeriv [Finite ι] (x b : ℝ) (Λ : ι → ℝ) {Z : Ω' → ℝ × (ι → ℝ)}
    (hZ : HasGaussianLaw Z P') : HasGaussianLaw (fun ω => fgCifDeriv x b Λ (Z ω)) P' := by
  cases nonempty_fintype ι
  exact hZ.map_fun (fgCifDeriv x b Λ)

/-- **Covariance of the CIF grid limit** (the plug-in variance): with `s = fgCifSlope x b Λ`,
`Zβ = (Z ·).1` and `ZΛ_j = (Z ·).2 j` square integrable,
`Cov(Y_i, Y_j) = s_i s_j (xΛ_i xΛ_j Var Zβ + xΛ_i Cov(Zβ, ZΛ_j) + xΛ_j Cov(ZΛ_i, Zβ)
+ Cov(ZΛ_i, ZΛ_j))` for `Y = fgCifDeriv x b Λ Z`. -/
theorem covariance_fgCifDeriv [IsFiniteMeasure P'] (x b : ℝ) (Λ : ι → ℝ)
    {Z : Ω' → ℝ × (ι → ℝ)} (hβ : MemLp (fun ω => (Z ω).1) 2 P')
    (hΛ : ∀ j, MemLp (fun ω => (Z ω).2 j) 2 P') (i j : ι) :
    cov[fun ω => fgCifDeriv x b Λ (Z ω) i, fun ω => fgCifDeriv x b Λ (Z ω) j; P'] =
      fgCifSlope x b Λ i * fgCifSlope x b Λ j *
        (x * Λ i * (x * Λ j) * cov[fun ω => (Z ω).1, fun ω => (Z ω).1; P'] +
          x * Λ i * cov[fun ω => (Z ω).1, fun ω => (Z ω).2 j; P'] +
          x * Λ j * cov[fun ω => (Z ω).2 i, fun ω => (Z ω).1; P'] +
          cov[fun ω => (Z ω).2 i, fun ω => (Z ω).2 j; P']) := by
  have key : cov[(fun ω => x * Λ i * (Z ω).1) + (fun ω => (Z ω).2 i),
      (fun ω => x * Λ j * (Z ω).1) + (fun ω => (Z ω).2 j); P'] =
        x * Λ i * (x * Λ j) * cov[fun ω => (Z ω).1, fun ω => (Z ω).1; P'] +
          x * Λ i * cov[fun ω => (Z ω).1, fun ω => (Z ω).2 j; P'] +
          x * Λ j * cov[fun ω => (Z ω).2 i, fun ω => (Z ω).1; P'] +
          cov[fun ω => (Z ω).2 i, fun ω => (Z ω).2 j; P'] := by
    rw [covariance_add_left (hβ.const_mul (x * Λ i)) (hΛ i)
        ((hβ.const_mul (x * Λ j)).add (hΛ j)),
      covariance_add_right (hβ.const_mul (x * Λ i)) (hβ.const_mul (x * Λ j)) (hΛ j),
      covariance_add_right (hΛ i) (hβ.const_mul (x * Λ j)) (hΛ j),
      covariance_const_mul_left, covariance_const_mul_right, covariance_const_mul_left,
      covariance_const_mul_right]
    ring
  have e : ∀ l, (fun ω => fgCifDeriv x b Λ (Z ω) l) = fun ω =>
      fgCifSlope x b Λ l * ((fun ω => x * Λ l * (Z ω).1) + (fun ω => (Z ω).2 l)) ω :=
    fun l => funext fun ω => by rw [fgCifDeriv_apply, Pi.add_apply]
  rw [e i, e j, covariance_const_mul_left, covariance_const_mul_right, key]
  ring

end Gaussian

/-! ### Known baseline: the band from the coefficient asymptotics -/

/-- On a rank-one limit `j ↦ g j · t` with nonzero `g`, the weighted sup with weights `|g|` is
`|t|`. -/
theorem weightedSup_abs_mul [Fintype ι] [Nonempty ι] {g : ι → ℝ} (hg : ∀ j, g j ≠ 0) (t : ℝ) :
    weightedSup (fun j => |g j|) (fun j => g j * t) = |t| := by
  have h : ∀ j, ‖g j * t / |g j|‖ = |t| := fun j => by
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_abs,
      mul_div_cancel_left₀ _ (abs_ne_zero.2 (hg j))]
  change ‖fun j => g j * t / |g j|‖ = |t|
  obtain ⟨j₀⟩ := ‹Nonempty ι›
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg t)).2 fun j => (h j).le) ?_
  exact (h j₀).symm.le.trans (norm_le_pi_norm (fun j => g j * t / |g j|) j₀)

/-- The derivative applied to a pure coefficient perturbation `(t, 0)`. -/
theorem fgCifDeriv_mk_zero (x b : ℝ) (Λ : ι → ℝ) (t : ℝ) :
    fgCifDeriv x b Λ (t, 0) = fun j => fgCifSlope x b Λ j * (x * Λ j) * t := by
  funext j
  rw [fgCifDeriv_apply]
  simp only [Pi.zero_apply, add_zero]
  ring

section KnownBaseline

variable {Ω Ω' κ : Type*} [DecidableEq κ] {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : (n : ℕ) → Ω → Fin n → ℝ} {ε : (n : ℕ) → Ω → Fin n → Option κ} {c : κ}
  {G : ℕ → Ω → ℝ → ℝ} {z : (n : ℕ) → Ω → Fin n → ℝ} {β₀ r : ℝ} {i : ℝ → ℝ} {v : NNReal}
  {Z : Ω' → ℝ} {βhat : ℕ → Ω → ℝ}

/-- **Fine–Gray CIF band with a known baseline.** Under
`FineGrayConditions` (score limit `Z`, information limit `v`), let `βhat n` maximize the weighted
Fine–Gray log partial likelihood whenever a maximizer exists. With the baseline values `Λ₀` known,
the band `fgCif x (βhat n) Λ₀ ± qhat n · ŵ n / √n` covers `fgCif x β₀ Λ₀` at every grid point with
probability tending to `P'(weightedSup w (j ↦ s_j x Λ₀_j · Z / v) ≤ q)`,
`s = fgCifSlope x β₀ Λ₀`, provided that limit has no atom at `q`. -/
theorem tendsto_coverage_fgCifBand_knownBaseline [Fintype ι] [Nonempty ι]
    (h : FineGrayConditions P P' X ε c G z β₀ r i v Z)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ
          (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P) (x : ℝ) (Λ₀ : ι → ℝ)
    {ŵ : ℕ → Ω → ι → ℝ} {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    (hŵ : TendstoInMeasure P ŵ atTop (fun _ => w)) (hŵm : ∀ n, AEMeasurable (ŵ n) P)
    {qhat : ℕ → Ω → ℝ} {q : ℝ} (hqhat : TendstoInMeasure P qhat atTop (fun _ => q))
    (hqhatm : ∀ n, AEMeasurable (qhat n) P)
    (hatom : P' {ω | weightedSup w
      (fun j => fgCifSlope x β₀ Λ₀ j * (x * Λ₀ j) * (Z ω / v)) = q} = 0) :
    Tendsto (fun n => P {ω | fgCif x β₀ Λ₀ ∈
        simultaneousBand (fgCif x (βhat n ω) Λ₀) (ŵ n ω) (qhat n ω) n}) atTop
      (𝓝 (P' {ω | weightedSup w
        (fun j => fgCifSlope x β₀ Λ₀ j * (x * Λ₀ j) * (Z ω / v)) ≤ q})) := by
  have hβ := tendstoInDistribution_fgMPLE h hβhat hβhat_meas
  have hfun : (fun (n : ℕ) ω => √(n : ℝ) • ((βhat n ω, Λ₀) - (β₀, Λ₀))) =
      fun (n : ℕ) ω => (√(n : ℝ) * (βhat n ω - β₀), (0 : ι → ℝ)) := by
    funext n ω
    simp [Prod.smul_mk]
  have hJ : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • ((βhat n ω, Λ₀) - (β₀, Λ₀))) atTop
      (fun ω => (Z ω / (v : ℝ), (0 : ι → ℝ))) (fun _ => P) P' := by
    rw [hfun]
    exact hβ.continuous_comp (g := fun t : ℝ => (t, (0 : ι → ℝ))) (by fun_prop)
  have key := tendsto_coverage_fgCifBand (Λhat := fun _ _ => Λ₀) x hJ hβhat_meas
    (fun _ => aemeasurable_const) hw hŵ hŵm hqhat hqhatm
    (by simpa only [fgCifDeriv_mk_zero] using hatom)
  simpa only [fgCifDeriv_mk_zero] using key

/-- **Known-baseline band with the natural weights: simultaneous costs nothing over pointwise.**
Under the hypotheses of `tendsto_coverage_fgCifBand_knownBaseline` with `x ≠ 0`, `Λ₀ j ≠ 0` and
estimated weights converging to `|s_j x Λ₀_j|`, the limiting coverage is `P'(|Z / v| ≤ q)`, the
same as the limiting coverage of a single pointwise interval: the grid limit is rank one. -/
theorem tendsto_coverage_fgCifBand_knownBaseline_abs [Fintype ι] [Nonempty ι]
    (h : FineGrayConditions P P' X ε c G z β₀ r i v Z)
    (hβhat : ∀ n ω,
      (∃ b, IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ b) →
        IsMaxOn (fgLogPartialLikelihood₁ (X n ω) (ε n ω) c (G n ω) (z n ω)) Set.univ
          (βhat n ω))
    (hβhat_meas : ∀ n, AEMeasurable (βhat n) P) {x : ℝ} (hx : x ≠ 0) {Λ₀ : ι → ℝ}
    (hΛ₀ : ∀ j, Λ₀ j ≠ 0) {ŵ : ℕ → Ω → ι → ℝ}
    (hŵ : TendstoInMeasure P ŵ atTop (fun _ j => |fgCifSlope x β₀ Λ₀ j * (x * Λ₀ j)|))
    (hŵm : ∀ n, AEMeasurable (ŵ n) P)
    {qhat : ℕ → Ω → ℝ} {q : ℝ} (hqhat : TendstoInMeasure P qhat atTop (fun _ => q))
    (hqhatm : ∀ n, AEMeasurable (qhat n) P) (hatom : P' {ω | |Z ω / v| = q} = 0) :
    Tendsto (fun n => P {ω | fgCif x β₀ Λ₀ ∈
        simultaneousBand (fgCif x (βhat n ω) Λ₀) (ŵ n ω) (qhat n ω) n}) atTop
      (𝓝 (P' {ω | |Z ω / v| ≤ q})) := by
  have hg : ∀ j, fgCifSlope x β₀ Λ₀ j * (x * Λ₀ j) ≠ 0 := fun j =>
    mul_ne_zero (fgCifSlope_pos x β₀ Λ₀ j).ne' (mul_ne_zero hx (hΛ₀ j))
  have hsup : ∀ t : ℝ, weightedSup (fun j => |fgCifSlope x β₀ Λ₀ j * (x * Λ₀ j)|)
      (fun j => fgCifSlope x β₀ Λ₀ j * (x * Λ₀ j) * t) = |t| :=
    weightedSup_abs_mul hg
  have key := tendsto_coverage_fgCifBand_knownBaseline h hβhat hβhat_meas x Λ₀
    (fun j => abs_pos.2 (hg j)) hŵ hŵm hqhat hqhatm (by simpa only [hsup] using hatom)
  simpa only [hsup] using key

end KnownBaseline

/-! ### Link to the proportional subdistribution hazards model -/

section Model

variable {Ω κ : Type*} [MeasurableSpace Ω] {P : (Fin 1 → ℝ) → Measure Ω} {T : Ω → ℝ}
  {J : Ω → κ} {c : κ} {hazard₀ : ℝ → ℝ} {β : Fin 1 → ℝ}

/-- **`fgCif` is the model CIF.** Under proportional subdistribution hazards with a scalar
covariate, the cumulative incidence function of cause `c` at covariate value `x` and grid times
`t j ≥ 0` is `fgCif x (β 0) Λ₀` with `Λ₀ j = ∫₀^{t j} λ₀`, under the regularity hypotheses of
`IsPropSubdistHazards.cif_eq` at every grid time. -/
theorem cif_eq_fgCif (h : IsPropSubdistHazards P T J c hazard₀ β)
    (hT : Measurable T) (hJ : MeasurableSet {ω | J ω = c}) (x : ℝ)
    [IsProbabilityMeasure (P fun _ => x)] (hpos : ∀ᵐ ω ∂P fun _ => x, 0 < T ω) (t : ι → ℝ)
    (ht : ∀ j, 0 ≤ t j) (f : ι → ℝ → ℝ)
    (hc : ∀ j, ContinuousOn (cif (P fun _ => x) T J c) (Icc 0 (t j)))
    (hd : ∀ j, ∀ s ∈ Ioo 0 (t j), HasDerivAt (cif (P fun _ => x) T J c) (f j s) s)
    (hf : ∀ j, IntervalIntegrable (f j) volume 0 (t j))
    (hlt : ∀ j, cif (P fun _ => x) T J c (t j) < 1) :
    (fun j => cif (P fun _ => x) T J c (t j)) =
      fgCif x (β 0) (fun j => ∫ s in (0 : ℝ)..t j, hazard₀ s) := by
  funext j
  rw [h.cif_eq hT hJ _ hpos (ht j) (hc j) (hd j) (hf j) (hlt j), fgCif]
  simp [dotProduct]

end Model

end MathlibExt.Probability.Statistics.FineGrayBands
