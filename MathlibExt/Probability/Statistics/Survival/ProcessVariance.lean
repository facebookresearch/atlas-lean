/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import MathlibExt.Probability.Statistics.Survival.StochasticIntegral

/-!
# Conditional square sums of the scaled Nelson–Aalen process

For the scaled Nelson–Aalen process `√n (Â - Λ*)`, this file proves that its conditional square
sums `∑_{i < k} E[(Δ √n (Â - Λ*))² | ℱ_i]` (`predictableQuadraticVariation`) at time `t` satisfy

`∑ E[(Δ √n (Â - Λ*))² | ℱ] → ∫_{(0, t]} dΛ / y` in probability,

where `y` is the limiting at-risk fraction, from the T45 stochastic-integral representation
`Â - Λ* = Y⁻¹ • M` (`nelsonAalenProcess_sub_restrictedHazard`), a law of large numbers for
`Y / n`, and the conditional second moment `E[(ΔM)² | ℱ] = Y ΔΛ (1 - ΔΛ)` of `M = N - ∫ Y dα`.

These are results about arbitrary conditional square sums: `N` is any real process, and `M` is not
assumed to be a martingale, so the second-moment hypothesis does not make the sums variances. When
`M` is a martingale, `martingale_nelsonAalenProcess_sub` makes `Â - Λ*`, hence `√n (Â - Λ*)`, a
martingale; the hypothesis is then the binomial conditional variance, and the sums are the
predictable variation `⟨√n (Â - Λ*)⟩`, whose convergence is the variance condition of the martingale
central limit theorem for the Nelson–Aalen estimator (Rebolledo's theorem).

## Main results

* `predictableQuadraticVariation_naScaledProcess` (exact, per `n`): under the conditional second
  moment `E[(ΔM)² | ℱ] = Y ΔΛ (1 - ΔΛ)`, the conditional square sum of `√n (Â - Λ*)` up to step `k`
  is `n ∑_{i < k} Y_{i+1}⁻¹ ΔΛ_{i+1} (1 - ΔΛ_{i+1})` a.e. (`naVarianceSum`). Proof:
  the square-sum identity for `H • M` (`predictableQuadraticVariation_stochasticIntegral`).
* `condExp_sq_increment_of_hasUnitJumps`: for a single subject (unit jumps, `Y ∈ {0, 1}`) whose
  `N - ∫ Y dα` is a martingale, the second-moment hypothesis is *derived*, as the binomial
  conditional variance, from T45's `⟨N - A⟩ = ∑ ΔA (1 - ΔA)`.
* `abs_naVarianceSum_sub_le`, `tendstoInMeasure_naVarianceSum` (law of large numbers): if
  `Y / n → ȳ ≥ ε > 0` uniformly over the grid in probability and the hazard increments are
  uniformly small, the variance sums converge in probability to the limit of the
  Riemann–Stieltjes sums `∑ ΔΛ / ȳ`.
* `tendsto_gridSum_integral` (grid limit): for a continuous cumulative hazard `Λ` and `y`
  continuous and `≥ ε > 0` on `[0, τ]`, the right-endpoint sums on the grid of mesh `τ / K n`
  converge to `∫_{(0, t]} (y s)⁻¹ dΛ(s)`; `eventually_gridHazard_increment_le` gives the mesh
  condition.
* `tendstoInMeasure_predictableQuadraticVariation_naScaledProcess` (array form, grid limit as a
  hypothesis) and **`tendstoInMeasure_predictableQuadraticVariation_naScaledProcess_integral`**
  (the conditional square sums of `√n (Â - Λ*)` at `t` converge to `∫_0^t dΛ / y`, grid limit
  proved).

## Boundary cases

* **Hazard jumps.** On a grid the square sum carries the factor `1 - ΔΛ`
  (`⟨M⟩ = ∫ (1 - ΔΛ) dΛ` for one subject); it disappears in the limit only because `Λ` is
  continuous, through the mesh condition. With a discrete hazard the limit is not `∫ dΛ / y`.
* **Vanishing risk.** Steps with `Y = 0` contribute `0` (totalized inverse, the indicator
  `J = 1{Y ≠ 0}`), which is why the process is `Â - Λ*` with the restricted hazard `Λ*`. The
  LLN hypothesis with `ȳ ≥ ε > 0` makes such steps asymptotically negligible: on the LLN event
  `Y ≥ n ε / 2 > 0`.
* **Support.** `y ≥ ε > 0` on `[0, τ]` is the supported-horizon condition; without it `∫ dΛ / y`
  can be infinite.

## What is assumed, and what is not claimed

* **Time is discrete**, as in T45: a deterministic grid of mesh `τ / K n → 0` and a deterministic
  cumulative hazard. The continuous-time Doob–Meyer compensator is not used.
* **The martingale property is not assumed.** `hcv` fixes the conditional second moments of the
  increments of `M = N - ∫ Y dα`, not their conditional means, and `N` is an arbitrary real
  process (not assumed to be a counting process), so for general `N` the sums are not variances.
  The test module applies the headline theorem to deterministic increments that are not a
  martingale.
* **The conditional second moment of the increments is a hypothesis** (`hcv`, binomial form: for a
  martingale `M` it says that the `Y` subjects at risk fail independently with probability `ΔΛ`).
  It is derived here only for a single subject (`condExp_sq_increment_of_hasUnitJumps`); for `n`
  subjects it needs conditional independence, not formalized.
* **The law of large numbers for `Y / n` is a hypothesis** (`hLLN`, uniform over the grid points up
  to `t`); its Glivenko–Cantelli proof from i.i.d. censored data is not given here.
* **The martingale CLT itself is not proved.** For a martingale `M`, this file supplies the kind of
  variance condition that `hQV` of `MathlibExt.Probability.Martingale.MartingaleTightness` assumes,
  but not in that form: `hQV` uses the grid `⌊n t⌋` on `[0, 1]` with limit `t`, so a time change
  normalizing `σ²` to `t` would be needed. The T57 Nelson–Aalen process limit (PR #1536, not
  imported) assumes the identification as part of `hfdd`.

## Source receipt (reuse search, 2026-11-12)

Named theorem (the martingale case): the variance condition
`⟨M^{(n)}⟩(t) →ᴾ σ²(t) = ∫_0^t dΛ / y` in the proof of the Nelson–Aalen central limit theorem,
Andersen–Borgan–Gill–Keiding (1993), §IV.1 "The Nelson–Aalen estimator" (via Rebolledo's martingale
CLT, §II.5 "Limit Theory").

Reused, not redefined: `stochasticIntegral`, `nelsonAalenProcess`, `restrictedHazard`,
`aalenCompensator`, `nelsonAalenProcess_sub_restrictedHazard`,
`predictableQuadraticVariation_stochasticIntegral`, `isStronglyPredictable_inv`,
`HasUnitJumps.predictableQuadraticVariation_martingalePart`, `predictablePart_eq_aalenCompensator`
(T45, `MathlibExt.Probability.Statistics.Survival.StochasticIntegral`);
`predictableQuadraticVariation` (`MathlibExt.Probability.DoobLpInequality`); Mathlib's
`TendstoInMeasure`, `StieltjesFunction.measure`, `intervalIntegral.sum_integral_adjacent_intervals`,
`IsCompact.uniformContinuousOn_of_continuous`. No existing Mathlib/MathlibExt/CSLibExt/WantedExt
declaration states this identification; T57's `ProcessAsymptotics` (unmerged) takes it as a
hypothesis. New here: `naScaledProcess`, `naVarianceSum`, `gridHazard`, `gridIndex`.

## References

* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), §II.5 (Rebolledo's theorem), §IV.1 (the Nelson–Aalen estimator).
* R. Rebolledo, *Central limit theorems for local martingales*, Z. Wahrsch. Verw. Gebiete 51
  (1980), 269–286.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.ProcessVariance

open MeasureTheory Finset Filter Topology
open MathlibExt.Probability.Statistics.CountingProcess

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### Conditional square sums of the scaled Nelson–Aalen process -/

/-- The **scaled Nelson–Aalen process** `√n (Â - Λ*)`, with `Â = nelsonAalenProcess N Y` and
`Λ* = restrictedHazard Y α` the cumulative hazard restricted to the risk set. It is a martingale
when `N - ∫ Y dα` is one (`martingale_nelsonAalenProcess_sub`); nothing in this file assumes
that. -/
noncomputable def naScaledProcess (n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt n * (nelsonAalenProcess N Y k ω - restrictedHazard Y α k ω)

/-- The closed form `n ∑_{i < k} Y_{i+1}⁻¹ Δα_{i+1} (1 - Δα_{i+1})` of the conditional square sum of
`√n (Â - Λ*)` under the binomial second-moment hypothesis (for a martingale, the binomial
grouped-data variance); `Y⁻¹` is the totalized inverse, so steps with an empty risk set contribute
`0` (the indicator `J = 1{Y ≠ 0}`). -/
noncomputable def naVarianceSum (n : ℕ) (Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ range k, (n : ℝ) * (Y (i + 1) ω)⁻¹ * (α (i + 1) - α i) * (1 - (α (i + 1) - α i))

/-- The T45 representation, scaled: `√n (Â - Λ*) = (√n Y⁻¹) • M` with `M = N - ∫ Y dα`. -/
theorem naScaledProcess_eq_stochasticIntegral (n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) :
    naScaledProcess n N Y α = stochasticIntegral (fun k ω => Real.sqrt n * (Y k ω)⁻¹)
      (fun k ω => N k ω - aalenCompensator Y α k ω) := by
  funext k ω
  rw [naScaledProcess, nelsonAalenProcess_sub_restrictedHazard]
  simp only [stochasticIntegral, mul_sum]
  exact sum_congr rfl fun _ _ => by ring

private lemma sq_inv_mul_self (y : ℝ) : (y⁻¹) ^ 2 * y = y⁻¹ := by
  rcases eq_or_ne y 0 with h | h
  · simp [h]
  · field_simp

/-- The square-sum identity for `H • M` (`predictableQuadraticVariation_stochasticIntegral`),
localized: at step `n` it needs the integrability hypotheses only for the steps `k < n`. -/
private lemma predictableQuadraticVariation_stochasticIntegral_of_lt {H M : ℕ → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H) {n : ℕ}
    (hint : ∀ k < n, Integrable (fun ω => H (k + 1) ω ^ 2 * (M (k + 1) ω - M k ω) ^ 2) μ)
    (hint' : ∀ k < n, Integrable (fun ω => (M (k + 1) ω - M k ω) ^ 2) μ) :
    predictableQuadraticVariation μ ℱ (stochasticIntegral H M) n =ᵐ[μ]
      stochasticIntegral (fun k ω => H k ω ^ 2) (predictableQuadraticVariation μ ℱ M) n := by
  have hk : ∀ k, ∀ᵐ ω ∂μ, k < n →
      μ[(fun ω => (H (k + 1) ω * (M (k + 1) ω - M k ω)) ^ 2) | ℱ k] ω =
        H (k + 1) ω ^ 2 * μ[(fun ω => (M (k + 1) ω - M k ω) ^ 2) | ℱ k] ω := by
    intro k
    by_cases hkn : k < n
    · have heq : (fun ω => (H (k + 1) ω * (M (k + 1) ω - M k ω)) ^ 2) =
          (fun ω => H (k + 1) ω ^ 2) * fun ω => (M (k + 1) ω - M k ω) ^ 2 := by
        funext ω; simp only [Pi.mul_apply]; ring
      rw [heq]
      filter_upwards [condExp_mul_of_stronglyMeasurable_left ((hH.measurable_add_one k).pow 2)
        (hint k hkn) (hint' k hkn)] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hkn
  filter_upwards [ae_all_iff.2 hk] with ω hω
  simp only [predictableQuadraticVariation, stochasticIntegral, sum_range_succ,
    add_sub_cancel_left]
  exact sum_congr rfl fun k hk => hω k (mem_range.1 hk)

/-- **Conditional square sum of the scaled Nelson–Aalen process** (exact, on the grid). For
`M = N - ∫ Y dα` with an arbitrary real process `N`, suppose the increments have the conditional
second moment `E[(ΔM_{j+1})² | ℱ_j] = Y_{j+1} Δα_{j+1} (1 - Δα_{j+1})` at the steps `j < k`
(only those are used). Then the conditional square sum `∑_{i < k} E[(Δ √n (Â - Λ*))² | ℱ_i]`
(`predictableQuadraticVariation`) equals
`n ∑_{i < k} Y_{i+1}⁻¹ Δα_{i+1} (1 - Δα_{i+1})` a.e. The martingale property of `M` is not
assumed; for a martingale `M` (binomial variance: each of the `Y_{k+1}` subjects at risk fails
independently with probability `Δα_{k+1}`) this is `⟨√n (Â - Λ*)⟩_k`, the grid form of
`∫_0^t n J / Y dΛ`. The proof is the square-sum identity for `H • M`
(`predictableQuadraticVariation_stochasticIntegral`) applied to the T45 representation. -/
theorem predictableQuadraticVariation_naScaledProcess {n : ℕ} {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (k : ℕ) (hY : IsStronglyPredictable ℱ Y) (hY1 : ∀ k ω, Y k ω = 0 ∨ 1 ≤ Y k ω)
    (hsq : ∀ j < k, Integrable (fun ω => ((N (j + 1) ω - aalenCompensator Y α (j + 1) ω) -
      (N j ω - aalenCompensator Y α j ω)) ^ 2) μ)
    (hcv : ∀ j < k, μ[fun ω => ((N (j + 1) ω - aalenCompensator Y α (j + 1) ω) -
      (N j ω - aalenCompensator Y α j ω)) ^ 2 | ℱ j] =ᵐ[μ]
        fun ω => Y (j + 1) ω * (α (j + 1) - α j) * (1 - (α (j + 1) - α j))) :
    predictableQuadraticVariation μ ℱ (naScaledProcess n N Y α) k =ᵐ[μ]
      naVarianceSum n Y α k := by
  have hYi := isStronglyPredictable_inv hY
  have hH : IsStronglyPredictable ℱ fun k ω => Real.sqrt n * (Y k ω)⁻¹ :=
    .of_measurable_add_one (stronglyMeasurable_const.mul (hYi.stronglyAdapted 0))
      fun j => stronglyMeasurable_const.mul (hYi.measurable_add_one j)
  have hint : ∀ j < k, Integrable (fun ω => (Real.sqrt n * (Y (j + 1) ω)⁻¹) ^ 2 *
      ((N (j + 1) ω - aalenCompensator Y α (j + 1) ω) -
        (N j ω - aalenCompensator Y α j ω)) ^ 2) μ := by
    intro j hj
    refine (hsq j hj).bdd_mul (c := (n : ℝ))
      (((hH.measurable_add_one j).mono (ℱ.le j)).pow 2).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    have h1 : (Y (j + 1) ω)⁻¹ ^ 2 ≤ 1 := by
      rcases hY1 (j + 1) ω with h | h
      · simp [h]
      · exact pow_le_one₀ (inv_nonneg.2 (by linarith)) (inv_le_one_of_one_le₀ h)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have h := predictableQuadraticVariation_stochasticIntegral_of_lt (μ := μ)
    (H := fun k ω => Real.sqrt n * (Y k ω)⁻¹)
    (M := fun k ω => N k ω - aalenCompensator Y α k ω) hH hint hsq
  have hcv' : ∀ j, ∀ᵐ ω ∂μ, j < k →
      μ[fun ω => ((N (j + 1) ω - aalenCompensator Y α (j + 1) ω) -
        (N j ω - aalenCompensator Y α j ω)) ^ 2 | ℱ j] ω =
        Y (j + 1) ω * (α (j + 1) - α j) * (1 - (α (j + 1) - α j)) := fun j => by
    by_cases hj : j < k
    · filter_upwards [hcv j hj] with ω hω _ using hω
    · exact Eventually.of_forall fun _ h => absurd h hj
  rw [naScaledProcess_eq_stochasticIntegral]
  filter_upwards [h, ae_all_iff.2 hcv'] with ω h1 h2
  rw [h1]
  simp only [stochasticIntegral, naVarianceSum]
  refine sum_congr rfl fun i hi => ?_
  rw [predictableQuadraticVariation, predictableQuadraticVariation, sum_range_succ,
    add_sub_cancel_left, h2 i (mem_range.1 hi), mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  have := sq_inv_mul_self (Y (i + 1) ω)
  linear_combination (n : ℝ) * (α (i + 1) - α i) * (1 - (α (i + 1) - α i)) * this

/-- **The binomial conditional variance holds for a single subject.** If the counting process has
unit jumps (adapted and integrable), follows Aalen's model with a predictable integrable at-risk
indicator `Y ∈ {0, 1}`, then `E[(ΔM_{k+1})² | ℱ_k] = Y_{k+1} Δα_{k+1} (1 - Δα_{k+1})` a.e. for
`M = N - ∫ Y dα`. Derived from the T45 identity `⟨N - A⟩ = ∑ ΔA (1 - ΔA)`
(`HasUnitJumps.predictableQuadraticVariation_martingalePart`) and the compensator identification
`predictablePart_eq_aalenCompensator`; it shows the hypothesis `hcv` of
`predictableQuadraticVariation_naScaledProcess` is met by a genuine model. -/
theorem condExp_sq_increment_of_hasUnitJumps [IsFiniteMeasure μ] {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hN : HasUnitJumps N) (hadapt : StronglyAdapted ℱ N) (hint : ∀ n, Integrable (N n) μ)
    (hM : Martingale (fun n ω => N n ω - aalenCompensator Y α n ω) ℱ μ)
    (hY : IsStronglyPredictable ℱ Y) (hYint : ∀ n, Integrable (Y n) μ)
    (hY01 : ∀ n ω, Y n ω = 0 ∨ Y n ω = 1) (k : ℕ) :
    μ[fun ω => ((N (k + 1) ω - aalenCompensator Y α (k + 1) ω) -
      (N k ω - aalenCompensator Y α k ω)) ^ 2 | ℱ k] =ᵐ[μ]
        fun ω => Y (k + 1) ω * (α (k + 1) - α k) * (1 - (α (k + 1) - α k)) := by
  have hP := predictablePart_eq_aalenCompensator hM hY hYint
  have hQ := hN.predictableQuadraticVariation_martingalePart (μ := μ) (ℱ := ℱ) hadapt hint
  -- the squared increments of `martingalePart N` and of `N - ∫ Y dα` agree a.e.
  have hsq : (fun ω => (martingalePart N ℱ μ (k + 1) ω - martingalePart N ℱ μ k ω) ^ 2) =ᵐ[μ]
      fun ω => ((N (k + 1) ω - aalenCompensator Y α (k + 1) ω) -
        (N k ω - aalenCompensator Y α k ω)) ^ 2 := by
    filter_upwards [hP k, hP (k + 1)] with ω h0 h1
    simp only [martingalePart, Pi.sub_apply, h0, h1]
  -- the compensator increment is `Y Δα`
  have ha : μ[N (k + 1) - N k | ℱ k] =ᵐ[μ] fun ω => Y (k + 1) ω * (α (k + 1) - α k) := by
    filter_upwards [hP k, hP (k + 1)] with ω h0 h1
    have h2 := congrFun (predictablePart_add_one (f := N) (ℱ := ℱ) (μ := μ) k) ω
    simp only [Pi.add_apply] at h2
    rw [h0, h1, aalenCompensator, stochasticIntegral_succ] at h2
    linarith
  -- the predictable variation increment is the conditional variance
  have hinc : ∀ ω, predictableQuadraticVariation μ ℱ (martingalePart N ℱ μ) (k + 1) ω -
      predictableQuadraticVariation μ ℱ (martingalePart N ℱ μ) k ω =
        μ[fun ω => (martingalePart N ℱ μ (k + 1) ω - martingalePart N ℱ μ k ω) ^ 2 | ℱ k] ω :=
    fun ω => by simp [predictableQuadraticVariation, sum_range_succ]
  filter_upwards [hQ k, hQ (k + 1), condExp_congr_ae (m := ℱ k) hsq, ha] with ω h0 h1 h2 h3
  rw [← h2, ← hinc, h0, h1, sum_range_succ, add_sub_cancel_left, h3]
  rcases hY01 (k + 1) ω with h | h <;> simp [h]

/-! ### Law of large numbers: the variance sum converges -/

/-- Termwise error of replacing `n Y⁻¹ d (1 - d)` by `d / ȳ` when `Y / n` is within `δ ≤ ε / 2` of
`ȳ ≥ ε > 0` and `0 ≤ d ≤ η`. -/
private lemma abs_varianceTerm_sub_le {n : ℕ} (hn : 0 < n) {y yb d δ ε η : ℝ} (hε : 0 < ε)
    (hyb : ε ≤ yb) (hδ : δ ≤ ε / 2) (hdev : |y / n - yb| ≤ δ) (hd0 : 0 ≤ d) (hdη : d ≤ η) :
    |(n : ℝ) * y⁻¹ * d * (1 - d) - d / yb| ≤ d * (2 * δ / ε ^ 2 + 2 * η / ε) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.2 hn
  set u := y / n with hu
  have hdev' := abs_le.1 hdev
  have hu0 : ε / 2 ≤ u := by linarith [hdev'.1]
  have hupos : 0 < u := by linarith
  have hybpos : 0 < yb := by linarith
  have hy : y = u * n := by rw [hu]; field_simp
  have hE : (n : ℝ) * y⁻¹ * d * (1 - d) - d / yb = d * ((yb - u) / (u * yb)) - d * (d / u) := by
    rw [hy]; field_simp; ring
  rw [hE]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hd0, abs_div, abs_of_pos (mul_pos hupos hybpos),
    abs_of_nonneg (div_nonneg hd0 hupos.le), mul_add]
  gcongr ?_ + ?_
  · refine mul_le_mul_of_nonneg_left ?_ hd0
    rw [div_le_div_iff₀ (mul_pos hupos hybpos) (by positivity), abs_sub_comm]
    have : ε ^ 2 ≤ 2 * (u * yb) := by nlinarith
    nlinarith [abs_nonneg (u - yb)]
  · refine mul_le_mul_of_nonneg_left ?_ hd0
    rw [div_le_div_iff₀ hupos hε]
    nlinarith

/-- **Pathwise LLN bound.** If at every grid step `i < k` the at-risk fraction `Y_{i+1} / n` is
within `δ ≤ ε / 2` of a level `ȳ_{i+1} ≥ ε > 0` and the hazard increments satisfy
`0 ≤ Δα ≤ η`, the variance sum differs from the Riemann–Stieltjes sum `∑ Δα / ȳ` by at most
`(2 δ / ε² + 2 η / ε) (α_k - α_0)`. -/
theorem abs_naVarianceSum_sub_le {n : ℕ} (hn : 0 < n) {Y : ℕ → Ω → ℝ} {α ybar : ℕ → ℝ} {k : ℕ}
    {δ ε η : ℝ} {ω : Ω} (hε : 0 < ε) (hδ : δ ≤ ε / 2)
    (hinc : ∀ i < k, 0 ≤ α (i + 1) - α i) (hη : ∀ i < k, α (i + 1) - α i ≤ η)
    (hyb : ∀ i < k, ε ≤ ybar (i + 1)) (hdev : ∀ i < k, |Y (i + 1) ω / n - ybar (i + 1)| ≤ δ) :
    |naVarianceSum n Y α k ω - ∑ i ∈ range k, (α (i + 1) - α i) / ybar (i + 1)| ≤
      (2 * δ / ε ^ 2 + 2 * η / ε) * (α k - α 0) := by
  rw [naVarianceSum, ← sum_sub_distrib, ← sum_range_sub, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  have hi := mem_range.1 hi
  rw [mul_comm (2 * δ / ε ^ 2 + 2 * η / ε)]
  exact abs_varianceTerm_sub_le hn hε (hyb i hi) hδ (hdev i hi) (hinc i hi) (hη i hi)

/-- **Variance identification from a law of large numbers** (array form). For each sample size
`n`, let `Y n` be an at-risk process and `α n` a cumulative hazard on a grid with `k n` steps up to
the time of interest, and let `ȳ n` be deterministic levels with `ȳ n (i + 1) ≥ ε > 0`. Assume

* the hazard increments are non-negative, uniformly small (the mesh condition `hmesh`, which holds
  for a continuous limiting hazard), and of bounded total `α n (k n) - α n 0 ≤ L`;
* (**uniform LLN**) `P(∃ i < k n, |Y n (i+1) / n - ȳ n (i+1)| > δ) → 0` for every `δ > 0`;
* (**grid limit**, a T57-style input) the Riemann–Stieltjes sums `∑_{i < k n} Δα / ȳ` converge to
  `σ²`.

Then the variance sums `n ∑ Y⁻¹ Δα (1 - Δα)` converge in probability to `σ²`. -/
theorem tendstoInMeasure_naVarianceSum {Y : ℕ → ℕ → Ω → ℝ} {α ybar : ℕ → ℕ → ℝ} {k : ℕ → ℕ}
    {ε L σsq : ℝ} (hε : 0 < ε)
    (hinc : ∀ n, ∀ i < k n, 0 ≤ α n (i + 1) - α n i)
    (hmesh : ∀ e, 0 < e → ∀ᶠ n in atTop, ∀ i < k n, α n (i + 1) - α n i ≤ e)
    (hL : ∀ n, α n (k n) - α n 0 ≤ L)
    (hyb : ∀ n, ∀ i < k n, ε ≤ ybar n (i + 1))
    (hLLN : ∀ δ, 0 < δ → Tendsto (fun n => μ {ω | ∃ i < k n,
      δ < |Y n (i + 1) ω / n - ybar n (i + 1)|}) atTop (𝓝 0))
    (hgrid : Tendsto (fun n => ∑ i ∈ range (k n), (α n (i + 1) - α n i) / ybar n (i + 1)) atTop
      (𝓝 σsq)) :
    TendstoInMeasure μ (fun n => naVarianceSum n (Y n) (α n) (k n)) atTop (fun _ => σsq) := by
  rw [tendstoInMeasure_iff_dist]
  intro e he
  set C : ℝ := |L| + 1 with hC
  have hCpos : 0 < C := by positivity
  set δ : ℝ := min (ε / 2) (e * ε ^ 2 / (8 * C)) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε / 2 := min_le_left _ _
  have hδe : 2 * δ / ε ^ 2 * C ≤ e / 4 := by
    have : δ ≤ e * ε ^ 2 / (8 * C) := min_le_right _ _
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  set η : ℝ := e * ε / (8 * C) with hηdef
  have hηe : 2 * η / ε * C ≤ e / 4 := by
    rw [hηdef]; field_simp; nlinarith
  have hge : ∀ᶠ n in atTop, dist (∑ i ∈ range (k n), (α n (i + 1) - α n i) / ybar n (i + 1))
      σsq < e / 2 := (Metric.tendsto_nhds.1 hgrid) _ (by positivity)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hLLN δ hδpos)
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hmesh η (by positivity), hge, eventually_gt_atTop 0] with n hηn hgn hn
  refine measure_mono fun ω hω => ?_
  simp only [Set.mem_ofPred_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have hdev : ∀ i < k n, |Y n (i + 1) ω / n - ybar n (i + 1)| ≤ δ := fun i hi => hcon i hi
  have hb := abs_naVarianceSum_sub_le hn hε hδε (hinc n) hηn (hyb n) hdev
  have hαnn : 0 ≤ α n (k n) - α n 0 := by
    rw [← sum_range_sub]; exact sum_nonneg fun i hi => hinc n i (mem_range.1 hi)
  have hαC : α n (k n) - α n 0 ≤ C := (hL n).trans (by rw [hC]; linarith [le_abs_self L])
  have hb' : (2 * δ / ε ^ 2 + 2 * η / ε) * (α n (k n) - α n 0) ≤ e / 2 := by
    calc (2 * δ / ε ^ 2 + 2 * η / ε) * (α n (k n) - α n 0)
        ≤ (2 * δ / ε ^ 2 + 2 * η / ε) * C :=
          mul_le_mul_of_nonneg_left hαC (by positivity)
      _ ≤ e / 2 := by rw [add_mul]; linarith
  rw [Real.dist_eq] at hgn hω
  have := abs_sub_le (naVarianceSum n (Y n) (α n) (k n) ω)
    (∑ i ∈ range (k n), (α n (i + 1) - α n i) / ybar n (i + 1)) σsq
  linarith
/-- **Conditional square sums of the scaled Nelson–Aalen process** (grid form). For each `n`, let
`N n` be a real process and `Y n` a predictable at-risk process with values in `{0} ∪ [1, ∞)`, on a
grid with filtration `ℱ n`, with the conditional second moment of
`predictableQuadraticVariation_naScaledProcess` at the steps `j < k n`; no martingale property is
assumed. Under the
uniform LLN for `Y n / n`, the mesh condition and the grid limit of
`tendstoInMeasure_naVarianceSum`, the conditional square sums of `√n (Â - Λ*)` up to step `k n`
converge in probability to `σ²`. -/
theorem tendstoInMeasure_predictableQuadraticVariation_naScaledProcess
    {ℱ : ℕ → Filtration ℕ m0} {N Y : ℕ → ℕ → Ω → ℝ} {α ybar : ℕ → ℕ → ℝ} {k : ℕ → ℕ}
    {ε L σsq : ℝ} (hε : 0 < ε)
    (hY : ∀ n, IsStronglyPredictable (ℱ n) (Y n)) (hY1 : ∀ n j ω, Y n j ω = 0 ∨ 1 ≤ Y n j ω)
    (hsq : ∀ n, ∀ j < k n, Integrable (fun ω =>
      ((N n (j + 1) ω - aalenCompensator (Y n) (α n) (j + 1) ω) -
        (N n j ω - aalenCompensator (Y n) (α n) j ω)) ^ 2) μ)
    (hcv : ∀ n, ∀ j < k n, μ[fun ω => ((N n (j + 1) ω - aalenCompensator (Y n) (α n) (j + 1) ω) -
      (N n j ω - aalenCompensator (Y n) (α n) j ω)) ^ 2 | ℱ n j] =ᵐ[μ]
        fun ω => Y n (j + 1) ω * (α n (j + 1) - α n j) * (1 - (α n (j + 1) - α n j)))
    (hinc : ∀ n, ∀ i < k n, 0 ≤ α n (i + 1) - α n i)
    (hmesh : ∀ e, 0 < e → ∀ᶠ n in atTop, ∀ i < k n, α n (i + 1) - α n i ≤ e)
    (hL : ∀ n, α n (k n) - α n 0 ≤ L)
    (hyb : ∀ n, ∀ i < k n, ε ≤ ybar n (i + 1))
    (hLLN : ∀ δ, 0 < δ → Tendsto (fun n => μ {ω | ∃ i < k n,
      δ < |Y n (i + 1) ω / n - ybar n (i + 1)|}) atTop (𝓝 0))
    (hgrid : Tendsto (fun n => ∑ i ∈ range (k n), (α n (i + 1) - α n i) / ybar n (i + 1)) atTop
      (𝓝 σsq)) :
    TendstoInMeasure μ (fun n => predictableQuadraticVariation μ (ℱ n)
      (naScaledProcess n (N n) (Y n) (α n)) (k n)) atTop (fun _ => σsq) :=
  (tendstoInMeasure_naVarianceSum hε hinc hmesh hL hyb hLLN hgrid).congr_left fun n =>
    (predictableQuadraticVariation_naScaledProcess (k n) (hY n) (hY1 n) (hsq n) (hcv n)).symm
/-! ### The grid limit: Riemann–Stieltjes sums of `dΛ / y` -/

/-- The cumulative hazard `Λ` sampled on the uniform grid of mesh `h`: `i ↦ Λ (i h)`. -/
noncomputable def gridHazard (Λ : ℝ → ℝ) (h : ℝ) (i : ℕ) : ℝ := Λ (i * h)

/-- The index `⌊t / h⌋` of the last point of the grid of mesh `h` at or before `t`. -/
noncomputable def gridIndex (t h : ℝ) : ℕ := ⌊t / h⌋₊

/-- The grid point `⌊t / h⌋ h` lies at or before `t`. -/
theorem gridIndex_mul_le {t h : ℝ} (ht : 0 ≤ t) (hh : 0 < h) : (gridIndex t h : ℝ) * h ≤ t := by
  have := Nat.floor_le (div_nonneg ht hh.le)
  rw [gridIndex]
  rwa [le_div_iff₀ hh] at this

/-- The grid point `⌊t / h⌋ h` lies within one mesh of `t`. -/
theorem sub_lt_gridIndex_mul {t h : ℝ} (hh : 0 < h) : t - h < (gridIndex t h : ℝ) * h := by
  have := Nat.lt_floor_add_one (t / h)
  rw [div_lt_iff₀ hh] at this
  rw [gridIndex]
  linarith

private lemma measureReal_Ioc (Λ : StieltjesFunction ℝ) {a b : ℝ} (hab : a ≤ b) :
    Λ.measure.real (Set.Ioc a b) = Λ b - Λ a := by
  rw [measureReal_def, Λ.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 (Λ.mono hab))]

private lemma measure_Ioc_lt_top (Λ : StieltjesFunction ℝ) (a b : ℝ) :
    Λ.measure (Set.Ioc a b) < ⊤ := by
  rw [Λ.measure_Ioc]; exact ENNReal.ofReal_lt_top

/-- One Riemann–Stieltjes cell: `|ΔΛ f(b) - ∫_{(a, b]} f dΛ| ≤ w ΔΛ` if `f` varies by at most `w`
from its right-endpoint value on `(a, b]`. -/
private lemma abs_cell_sub_le (Λ : StieltjesFunction ℝ) {f : ℝ → ℝ} {a b w : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Set.Ioc a b) Λ.measure) (hw : ∀ s ∈ Set.Ioc a b, |f b - f s| ≤ w) :
    |(Λ b - Λ a) * f b - ∫ s in Set.Ioc a b, f s ∂Λ.measure| ≤ w * (Λ b - Λ a) := by
  have hfin := measure_Ioc_lt_top Λ a b
  have heq : (Λ b - Λ a) * f b - ∫ s in Set.Ioc a b, f s ∂Λ.measure =
      ∫ s in Set.Ioc a b, (f b - f s) ∂Λ.measure := by
    rw [integral_sub (integrableOn_const hfin.ne) hf, setIntegral_const, smul_eq_mul,
      measureReal_Ioc Λ hab]
  rw [heq, ← measureReal_Ioc Λ hab, ← Real.norm_eq_abs]
  exact norm_setIntegral_le_of_norm_le_const hfin fun s hs => by
    rw [Real.norm_eq_abs]; exact hw s hs
/-- The integral over `(0, k h]` splits into the grid cells `(i h, (i + 1) h]`. -/
private lemma setIntegral_Ioc_eq_sum (Λ : StieltjesFunction ℝ) {f : ℝ → ℝ} {h : ℝ} (hh : 0 ≤ h)
    (k : ℕ) (hf : IntegrableOn f (Set.Ioc 0 (k * h)) Λ.measure) :
    ∫ s in Set.Ioc 0 ((k : ℝ) * h), f s ∂Λ.measure =
      ∑ i ∈ range k, ∫ s in Set.Ioc ((i : ℝ) * h) (((i + 1 : ℕ) : ℝ) * h), f s ∂Λ.measure := by
  have hmono : ∀ i j : ℕ, i ≤ j → (i : ℝ) * h ≤ (j : ℝ) * h := fun i j hij =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hh
  have hint : ∀ i < k, IntervalIntegrable f Λ.measure ((i : ℝ) * h) (((i + 1 : ℕ) : ℝ) * h) := by
    intro i hi
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hmono _ _ (Nat.le_succ i))]
    refine hf.mono_set (Set.Ioc_subset_Ioc ?_ (hmono _ _ hi))
    exact mul_nonneg (Nat.cast_nonneg _) hh
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := Λ.measure) (f := f)
    (a := fun i : ℕ => (i : ℝ) * h) hint
  simp only [Nat.cast_zero, zero_mul] at h
  rw [← intervalIntegral.integral_of_le (mul_nonneg (Nat.cast_nonneg _) hh), ← h]
  exact sum_congr rfl fun i _ => intervalIntegral.integral_of_le (hmono _ _ (Nat.le_succ i))

/-- **Riemann–Stieltjes error on the grid**: if `f` varies by at most `w` within each cell, the
right-endpoint sum `∑_{i < k} ΔΛ_i f((i + 1) h)` is within `w (Λ(k h) - Λ 0)` of
`∫_{(0, k h]} f dΛ`. -/
private lemma abs_gridSum_sub_integral_le (Λ : StieltjesFunction ℝ) {f : ℝ → ℝ} {h w : ℝ}
    (hh : 0 ≤ h) (k : ℕ) (hf : IntegrableOn f (Set.Ioc 0 (k * h)) Λ.measure)
    (hw : ∀ i < k, ∀ s ∈ Set.Ioc ((i : ℝ) * h) (((i + 1 : ℕ) : ℝ) * h),
      |f (((i + 1 : ℕ) : ℝ) * h) - f s| ≤ w) :
    |∑ i ∈ range k, (Λ (((i + 1 : ℕ) : ℝ) * h) - Λ ((i : ℝ) * h)) * f (((i + 1 : ℕ) : ℝ) * h) -
      ∫ s in Set.Ioc 0 ((k : ℝ) * h), f s ∂Λ.measure| ≤ w * (Λ ((k : ℝ) * h) - Λ 0) := by
  have hmono : ∀ i j : ℕ, i ≤ j → (i : ℝ) * h ≤ (j : ℝ) * h := fun i j hij =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hh
  have htel : Λ ((k : ℝ) * h) - Λ 0 =
      ∑ i ∈ range k, (Λ (((i + 1 : ℕ) : ℝ) * h) - Λ ((i : ℝ) * h)) := by
    rw [sum_range_sub (fun i : ℕ => Λ ((i : ℝ) * h))]; simp
  rw [setIntegral_Ioc_eq_sum Λ hh k hf, ← sum_sub_distrib, htel, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  have hi := mem_range.1 hi
  refine abs_cell_sub_le Λ (hmono _ _ (Nat.le_succ i)) ?_ (hw i hi)
  refine hf.mono_set (Set.Ioc_subset_Ioc ?_ (hmono _ _ hi))
  exact mul_nonneg (Nat.cast_nonneg _) hh
/-- **Riemann–Stieltjes convergence on the uniform grid.** Let `Λ` be a continuous cumulative hazard
(a continuous `StieltjesFunction`), `y` continuous on `[0, τ]` with `y ≥ ε > 0` there, and
`K n → ∞` grid sizes of mesh `h_n = τ / K n`. For `t ∈ [0, τ]` the right-endpoint sums
`∑_{i < ⌊t / h_n⌋} (Λ((i + 1) h_n) - Λ(i h_n)) / y((i + 1) h_n)` converge to
`∫_{(0, t]} dΛ / y`. -/
theorem tendsto_gridSum_integral (Λ : StieltjesFunction ℝ) (hΛ : Continuous Λ) {y : ℝ → ℝ}
    {τ t ε : ℝ} (hτ : 0 < τ) (ht : t ∈ Set.Icc 0 τ) (hε : 0 < ε)
    (hy : ContinuousOn y (Set.Icc 0 τ)) (hyε : ∀ s ∈ Set.Icc 0 τ, ε ≤ y s) {K : ℕ → ℕ}
    (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => ∑ i ∈ range (gridIndex t (τ / K n)),
      (gridHazard Λ (τ / K n) (i + 1) - gridHazard Λ (τ / K n) i) /
        y (((i + 1 : ℕ) : ℝ) * (τ / K n))) atTop
      (𝓝 (∫ s in Set.Ioc 0 t, (y s)⁻¹ ∂Λ.measure)) := by
  set f : ℝ → ℝ := fun s => (y s)⁻¹ with hf
  have hfc : ContinuousOn f (Set.Icc 0 τ) :=
    hy.inv₀ fun s hs => (lt_of_lt_of_le hε (hyε s hs)).ne'
  have hfint : IntegrableOn f (Set.Icc 0 τ) Λ.measure := hfc.integrableOn_compact isCompact_Icc
  have hfb : ∀ s ∈ Set.Icc 0 τ, |f s| ≤ ε⁻¹ := fun s hs => by
    have h1 := hyε s hs
    have h0 : 0 < y s := hε.trans_le h1
    rw [hf, abs_inv, abs_of_pos h0]
    exact inv_anti₀ hε h1
  have hUC := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hfc)
  rw [Metric.tendsto_nhds]
  intro e he
  set W : ℝ := Λ τ - Λ 0 + 1 with hWdef
  have hΛτ : Λ 0 ≤ Λ τ := Λ.mono hτ.le
  have hW : 0 < W := by linarith
  obtain ⟨d, hd, hdf⟩ := hUC (e / (2 * W)) (by positivity)
  have hh0 : Tendsto (fun n => τ / (K n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat τ).comp hK
  have hpos : ∀ᶠ n in atTop, 0 < K n := hK.eventually_gt_atTop 0
  have hsmall : ∀ᶠ n in atTop, τ / (K n : ℝ) < d := hh0.eventually (gt_mem_nhds hd)
  have hak : Tendsto (fun n => (gridIndex t (τ / K n) : ℝ) * (τ / K n)) atTop (𝓝 t) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun n => t - τ / K n)
      (h := fun _ => t) ?_ tendsto_const_nhds ?_ ?_
    · simpa using (tendsto_const_nhds (x := t)).sub hh0
    · filter_upwards [hpos] with n hn
      exact (sub_lt_gridIndex_mul (by positivity)).le
    · filter_upwards [hpos] with n hn
      exact gridIndex_mul_le ht.1 (by positivity)
  have hΛk : ∀ᶠ n in atTop,
      Λ t - Λ ((gridIndex t (τ / K n) : ℝ) * (τ / K n)) < e * ε / 2 := by
    have h2 := (tendsto_const_nhds (x := Λ t)).sub ((hΛ.tendsto t).comp hak)
    rw [sub_self] at h2
    exact h2.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hpos, hsmall, hΛk] with n hn hsm hΛn
  set h : ℝ := τ / (K n : ℝ) with hhdef
  have hh : 0 < h := by positivity
  set k := gridIndex t h with hkdef
  have hkt : (k : ℝ) * h ≤ t := gridIndex_mul_le ht.1 hh
  have hk0 : 0 ≤ (k : ℝ) * h := by positivity
  have hsubI : Set.Ioc 0 ((k : ℝ) * h) ⊆ Set.Icc 0 τ := fun s hs =>
    ⟨hs.1.le, hs.2.trans (hkt.trans ht.2)⟩
  have hsubT : Set.Ioc ((k : ℝ) * h) t ⊆ Set.Icc 0 τ := fun s hs =>
    ⟨hk0.trans hs.1.le, hs.2.trans ht.2⟩
  have hcell : ∀ i < k, ∀ s ∈ Set.Ioc ((i : ℝ) * h) (((i + 1 : ℕ) : ℝ) * h),
      |f (((i + 1 : ℕ) : ℝ) * h) - f s| ≤ e / (2 * W) := by
    intro i hi s hs
    have hb : ((i + 1 : ℕ) : ℝ) * h ≤ (k : ℝ) * h :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.2 hi) hh.le
    have hs0 : 0 ≤ (i : ℝ) * h := by positivity
    have hbI : ((i + 1 : ℕ) : ℝ) * h ∈ Set.Icc 0 τ := ⟨by positivity, hb.trans (hkt.trans ht.2)⟩
    have hsI : s ∈ Set.Icc 0 τ := ⟨hs0.trans hs.1.le, hs.2.trans (hb.trans (hkt.trans ht.2))⟩
    have hcast : ((i + 1 : ℕ) : ℝ) * h = (i : ℝ) * h + h := by push_cast; ring
    have hdist : dist (((i + 1 : ℕ) : ℝ) * h) s < d := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.2])]
      linarith [hs.1]
    have := hdf _ hbI _ hsI hdist
    rw [Real.dist_eq] at this
    exact this.le
  have h1 := abs_gridSum_sub_integral_le Λ hh.le k (hfint.mono_set hsubI) hcell
  have hsplit : ∫ s in Set.Ioc 0 t, f s ∂Λ.measure =
      ∫ s in Set.Ioc 0 ((k : ℝ) * h), f s ∂Λ.measure +
        ∫ s in Set.Ioc ((k : ℝ) * h) t, f s ∂Λ.measure := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
      (hfint.mono_set hsubI) (hfint.mono_set hsubT), Set.Ioc_union_Ioc_eq_Ioc hk0 hkt]
  have htail : |∫ s in Set.Ioc ((k : ℝ) * h) t, f s ∂Λ.measure| ≤
      ε⁻¹ * (Λ t - Λ ((k : ℝ) * h)) := by
    rw [← measureReal_Ioc Λ hkt, ← Real.norm_eq_abs]
    exact norm_setIntegral_le_of_norm_le_const (measure_Ioc_lt_top Λ _ _) fun s hs => by
      rw [Real.norm_eq_abs]; exact hfb s (hsubT hs)
  have hsum : ∑ i ∈ range k, (gridHazard Λ h (i + 1) - gridHazard Λ h i) /
      y (((i + 1 : ℕ) : ℝ) * h) = ∑ i ∈ range k,
        (Λ (((i + 1 : ℕ) : ℝ) * h) - Λ ((i : ℝ) * h)) * f (((i + 1 : ℕ) : ℝ) * h) :=
    sum_congr rfl fun i _ => by rw [gridHazard, gridHazard, hf, div_eq_mul_inv]
  have hA : e / (2 * W) * (Λ ((k : ℝ) * h) - Λ 0) ≤ e / 2 := by
    have hX : Λ ((k : ℝ) * h) - Λ 0 ≤ W := by
      have := Λ.mono (hkt.trans ht.2); linarith
    have hX0 : 0 ≤ Λ ((k : ℝ) * h) - Λ 0 := sub_nonneg.2 (Λ.mono hk0)
    calc e / (2 * W) * (Λ ((k : ℝ) * h) - Λ 0) ≤ e / (2 * W) * W :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = e / 2 := by field_simp
  have hB : ε⁻¹ * (Λ t - Λ ((k : ℝ) * h)) < e / 2 := by
    rw [inv_mul_lt_iff₀ hε]; linarith
  rw [Real.dist_eq, hsum, hsplit]
  have := abs_sub (∑ i ∈ range k, (Λ (((i + 1 : ℕ) : ℝ) * h) - Λ ((i : ℝ) * h)) *
    f (((i + 1 : ℕ) : ℝ) * h) - ∫ s in Set.Ioc 0 ((k : ℝ) * h), f s ∂Λ.measure)
    (∫ s in Set.Ioc ((k : ℝ) * h) t, f s ∂Λ.measure)
  rw [sub_sub] at this
  linarith
/-- **Mesh condition for a continuous hazard**: the grid increments of a continuous cumulative
hazard up to `t ∈ [0, τ]` are eventually uniformly small. -/
theorem eventually_gridHazard_increment_le (Λ : StieltjesFunction ℝ) (hΛ : Continuous Λ)
    {τ t : ℝ} (hτ : 0 < τ) (ht : t ∈ Set.Icc 0 τ) {K : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    (e : ℝ) (he : 0 < e) : ∀ᶠ n in atTop, ∀ i < gridIndex t (τ / K n),
      gridHazard Λ (τ / K n) (i + 1) - gridHazard Λ (τ / K n) i ≤ e := by
  obtain ⟨d, hd, hdf⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hΛ.continuousOn) e he
  have hh0 : Tendsto (fun n => τ / (K n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat τ).comp hK
  filter_upwards [hK.eventually_gt_atTop 0, hh0.eventually (gt_mem_nhds hd)] with n hn hsm i hi
  set h : ℝ := τ / (K n : ℝ) with hhdef
  have hh : 0 < h := by positivity
  have hkt := gridIndex_mul_le ht.1 hh
  have hb : ((i + 1 : ℕ) : ℝ) * h ≤ (gridIndex t h : ℝ) * h :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hi) hh.le
  have hcast : ((i + 1 : ℕ) : ℝ) * h = (i : ℝ) * h + h := by push_cast; ring
  have hs0 : 0 ≤ (i : ℝ) * h := by positivity
  have hbI : ((i + 1 : ℕ) : ℝ) * h ∈ Set.Icc 0 τ := ⟨by positivity, hb.trans (hkt.trans ht.2)⟩
  have haI : (i : ℝ) * h ∈ Set.Icc 0 τ := ⟨hs0, by linarith [hb, hkt, ht.2]⟩
  have hdist : dist (((i + 1 : ℕ) : ℝ) * h) ((i : ℝ) * h) < d := by
    rw [Real.dist_eq, hcast, add_sub_cancel_left, abs_of_pos hh]; exact hsm
  have := hdf _ hbI _ haI hdist
  rw [Real.dist_eq] at this
  rw [gridHazard, gridHazard]
  exact (le_abs_self _).trans this.le

/-- **Conditional square sums of `√n (Â - Λ*)` converge to `∫_0^t dΛ / y`** in probability.

Setting: a continuous cumulative hazard `Λ` (a continuous `StieltjesFunction`), a horizon `τ > 0`
and a time `t ∈ [0, τ]`; for each `n` a grid of mesh `h_n = τ / K n` (`K n → ∞`) carrying a real
process `N n` and a predictable at-risk process `Y n` (values in `{0} ∪ [1, ∞)`), with hazard
increments `ΔΛ` (`gridHazard`) and the conditional second moment `E[(ΔM)² | ℱ] = Y ΔΛ (1 - ΔΛ)` of
`M = N n - ∫ Y n dΛ` at the grid steps before `t` (with its integrability). Neither that `N n` is
a counting process nor that `M` is a martingale is assumed. The limiting at-risk fraction `y` is
continuous on `[0, τ]` and bounded below by `ε > 0` (the horizon is supported), and the **law of
large numbers** `sup_{grid points ≤ t} |Y n / n - y| → 0` holds in probability. Then the conditional
square sums `∑ E[(Δ √n (Â - Λ*))² | ℱ]` up to the grid point `⌊t / h_n⌋ h_n` converge in
probability to `∫_{(0, t]} (y s)⁻¹ dΛ(s)`. If `M` is a martingale
(`martingale_nelsonAalenProcess_sub` then makes `√n (Â - Λ*)` one), these sums are the predictable
variations `⟨√n (Â - Λ*)⟩` and the limit is the variance function of the Gaussian-martingale limit
(Andersen–Borgan–Gill–Keiding, §IV.1). -/
theorem tendstoInMeasure_predictableQuadraticVariation_naScaledProcess_integral
    {ℱ : ℕ → Filtration ℕ m0} {N Y : ℕ → ℕ → Ω → ℝ} (Λ : StieltjesFunction ℝ)
    (hΛ : Continuous Λ) {y : ℝ → ℝ} {τ t ε : ℝ} (hτ : 0 < τ) (ht : t ∈ Set.Icc 0 τ)
    (hε : 0 < ε) (hy : ContinuousOn y (Set.Icc 0 τ)) (hyε : ∀ s ∈ Set.Icc 0 τ, ε ≤ y s)
    {K : ℕ → ℕ} (hK : Tendsto K atTop atTop)
    (hY : ∀ n, IsStronglyPredictable (ℱ n) (Y n)) (hY1 : ∀ n j ω, Y n j ω = 0 ∨ 1 ≤ Y n j ω)
    (hsq : ∀ n, ∀ j < gridIndex t (τ / K n), Integrable (fun ω =>
      ((N n (j + 1) ω - aalenCompensator (Y n) (gridHazard Λ (τ / K n)) (j + 1) ω) -
        (N n j ω - aalenCompensator (Y n) (gridHazard Λ (τ / K n)) j ω)) ^ 2) μ)
    (hcv : ∀ n, ∀ j < gridIndex t (τ / K n), μ[fun ω =>
      ((N n (j + 1) ω - aalenCompensator (Y n) (gridHazard Λ (τ / K n)) (j + 1) ω) -
        (N n j ω - aalenCompensator (Y n) (gridHazard Λ (τ / K n)) j ω)) ^ 2 | ℱ n j] =ᵐ[μ]
        fun ω => Y n (j + 1) ω * (gridHazard Λ (τ / K n) (j + 1) - gridHazard Λ (τ / K n) j) *
          (1 - (gridHazard Λ (τ / K n) (j + 1) - gridHazard Λ (τ / K n) j)))
    (hLLN : ∀ δ, 0 < δ → Tendsto (fun n => μ {ω | ∃ i < gridIndex t (τ / K n),
      δ < |Y n (i + 1) ω / n - y (((i + 1 : ℕ) : ℝ) * (τ / K n))|}) atTop (𝓝 0)) :
    TendstoInMeasure μ (fun n => predictableQuadraticVariation μ (ℱ n)
      (naScaledProcess n (N n) (Y n) (gridHazard Λ (τ / K n))) (gridIndex t (τ / K n)))
      atTop (fun _ => ∫ s in Set.Ioc 0 t, (y s)⁻¹ ∂Λ.measure) := by
  have hgridI : ∀ n, ∀ i < gridIndex t (τ / K n), ((i + 1 : ℕ) : ℝ) * (τ / K n) ∈ Set.Icc 0 τ := by
    intro n i hi
    rcases Nat.eq_zero_or_pos (K n) with h0 | hpos
    · simp [h0, hτ.le]
    · have hh : 0 < τ / (K n : ℝ) := by positivity
      refine ⟨by positivity, ?_⟩
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hi) hh.le).trans
        ((gridIndex_mul_le ht.1 hh).trans ht.2)
  refine tendstoInMeasure_predictableQuadraticVariation_naScaledProcess (L := Λ τ - Λ 0)
    (ybar := fun n i => y ((i : ℝ) * (τ / K n))) hε hY hY1 hsq hcv ?_
    (eventually_gridHazard_increment_le Λ hΛ hτ ht hK) ?_ (fun n i hi => hyε _ (hgridI n i hi))
    hLLN (tendsto_gridSum_integral Λ hΛ hτ ht hε hy hyε hK)
  · intro n i _
    rw [gridHazard, gridHazard, sub_nonneg]
    rcases Nat.eq_zero_or_pos (K n) with h0 | hpos
    · simp [h0]
    · exact Λ.mono (mul_le_mul_of_nonneg_right (by push_cast; linarith) (by positivity))
  · intro n
    rw [gridHazard, gridHazard, Nat.cast_zero, zero_mul]
    rcases Nat.eq_zero_or_pos (K n) with h0 | hpos
    · simp [h0, Λ.mono hτ.le]
    · have hh : 0 < τ / (K n : ℝ) := by positivity
      have := Λ.mono ((gridIndex_mul_le ht.1 hh).trans ht.2)
      linarith
end MathlibExt.Probability.Statistics.ProcessVariance
