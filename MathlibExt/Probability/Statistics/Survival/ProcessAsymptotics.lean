/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Moments.Covariance
public import MathlibExt.Probability.Martingale.FunctionalCLT
public import MathlibExt.Probability.Statistics.FunctionalDelta
public import MathlibExt.Probability.Statistics.Survival.StochasticIntegral
public import MathlibExt.Probability.Statistics.Survival.CompetingRisks

/-!
# Process-level limits of the Nelson–Aalen, Kaplan–Meier and Aalen–Johansen estimators

This file applies the SURV-08 toolkit (the `C → D` transfer theorem and converging-together lemma
of `MathlibExt.Probability.Martingale.FunctionalCLT`, the functional delta theorem and grid
product integral of `MathlibExt.Probability.Statistics.FunctionalDelta`, and the counting-process
martingale representations of `MathlibExt.Probability.Statistics.Survival.StochasticIntegral`) to
the three classical survival estimators. Horizon, topology and covariance are fixed below for
each estimator.

## Horizon

A finite horizon `[0, τ]`, `τ > 0`, **supported** in the sense that the risk set is non-empty up
to `τ`: for Nelson–Aalen in `D([0, τ])`, the probability of an empty risk set at some grid step of
`(0, τ]` tends to `0` (`hsupp`); for the grid statements, the grid `1, …, K` lies inside the
support (no hazard jump equals `1`, so `S > 0`, in the covariance theorems; positivity of the
limiting at-risk fractions is part of the Nelson–Aalen CLT hypothesis).

## Results, topology and covariance

* **Nelson–Aalen, `D([0, τ])` with the Skorokhod J1 topology**
  (`tendstoInDistribution_naErrorPath`, `tendstoInDistribution_naErrorPath_timeChangedBrownian`).
  A counting process `N n` with at-risk process `Y n` in Aalen's multiplicative model is observed on
  the grid of mesh `τ / K n`; `naErrorPath` is the càdlàg step path of `√n (Â_n - α_n)`
  (`gridPath`, `naErrorPath_apply_gridTime`). The limit `Z` is whatever the hypotheses `hfdd`
  and `htight` name. **If** `Z = B ∘ σ²` a.s. (hypothesis `hZB` of the corollary) for a Brownian
  motion `B` and a non-decreasing variance function `σ²`, then `Cov(Z s, Z t) = σ²(min s t)` and
  `Z t ~ N(0, σ²(t))` (`covariance_timeChangedBrownian`, `hasLaw_timeChangedBrownian`, from
  Mathlib's `IsPreBrownianReal.covariance_eval`). For Nelson–Aalen the classical
  identification `σ²(t) = ∫_0^t dΛ / y` is **not proved** here; it is part of the hypotheses.
  This is a conditional derivation (T43 transfer + T45 representation), not a Nelson–Aalen
  functional CLT: none of the martingale-CLT inputs are supplied by T43.
  What is derived: off the event of an empty risk set the error path *equals* the martingale path
  `√n (Y⁻¹ • M)` (`naErrorPath_eq_naMartingalePath`, from
  `nelsonAalenProcess_sub_restrictedHazard`), so the J1 limit of the martingale path (transfer
  theorem) passes to the estimator (converging together).
* **Kaplan–Meier, fixed supported grid, uniform (sup-norm) topology**
  (`tendstoInDistribution_kmGridVector`, `tendstoInDistribution_kmGridVector_greenwood`). The
  processes `j ↦ Â_{j+1}`, `j ↦ Ŝ_{j+1}` on the grid `1, …, K` live in `Fin K → ℝ` with the max
  norm, the uniform topology of the process restricted to the grid. `kmGridVector_eq_prodIntegral`
  identifies the counting-process Kaplan–Meier process with the `FunctionalDelta` product integral
  of the Nelson–Aalen increments, and the functional delta theorem gives the limit
  `-duhamelDeriv (-ΔΛ) (ΔG)`. Covariance (`covariance_naGridLimit`, `covariance_kmGridLimit`):
  if `G` has uncorrelated increments of variances `v`, then `Cov(G a, G b) = ∑_{i ≤ a ∧ b} v i` and
  the Kaplan–Meier limit has the **Greenwood covariance** `S_a S_b ∑_{i ≤ a ∧ b} v i / (1 - ΔΛ_i)²`.
* **Aalen–Johansen (competing risks), fixed supported grid, uniform topology**
  (`tendstoInDistribution_ajIncidence`, `tendstoInDistribution_cumulativeIncidence_grid`). The
  grid map `ajIncidence` from cause-specific hazard increments to cumulative incidences is the
  Aalen–Johansen estimator on grouped data (`cumulativeIncidence_time_eq_ajIncidence`); it is
  Fréchet differentiable with explicit derivative `ajDeriv` (`hasFDerivAt_ajIncidence`,
  `ajDeriv_apply`). Covariance (`covariance_ajLimit`): for an arbitrary covariance matrix `Γ`
  of the cause-specific limit `G`, `Cov = ∑_p ∑_q a(j, c; p) a(j', c'; q) Γ p q` with the explicit
  coefficients `a = ajDeriv x δ_p`. For grouped data with ties the cause-specific counts at one
  grid time are multinomial, so `Γ (i, c) (i', e) = δ_{i i'} (x i c δ_{c e} - x i c x i e) / y i`
  is not diagonal across causes.

## What is assumed, and what is not claimed

* **The martingale CLT is a hypothesis.** `FunctionalCLT` does not prove Rebolledo's theorem for
  martingales with random compensators. For Nelson–Aalen in `D([0, τ])` its conclusions enter as
  `htight`, `hfdd`, `hjump` on the martingale path `naMartingalePath`; the identification of the
  limit variance `σ²` with `∫ dΛ / y` is part of `hfdd`, not proved. For the grid statements the
  Nelson–Aalen CLT is the hypothesis `hCLT`.
* **The counting-process setup is explicit.** The continuous-time construction of counting and
  risk processes and their compensators (SURV-07.1) is not imported: the processes are arbitrary
  real sequences `N n k`, `Y n k` on a grid, measurability is a hypothesis, and the Aalen model
  enters only through the pathwise algebra of `StochasticIntegral` (no martingale property is
  used by the limit theorems).
* **Kaplan–Meier and Aalen–Johansen in `D([0, τ])` are not claimed**, in neither J1 nor the uniform
  topology. The continuous-time product-integral map is not proved Hadamard differentiable
  (`FunctionalDelta` proves only the grid version), J1 continuity of product integration is not
  available, and in `ℓ^∞([0, τ])` the Borel measurability required by the delta theorem fails
  for continuous-time Nelson–Aalen (see the module docstring of `FunctionalDelta`). Their
  limits are proved on a fixed grid only.
* The Nelson–Aalen `D([0, τ])` result uses a deterministic grid of mesh `τ / K n` (Aalen's model
  on a discretized time axis), not the observed event times.
* Gaussianity of the grid limits is not stated separately. The Kaplan–Meier covariance
  theorems assume uncorrelated Nelson–Aalen increments (true for the all-cause grid limit); the
  Aalen–Johansen covariance theorem takes a general covariance matrix of the cause-specific
  limit.

## Source receipt (reuse search, 2026-11-12)

Reused, not redefined: `SkorokhodSpace`, `stepInd`,
`tendstoInDistribution_skorokhod_of_tight_of_fdd`, `tendstoInDistribution_of_eventually_edist_le`
(T43); `functional_delta_of_continuous`,
`prodIntegral`, `duhamelDeriv`, `gridIncrements`, `hasFDerivAt_prodIntegral` (T44);
`nelsonAalenProcess`, `kaplanMeierProcess`, `aalenCompensator`, `restrictedHazard`,
`stochasticIntegral_jump`, `nelsonAalenProcess_sub_restrictedHazard` (T45);
`CompetingRiskData.cumulativeIncidence`; Mathlib's `IsPreBrownianReal`, `IsBrownianReal`,
`covariance`, `covariance_fun_sum_fun_sum'`. New here: the grid step path in `D([0, τ])` for a
general horizon (T43's `stepPath` is on `[0, 1]` with `√n` scaling), the Nelson–Aalen error and
martingale paths, the grid vectors, the Aalen–Johansen grid map and its derivative.

## References

* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), §II.5 (Rebolledo), Theorem IV.1.2 (Nelson–Aalen), §IV.3
  (Kaplan–Meier, Greenwood), §IV.4 (Aalen–Johansen).
* R. D. Gill, *Censoring and Stochastic Integrals*, Mathematical Centre Tracts 124 (1980).
* A. W. van der Vaart, *Asymptotic Statistics* (1998), Theorem 20.8, §20.3.
* P. Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999), §§3, 12.
-/

@[expose] public section

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology Finset
open MathlibExt.Probability.Martingale
open scoped ENNReal NNReal

namespace MathlibExt.Probability.Statistics.ProcessAsymptotics

noncomputable section

/-! ### Grid step paths in `D([0, τ])` -/

/-- Underlying function of the **grid step path** on `[0, τ]` with `K` equal steps and
increments `y : Fin K → ℝ`: `t ↦ ∑_{i < K} y i · 1{(i + 1) τ / K ≤ t}`. At the grid time
`k τ / K` it equals `∑_{i < k} y i` (`gridPath_apply_gridTime`). -/
def gridPathFun (τ : ℝ) (K : ℕ) (y : Fin K → ℝ) (t : Set.Icc (0 : ℝ) τ) : ℝ :=
  ∑ i : Fin K, y i * stepInd τ (((i : ℕ) + 1 : ℝ) * τ / K) t

/-- Grid step paths are càdlàg (finite sums of càdlàg unit steps). -/
theorem isCadlag_gridPathFun (τ : ℝ) (K : ℕ) (y : Fin K → ℝ) : IsCadlag (gridPathFun τ K y) := by
  have hsum : ∀ s : Finset (Fin K),
      IsCadlag (fun t => ∑ i ∈ s, y i * stepInd τ (((i : ℕ) + 1 : ℝ) * τ / K) t) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((isCadlag_stepInd τ _).continuous_comp (continuous_const_mul (y a))).add ih
  exact hsum Finset.univ

/-- The **grid step path** in `D([0, τ])`: the càdlàg pure-jump path that starts at `0` and
jumps by `y i` at the grid time `(i + 1) τ / K`. It embeds a discrete-time process observed on
the grid `0, τ / K, 2 τ / K, …, τ` into continuous time. -/
def gridPath (τ : ℝ) (K : ℕ) (y : Fin K → ℝ) : SkorokhodSpace τ :=
  SkorokhodSpace.mk (gridPathFun τ K y) (isCadlag_gridPathFun τ K y)

private lemma stepInd_nonneg' (τ c : ℝ) (t : Set.Icc (0 : ℝ) τ) : 0 ≤ stepInd τ c t := by
  unfold stepInd; split_ifs <;> norm_num

private lemma stepInd_le_one' (τ c : ℝ) (t : Set.Icc (0 : ℝ) τ) : stepInd τ c t ≤ 1 := by
  unfold stepInd; split_ifs <;> norm_num

/-- The grid step path map `ℝ^K → D([0, τ])` is `K`-Lipschitz from the sup norm to J1 (in fact
to the uniform distance). -/
theorem lipschitzWith_gridPath (τ : ℝ) (K : ℕ) : LipschitzWith (K : ℝ≥0) (gridPath τ K) := by
  intro y z
  refine (SkorokhodSpace.edist_le_iSup_edist _ _).trans (iSup_le fun t => ?_)
  simp only [gridPath, SkorokhodSpace.mk_apply, gridPathFun]
  rw [edist_dist, edist_dist, Real.dist_eq, ← Finset.sum_sub_distrib]
  rw [show ((K : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) by simp,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc |∑ i : Fin K, (y i * stepInd τ _ t - z i * stepInd τ _ t)|
      ≤ ∑ i : Fin K, dist y z := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [← sub_mul, abs_mul, abs_of_nonneg (stepInd_nonneg' _ _ _)]
        calc |y i - z i| * stepInd τ _ t ≤ |y i - z i| * 1 :=
              mul_le_mul_of_nonneg_left (stepInd_le_one' _ _ _) (abs_nonneg _)
          _ = dist (y i) (z i) := by rw [mul_one, Real.dist_eq]
          _ ≤ dist y z := dist_le_pi_dist y z i
    _ = (K : ℝ) * dist y z := by simp

/-- The grid step path map is continuous, hence Borel measurable. -/
theorem continuous_gridPath (τ : ℝ) (K : ℕ) : Continuous (gridPath τ K) :=
  (lipschitzWith_gridPath τ K).continuous

/-- The grid time `k τ / K ∈ [0, τ]` for `k ≤ K` and `τ ≥ 0`. -/
def gridTime {τ : ℝ} (hτ : 0 ≤ τ) (K k : ℕ) (hk : k ≤ K) : Set.Icc (0 : ℝ) τ :=
  ⟨k * τ / K, div_nonneg (mul_nonneg k.cast_nonneg hτ) K.cast_nonneg, by
    rcases Nat.eq_zero_or_pos K with rfl | hK
    · simp [hτ]
    · rw [div_le_iff₀ (by exact_mod_cast hK), mul_comm τ]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hτ⟩

/-- **Value at the grid times**: `gridPath τ K y (k τ / K) = ∑_{i < k} y i`. -/
theorem gridPath_apply_gridTime {τ : ℝ} (hτ : 0 < τ) (K : ℕ) (y : Fin K → ℝ) (k : ℕ)
    (hk : k ≤ K) :
    gridPath τ K y (gridTime hτ.le K k hk) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin K => (i : ℕ) < k), y i := by
  simp only [gridPath, SkorokhodSpace.mk_apply, gridPathFun, gridTime, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hK : (0 : ℝ) < K := by exact_mod_cast (Nat.zero_lt_of_lt i.2)
  have hiff : (((i : ℕ) : ℝ) + 1) * τ / K ≤ k * τ / K ↔ (i : ℕ) < k := by
    rw [div_le_div_iff_of_pos_right hK, mul_le_mul_iff_left₀ hτ, Nat.lt_iff_add_one_le]
    exact_mod_cast Iff.rfl
  simp only [stepInd, hiff]
  split_ifs <;> simp

/-! ### The Nelson–Aalen process in `D([0, τ])` with the Skorokhod J1 topology -/

section NelsonAalen

open MathlibExt.Probability.Statistics.CountingProcess

variable {Ω : Type*}

/-- The normalized **Nelson–Aalen error increment** over the grid step `(i, i + 1]`:
`√n (ΔÂ_{i+1} - Δα_{i+1})`, with `Â = nelsonAalenProcess N Y` and deterministic cumulative
hazard `α`. -/
def naErrorIncrement (n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  √(n : ℝ) * ((nelsonAalenProcess N Y (i + 1) ω - nelsonAalenProcess N Y i ω) -
    (α (i + 1) - α i))

/-- The normalized **Nelson–Aalen martingale increment** over the grid step `(i, i + 1]`:
`√n Y_{i+1}⁻¹ ΔM_{i+1}` with `M = N - ∫ Y dα` (`aalenCompensator`). It is the jump of the
stochastic integral `√n (Y⁻¹ • M)` (`stochasticIntegral_jump`). -/
def naMartingaleIncrement (n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  √(n : ℝ) * ((Y (i + 1) ω)⁻¹ *
    ((N (i + 1) ω - aalenCompensator Y α (i + 1) ω) - (N i ω - aalenCompensator Y α i ω)))

/-- **On the risk set the error increment is the martingale increment.** If somebody is at risk
at step `i + 1`, then `√n (ΔÂ - Δα) = √n Y⁻¹ ΔM`. This is the increment form of the pathwise
representation `Â - Λ* = Y⁻¹ • M` (`nelsonAalenProcess_sub_restrictedHazard`), together with
`ΔΛ* = Δα` on `{Y ≠ 0}`. -/
theorem naErrorIncrement_eq_naMartingaleIncrement {n : ℕ} {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    {i : ℕ} {ω : Ω} (h : Y (i + 1) ω ≠ 0) :
    naErrorIncrement n N Y α i ω = naMartingaleIncrement n N Y α i ω := by
  have h1 := nelsonAalenProcess_sub_restrictedHazard N Y α (i + 1) ω
  have h0 := nelsonAalenProcess_sub_restrictedHazard N Y α i ω
  have hj := stochasticIntegral_jump (fun k ω => (Y k ω)⁻¹)
    (fun k ω => N k ω - aalenCompensator Y α k ω) i ω
  have hr : restrictedHazard Y α (i + 1) ω - restrictedHazard Y α i ω = α (i + 1) - α i := by
    rw [restrictedHazard, stochasticIntegral_jump]
    simp [h]
  unfold naErrorIncrement naMartingaleIncrement
  congr 1
  linarith

/-- The normalized **Nelson–Aalen error path** `t ↦ √n (Â(t) - (α(t) - α(0)))` in `D([0, τ])`,
for a counting process observed on the grid with `K` steps of length `τ / K`
(`naErrorPath_apply_gridTime`). -/
def naErrorPath (τ : ℝ) (K n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (ω : Ω) : SkorokhodSpace τ :=
  gridPath τ K fun i => naErrorIncrement n N Y α i ω

/-- The normalized **Nelson–Aalen martingale path** `t ↦ √n (Y⁻¹ • M)(t)` in `D([0, τ])`. -/
def naMartingalePath (τ : ℝ) (K n : ℕ) (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (ω : Ω) :
    SkorokhodSpace τ :=
  gridPath τ K fun i => naMartingaleIncrement n N Y α i ω

/-- **On a supported horizon the error path is the martingale path**: if the risk set is
non-empty at every grid step of `(0, τ]`, the two paths coincide. -/
theorem naErrorPath_eq_naMartingalePath {τ : ℝ} {K n : ℕ} {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    {ω : Ω} (h : ∀ i < K, Y (i + 1) ω ≠ 0) :
    naErrorPath τ K n N Y α ω = naMartingalePath τ K n N Y α ω := by
  unfold naErrorPath naMartingalePath
  congr 1
  funext i
  exact naErrorIncrement_eq_naMartingaleIncrement (h i i.2)

private lemma sum_filter_fin_lt_eq_sum_range {K k : ℕ} (hk : k ≤ K) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin K => (i : ℕ) < k), g i = ∑ i ∈ range k, g i := by
  rw [Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < k then g i else 0) K,
    ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- **The error path at the grid times**:
`naErrorPath τ K n N Y α ω (k τ / K) = √n (Â_k - (α_k - α_0))`. -/
theorem naErrorPath_apply_gridTime {τ : ℝ} (hτ : 0 < τ) (K n : ℕ) (N Y : ℕ → Ω → ℝ)
    (α : ℕ → ℝ) (ω : Ω) (k : ℕ) (hk : k ≤ K) :
    naErrorPath τ K n N Y α ω (gridTime hτ.le K k hk) =
      √(n : ℝ) * (nelsonAalenProcess N Y k ω - (α k - α 0)) := by
  rw [naErrorPath, gridPath_apply_gridTime hτ,
    sum_filter_fin_lt_eq_sum_range hk (fun i => naErrorIncrement n N Y α i ω)]
  simp only [naErrorIncrement, ← Finset.mul_sum, Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun i => nelsonAalenProcess N Y i ω),
    Finset.sum_range_sub (fun i => α i)]
  simp [nelsonAalenProcess, stochasticIntegral]

variable [MeasurableSpace Ω]

/-- The Nelson–Aalen process is measurable when `N` and `Y` are. -/
theorem measurable_nelsonAalenProcess {N Y : ℕ → Ω → ℝ} (hN : ∀ k, Measurable (N k))
    (hY : ∀ k, Measurable (Y k)) (k : ℕ) : Measurable (nelsonAalenProcess N Y k) := by
  unfold nelsonAalenProcess stochasticIntegral
  exact Finset.measurable_fun_sum _ fun j _ => (hY _).inv.mul ((hN _).sub (hN _))

/-- The Aalen compensator is measurable when `Y` is. -/
theorem measurable_aalenCompensator {Y : ℕ → Ω → ℝ} (hY : ∀ k, Measurable (Y k)) (α : ℕ → ℝ)
    (k : ℕ) : Measurable (aalenCompensator Y α k) := by
  unfold aalenCompensator stochasticIntegral
  exact Finset.measurable_fun_sum _ fun j _ => (hY _).mul measurable_const

/-- The Nelson–Aalen error path is a measurable `D([0, τ])`-valued random variable. -/
theorem measurable_naErrorPath (τ : ℝ) (K n : ℕ) {N Y : ℕ → Ω → ℝ} (α : ℕ → ℝ)
    (hN : ∀ k, Measurable (N k)) (hY : ∀ k, Measurable (Y k)) :
    Measurable (naErrorPath τ K n N Y α) :=
  (continuous_gridPath τ K).measurable.comp <| measurable_pi_iff.2 fun _ =>
    measurable_const.mul (((measurable_nelsonAalenProcess hN hY _).sub
      (measurable_nelsonAalenProcess hN hY _)).sub measurable_const)

/-- The Nelson–Aalen martingale path is a measurable `D([0, τ])`-valued random variable. -/
theorem measurable_naMartingalePath (τ : ℝ) (K n : ℕ) {N Y : ℕ → Ω → ℝ} (α : ℕ → ℝ)
    (hN : ∀ k, Measurable (N k)) (hY : ∀ k, Measurable (Y k)) :
    Measurable (naMartingalePath τ K n N Y α) :=
  (continuous_gridPath τ K).measurable.comp <| measurable_pi_iff.2 fun _ =>
    measurable_const.mul ((hY _).inv.mul (((hN _).sub (measurable_aalenCompensator hY α _)).sub
      ((hN _).sub (measurable_aalenCompensator hY α _))))

end NelsonAalen

/-! ### The limit: a time-changed Brownian motion, and the J1 limit theorem -/

section Limit

open MathlibExt.Probability.Statistics.CountingProcess

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P'] in
private lemma covariance_congr_ae {X X' Y Y' : Ω' → ℝ} (hX : X =ᵐ[P'] X') (hY : Y =ᵐ[P'] Y') :
    cov[X, Y; P'] = cov[X', Y'; P'] := by
  unfold covariance
  rw [integral_congr_ae hX, integral_congr_ae hY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2; rw [h1, h2])

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P'] in
/-- **Covariance of the Gaussian-martingale limit.** If the paths of `Z` are a.s. those of the
time-changed Brownian motion `t ↦ B (σ² t)` with a non-decreasing variance function `σ²`, then
`Cov(Z s, Z t) = σ²(min s t)`. For the Nelson–Aalen estimator the classical variance function is
`σ²(t) = ∫_0^t dΛ / y` (continuous `Λ`, limiting at-risk fraction `y`;
Andersen–Borgan–Gill–Keiding (1993), Theorem IV.1.2); that identification is not proved here. -/
theorem covariance_timeChangedBrownian {τ : ℝ} {B : ℝ≥0 → Ω' → ℝ} (hB : IsPreBrownianReal B P')
    {σsq : Set.Icc (0 : ℝ) τ → ℝ≥0} (hσ : Monotone σsq) {Z : Ω' → C(Set.Icc (0 : ℝ) τ, ℝ)}
    (hZB : ∀ᵐ ω' ∂P', ∀ t, Z ω' t = B (σsq t) ω') (s t : Set.Icc (0 : ℝ) τ) :
    cov[fun ω' => Z ω' s, fun ω' => Z ω' t; P'] = σsq (min s t) := by
  rw [covariance_congr_ae (X' := B (σsq s)) (Y' := B (σsq t))
    (by filter_upwards [hZB] with ω h using h s) (by filter_upwards [hZB] with ω h using h t),
    hB.covariance_eval, hσ.map_min]

omit [IsProbabilityMeasure P] [IsProbabilityMeasure P'] in
/-- **Marginal law of the Gaussian-martingale limit**: `Z t ~ N(0, σ²(t))`. -/
theorem hasLaw_timeChangedBrownian {τ : ℝ} {B : ℝ≥0 → Ω' → ℝ} (hB : IsPreBrownianReal B P')
    {σsq : Set.Icc (0 : ℝ) τ → ℝ≥0} {Z : Ω' → C(Set.Icc (0 : ℝ) τ, ℝ)}
    (hZB : ∀ᵐ ω' ∂P', ∀ t, Z ω' t = B (σsq t) ω') (t : Set.Icc (0 : ℝ) τ) :
    HasLaw (fun ω' => Z ω' t) (gaussianReal 0 (σsq t)) P' :=
  (hB.hasLaw_eval (σsq t)).congr (by filter_upwards [hZB] with ω h using h t)

/-- **Nelson–Aalen limit in `D([0, τ])`, Skorokhod J1 topology, conditional on the martingale
CLT.** This is not a Nelson–Aalen functional CLT: the martingale-CLT conclusions are hypotheses.

Setting: for each sample size `n`, a counting process `N n` and an at-risk process `Y n` are
observed on the grid `0, τ / K n, 2 τ / K n, …, τ` of the supported horizon `[0, τ]`, with
deterministic cumulative hazard `α n` on that grid. The error path is
`√n (Â_n(t) - (α_n(t) - α_n(0)))` (`naErrorPath`, `naErrorPath_apply_gridTime`).

Hypotheses (the counting-process / martingale-CLT setup, taken explicitly):
* `hsupp` (**supported horizon**): the probability that the risk set is empty at some grid step
  of `(0, τ]` tends to `0` (e.g. `Y n (K n) / n → y(τ) > 0` in probability);
* `htight`, `hfdd`, `hjump`: the conclusions of Rebolledo's martingale CLT for the normalized
  Nelson–Aalen martingale path `√n (Y⁻¹ • M)` (`naMartingalePath`), in the form consumed by
  `tendstoInDistribution_skorokhod_of_tight_of_fdd`: continuous companions `V n` with tight laws
  and finite-dimensional convergence to `Z`, uniformly close to the martingale path.

Conclusion: the error path converges in distribution to `Z` in `D([0, τ])` with the J1 topology.

Derivation: the transfer theorem gives J1 convergence of the martingale path; off the event of an
empty risk set the error path equals the martingale path (`naErrorPath_eq_naMartingalePath`,
from the representation `Â - Λ* = Y⁻¹ • M`), so converging together
(`tendstoInDistribution_of_eventually_edist_le`) transfers the limit. With `Z = B ∘ σ²`, see
`tendstoInDistribution_naErrorPath_timeChangedBrownian` for the covariance. -/
theorem tendstoInDistribution_naErrorPath {τ : ℝ} (hτ : 0 < τ) (K : ℕ → ℕ)
    (N Y : ℕ → ℕ → Ω → ℝ) (α : ℕ → ℕ → ℝ)
    (hN : ∀ n k, Measurable (N n k)) (hY : ∀ n k, Measurable (Y n k))
    (hsupp : Tendsto (fun n => P.real {ω | ∃ i < K n, Y n (i + 1) ω = 0}) atTop (𝓝 0))
    (V : ℕ → Ω → C(Set.Icc (0 : ℝ) τ, ℝ)) (Z : Ω' → C(Set.Icc (0 : ℝ) τ, ℝ))
    (hV : ∀ n, AEMeasurable (V n) P) (hZ : AEMeasurable Z P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map (V n)))
    (hfdd : ∀ I : Finset (Set.Icc (0 : ℝ) τ),
      TendstoInDistribution (fun n ω => I.restrict (fun t => V n ω t)) atTop
        (fun ω => I.restrict (fun t => Z ω t)) (fun _ => P) P')
    (hjump : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => P.real (A n)) atTop (𝓝 0) ∧
      ∀ n, ∀ ω ∉ A n, ∀ t, |naMartingalePath τ (K n) n (N n) (Y n) (α n) ω t - V n ω t| ≤ ε) :
    TendstoInDistribution (fun n => naErrorPath τ (K n) n (N n) (Y n) (α n)) atTop
      (fun ω' => SkorokhodSpace.ofContinuous (Z ω')) (fun _ => P) P' := by
  have hM := tendstoInDistribution_skorokhod_of_tight_of_fdd hτ
    (fun n => naMartingalePath τ (K n) n (N n) (Y n) (α n)) V Z
    (fun n => (measurable_naMartingalePath τ (K n) n (α n) (hN n) (hY n)).aemeasurable)
    hV hZ htight hfdd hjump
  refine tendstoInDistribution_of_eventually_edist_le _ _ _ hM
    (fun n => (measurable_naErrorPath τ (K n) n (α n) (hN n) (hY n)).aemeasurable) ?_
  intro ε _
  refine ⟨fun n => {ω | ∃ i < K n, Y n (i + 1) ω = 0}, fun n => ?_, hsupp, fun n ω hω => ?_⟩
  · dsimp only
    have hset : {ω | ∃ i < K n, Y n (i + 1) ω = 0} =
        ⋃ i ∈ Finset.range (K n), Y n (i + 1) ⁻¹' {0} := by
      ext ω; simp
    rw [hset]
    exact Finset.measurableSet_biUnion _ fun i _ => hY n (i + 1) (measurableSet_singleton 0)
  · simp only [Set.mem_ofPred_eq, not_exists, not_and] at hω
    rw [naErrorPath_eq_naMartingalePath hω, edist_self]
    exact bot_le

/-- **Nelson–Aalen J1 limit with an explicit Gaussian-martingale limit (conditional).** Under the
hypotheses of `tendstoInDistribution_naErrorPath` (which include the martingale-CLT inputs), if
the limit `Z` is a continuous version of the time-changed Brownian motion `t ↦ B (σ² t)` (`hZB`,
`σ²` non-decreasing; the Nelson–Aalen identification `σ²(t) = ∫_0^t dΛ / y` is not proved here
and enters only through `hfdd` and `hZB`), then
* `√n (Â_n - α_n) → Z` in distribution in `D([0, τ])` with the J1 topology;
* `Cov(Z s, Z t) = σ²(min s t)` (independent increments, variance function `σ²`);
* `Z t ~ N(0, σ²(t))`. -/
theorem tendstoInDistribution_naErrorPath_timeChangedBrownian {τ : ℝ} (hτ : 0 < τ)
    (K : ℕ → ℕ) (N Y : ℕ → ℕ → Ω → ℝ) (α : ℕ → ℕ → ℝ)
    (hN : ∀ n k, Measurable (N n k)) (hY : ∀ n k, Measurable (Y n k))
    (hsupp : Tendsto (fun n => P.real {ω | ∃ i < K n, Y n (i + 1) ω = 0}) atTop (𝓝 0))
    (V : ℕ → Ω → C(Set.Icc (0 : ℝ) τ, ℝ)) (Z : Ω' → C(Set.Icc (0 : ℝ) τ, ℝ))
    (hV : ∀ n, AEMeasurable (V n) P) (hZ : AEMeasurable Z P')
    (htight : IsTightMeasureSet (Set.range fun n => P.map (V n)))
    (hfdd : ∀ I : Finset (Set.Icc (0 : ℝ) τ),
      TendstoInDistribution (fun n ω => I.restrict (fun t => V n ω t)) atTop
        (fun ω => I.restrict (fun t => Z ω t)) (fun _ => P) P')
    (hjump : ∀ ε : ℝ, 0 < ε → ∃ A : ℕ → Set Ω, (∀ n, MeasurableSet (A n)) ∧
      Tendsto (fun n => P.real (A n)) atTop (𝓝 0) ∧
      ∀ n, ∀ ω ∉ A n, ∀ t, |naMartingalePath τ (K n) n (N n) (Y n) (α n) ω t - V n ω t| ≤ ε)
    {B : ℝ≥0 → Ω' → ℝ} (hB : IsBrownianReal B P') {σsq : Set.Icc (0 : ℝ) τ → ℝ≥0}
    (hσ : Monotone σsq) (hZB : ∀ᵐ ω' ∂P', ∀ t, Z ω' t = B (σsq t) ω') :
    TendstoInDistribution (fun n => naErrorPath τ (K n) n (N n) (Y n) (α n)) atTop
        (fun ω' => SkorokhodSpace.ofContinuous (Z ω')) (fun _ => P) P' ∧
      (∀ s t, cov[fun ω' => Z ω' s, fun ω' => Z ω' t; P'] = σsq (min s t)) ∧
      ∀ t, HasLaw (fun ω' => Z ω' t) (gaussianReal 0 (σsq t)) P' :=
  ⟨tendstoInDistribution_naErrorPath hτ K N Y α hN hY hsupp V Z hV hZ htight hfdd hjump,
    covariance_timeChangedBrownian hB.toIsPreBrownianReal hσ hZB,
    hasLaw_timeChangedBrownian hB.toIsPreBrownianReal hZB⟩

end Limit

/-! ### Covariance of linear images of uncorrelated coordinates -/

section CovarianceHelper

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- Covariance of two linear combinations of uncorrelated coordinates `W i` with variances
`v i`: `Cov(∑_{i ∈ s} c i W i, ∑_{i ∈ t} d i W i) = ∑_{i ∈ s ∩ t} c i d i v i`. -/
theorem covariance_sum_uncorrelated {ι : Type*} [DecidableEq ι] (W : Ω' → ι → ℝ) (v : ι → ℝ)
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 P')
    (hcov : ∀ i i', cov[fun ω => W ω i, fun ω => W ω i'; P'] = if i = i' then v i else 0)
    (s t : Finset ι) (c d : ι → ℝ) :
    cov[fun ω => ∑ i ∈ s, c i * W ω i, fun ω => ∑ i ∈ t, d i * W ω i; P'] =
      ∑ i ∈ s ∩ t, c i * d i * v i := by
  rw [covariance_fun_sum_fun_sum' (X := fun i ω => c i * W ω i) (Y := fun i ω => d i * W ω i)
    (fun i _ => (hW i).const_mul (c i)) (fun i _ => (hW i).const_mul (d i))]
  have hinner : ∀ i, ∑ j ∈ t, cov[fun ω => c i * W ω i, fun ω => d j * W ω j; P'] =
      if i ∈ t then c i * d i * v i else 0 := by
    intro i
    simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
    split_ifs with hi
    · rw [Finset.sum_eq_single i (fun j _ hji => by simp [Ne.symm hji])
        (fun h => absurd hi h)]
      simp only [↓reduceIte]
      ring
    · exact Finset.sum_eq_zero fun j hj => by
        have : i ≠ j := fun h => hi (h ▸ hj)
        simp [this]
  rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.sum_filter, Finset.filter_mem_eq_inter]

end CovarianceHelper

/-! ### Nelson–Aalen and Kaplan–Meier processes on a supported grid: uniform topology -/

section KaplanMeierGrid

open MathlibExt.Probability.Statistics.CountingProcess

variable {Ω : Type*} {K : ℕ}

/-- The **Nelson–Aalen process on the grid** `1, …, K`: `j ↦ Â_{j+1}`, as a vector of
`Fin K → ℝ` (sup norm, i.e. the uniform topology of the process on the grid). -/
def naGridVector (K : ℕ) (N Y : ℕ → Ω → ℝ) (ω : Ω) : Fin K → ℝ :=
  fun j => nelsonAalenProcess N Y (j + 1) ω

/-- The **Kaplan–Meier process on the grid** `1, …, K`: `j ↦ Ŝ_{j+1}`. -/
def kmGridVector (K : ℕ) (N Y : ℕ → Ω → ℝ) (ω : Ω) : Fin K → ℝ :=
  fun j => kaplanMeierProcess N Y (j + 1) ω

/-- The grid increments of the Nelson–Aalen vector are the Nelson–Aalen jumps
`Â_{j+1} - Â_j` (with `Â_0 = 0`). -/
theorem gridIncrements_naGridVector (N Y : ℕ → Ω → ℝ) (ω : Ω) (j : Fin K) :
    FunctionalDelta.gridIncrements (naGridVector K N Y ω) j =
      nelsonAalenProcess N Y (j + 1) ω - nelsonAalenProcess N Y j ω := by
  rw [FunctionalDelta.gridIncrements_apply]
  split_ifs with hj
  · simp only [naGridVector]
    congr 3
    omega
  · have hj0 : (j : ℕ) = 0 := by omega
    simp [naGridVector, hj0, nelsonAalenProcess, stochasticIntegral]

/-- **Kaplan–Meier is the grid product integral of the Nelson–Aalen process**:
`Ŝ_{j+1} = ∏_{i ≤ j} (1 - ΔÂ_{i+1})`, i.e. `kmGridVector = prodIntegral (-ΔÂ)` with the
`FunctionalDelta` grid product integral. This bridges the counting-process objects of
`StochasticIntegral` to the delta-method map of `FunctionalDelta`. -/
theorem kmGridVector_eq_prodIntegral (N Y : ℕ → Ω → ℝ) (ω : Ω) :
    kmGridVector K N Y ω =
      FunctionalDelta.prodIntegral (-FunctionalDelta.gridIncrements (naGridVector K N Y ω)) := by
  funext j
  simp only [kmGridVector, kaplanMeierProcess, CountingProcess.prodIntegral,
    FunctionalDelta.prodIntegral, Pi.neg_apply, gridIncrements_naGridVector, ← sub_eq_add_neg]
  rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.prod_map]
  rfl

variable {Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- **Kaplan–Meier process limit on a supported grid (uniform topology).** Fix the grid
`1, …, K` inside the supported horizon. If the Nelson–Aalen process satisfies the functional CLT
`√n (Â_n - Λ) ⇒ G` in `Fin K → ℝ` with the sup norm (`hCLT`, the explicit counting-process CLT
hypothesis), then the Kaplan–Meier process satisfies
`√n (Ŝ_n - S) ⇒ -duhamelDeriv (-ΔΛ) (ΔG)` with `S = prodIntegral (-ΔΛ)`; coordinatewise the
limit is `-∑_{i ≤ j} S_{i-1} ΔG_i ∏_{i < l ≤ j} (1 - ΔΛ_l)`, which is `-S_j ∑_{i ≤ j} ΔG_i /
(1 - ΔΛ_i)` when no hazard jump is `1`. Proof: the functional delta theorem for the Fréchet
differentiable grid product integral, composed with the increment map. -/
theorem tendstoInDistribution_kmGridVector (N Y : ℕ → ℕ → Ω → ℝ) {Λ : Fin K → ℝ}
    {G : Ω' → Fin K → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (naGridVector K (N n) (Y n) ω - Λ)) atTop G
      (fun _ => P) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (kmGridVector K (N n) (Y n) ω -
        FunctionalDelta.prodIntegral (-FunctionalDelta.gridIncrements Λ))) atTop
      (fun ω => -FunctionalDelta.duhamelDeriv (-FunctionalDelta.gridIncrements Λ)
        (FunctionalDelta.gridIncrements (G ω))) (fun _ => P) P' := by
  set Δ := (FunctionalDelta.gridIncrements : (Fin K → ℝ) →L[ℝ] (Fin K → ℝ)) with hΔ
  set φ : (Fin K → ℝ) → Fin K → ℝ := fun x => FunctionalDelta.prodIntegral (-Δ x) with hφ
  have hφd : HasFDerivAt φ ((FunctionalDelta.duhamelDeriv (-Δ Λ)).comp (-Δ)) Λ :=
    HasFDerivAt.comp (g := FunctionalDelta.prodIntegral) Λ
      (FunctionalDelta.hasFDerivAt_prodIntegral (-Δ Λ)) Δ.hasFDerivAt.neg
  have hr : Tendsto (fun n : ℕ => √(n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have key := hCLT.functional_delta_of_continuous hr
    (hφd.hasHadamardDerivWithinAt Set.univ Set.univ) (fun _ => ae_of_all _ fun _ => trivial)
    (ae_of_all _ fun _ => trivial)
    (FunctionalDelta.continuous_prodIntegral.comp (Δ.continuous.neg))
    (ContinuousLinearMap.continuous _)
  refine key.congr (fun n => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
  · simp only [hφ, hΔ, kmGridVector_eq_prodIntegral]
  · simp

/-! #### Explicit covariance: Greenwood form -/

private lemma Iic_inter_Iic' (a b : Fin K) : Iic a ∩ Iic b = Iic (min a b) := by
  ext l
  simp

private lemma erase_Iic' {i j : Fin K} (hij : i ≤ j) : (Iic j).erase i = Iio i ∪ Ioc i j := by
  ext l
  simp only [mem_erase, mem_Iic, mem_union, mem_Iio, mem_Ioc]
  constructor
  · rintro ⟨hne, hl⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hl⟩
  · rintro (h | h)
    · exact ⟨h.ne, h.le.trans hij⟩
    · exact ⟨h.1.ne', h.2⟩

/-- **Closed form of the Kaplan–Meier limit functional**: if no factor `1 + x i` vanishes,
`(-duhamelDeriv x h) j = ∑_{i ≤ j} -(S_j / (1 + x i)) h i` with `S = prodIntegral x`. With
`x = -ΔΛ` this is `-S_j ∑_{i ≤ j} h i / (1 - ΔΛ_i)`. -/
theorem neg_duhamelDeriv_apply_eq_sum (x h : Fin K → ℝ) (hx : ∀ i, 1 + x i ≠ 0) (j : Fin K) :
    (-FunctionalDelta.duhamelDeriv x h) j =
      ∑ i ∈ Iic j, -(FunctionalDelta.prodIntegral x j / (1 + x i)) * h i := by
  rw [Pi.neg_apply, FunctionalDelta.duhamelDeriv_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hij : i ≤ j := Finset.mem_Iic.1 hi
  have hsplit : FunctionalDelta.prodIntegral x j =
      (1 + x i) * ((∏ l ∈ Iio i, (1 + x l)) * ∏ l ∈ Ioc i j, (1 + x l)) := by
    rw [FunctionalDelta.prodIntegral, ← Finset.mul_prod_erase _ _ hi, erase_Iic' hij,
      Finset.prod_union (disjoint_left.2 fun l hl hl' => (mem_Iio.1 hl).not_gt (mem_Ioc.1 hl').1)]
  rw [hsplit]
  field_simp [hx i]

/-- **Covariance of the Nelson–Aalen grid limit**: if the limit `G` has uncorrelated
increments `W` with variances `v` (`G j = ∑_{i ≤ j} W i`), then `Cov(G a, G b) = ∑_{i ≤ min a b} v
i`, the grid form of `σ²(min s t)`. For the discrete-hazard Nelson–Aalen estimator
`v i = ΔΛ_i (1 - ΔΛ_i) / y_i` (`HasUnitJumps.predictableQuadraticVariation_martingalePart`). -/
theorem covariance_naGridLimit (W : Ω' → Fin K → ℝ) (v : Fin K → ℝ)
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 P')
    (hcov : ∀ i i', cov[fun ω => W ω i, fun ω => W ω i'; P'] = if i = i' then v i else 0)
    (a b : Fin K) :
    cov[fun ω => ∑ i ∈ Iic a, W ω i, fun ω => ∑ i ∈ Iic b, W ω i; P'] =
      ∑ i ∈ Iic (min a b), v i := by
  have h := covariance_sum_uncorrelated W v hW hcov (Iic a) (Iic b) 1 1
  simp only [Pi.one_apply, one_mul, mul_one] at h
  rw [h, Iic_inter_Iic']

/-- **Greenwood covariance of the Kaplan–Meier grid limit.** If the Nelson–Aalen limit has
uncorrelated increments `W` with variances `v`, and no hazard jump equals `1`, the Kaplan–Meier
limit `-duhamelDeriv (-ΔΛ) W` has covariance
`Cov(a, b) = S_a S_b ∑_{i ≤ min a b} v i / (1 - ΔΛ_i)²`, `S = prodIntegral (-ΔΛ)`; with
`v i = ΔΛ_i (1 - ΔΛ_i) / y_i` this is Greenwood's `S_a S_b ∑ ΔΛ_i / (y_i (1 - ΔΛ_i))`. -/
theorem covariance_kmGridLimit (Λ : Fin K → ℝ) (W : Ω' → Fin K → ℝ) (v : Fin K → ℝ)
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 P')
    (hcov : ∀ i i', cov[fun ω => W ω i, fun ω => W ω i'; P'] = if i = i' then v i else 0)
    (hΛ : ∀ i, FunctionalDelta.gridIncrements Λ i ≠ 1) (a b : Fin K) :
    cov[fun ω => (-FunctionalDelta.duhamelDeriv (-FunctionalDelta.gridIncrements Λ) (W ω)) a,
      fun ω => (-FunctionalDelta.duhamelDeriv (-FunctionalDelta.gridIncrements Λ) (W ω)) b; P'] =
      FunctionalDelta.prodIntegral (-FunctionalDelta.gridIncrements Λ) a *
        FunctionalDelta.prodIntegral (-FunctionalDelta.gridIncrements Λ) b *
        ∑ i ∈ Iic (min a b), v i / (1 - FunctionalDelta.gridIncrements Λ i) ^ 2 := by
  set x := -FunctionalDelta.gridIncrements Λ with hx_def
  have hx : ∀ i, 1 + x i ≠ 0 := fun i => by
    simp only [hx_def, Pi.neg_apply, ← sub_eq_add_neg]
    exact sub_ne_zero.2 (hΛ i).symm
  simp_rw [neg_duhamelDeriv_apply_eq_sum x _ hx]
  rw [covariance_sum_uncorrelated W v hW hcov, Iic_inter_Iic', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : 1 + x i = 1 - FunctionalDelta.gridIncrements Λ i := by
    simp [hx_def, sub_eq_add_neg]
  have hne : 1 + x i ≠ 0 := hx i
  rw [h1] at hne ⊢
  field_simp

/-- **Kaplan–Meier and Nelson–Aalen grid limits with explicit covariance.** Under the
Nelson–Aalen functional CLT `√n (Â_n - Λ) ⇒ G` on the supported grid (`hCLT`), with `G` the
cumulative sum of uncorrelated increments `W` of variances `v` (the Gaussian-martingale structure
of the limit) and no hazard jump equal to `1`:
* `√n (Ŝ_n - S) ⇒ -duhamelDeriv (-ΔΛ) W` in `Fin K → ℝ` (uniform topology on the grid);
* `Cov(G a, G b) = ∑_{i ≤ min a b} v i`;
* the Kaplan–Meier limit has the Greenwood covariance
  `S_a S_b ∑_{i ≤ min a b} v i / (1 - ΔΛ_i)²`. -/
theorem tendstoInDistribution_kmGridVector_greenwood (N Y : ℕ → ℕ → Ω → ℝ) {Λ : Fin K → ℝ}
    {G W : Ω' → Fin K → ℝ} (v : Fin K → ℝ)
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (naGridVector K (N n) (Y n) ω - Λ)) atTop G
      (fun _ => P) P')
    (hGW : ∀ ω j, G ω j = ∑ i ∈ Iic j, W ω i) (hW : ∀ i, MemLp (fun ω => W ω i) 2 P')
    (hcov : ∀ i i', cov[fun ω => W ω i, fun ω => W ω i'; P'] = if i = i' then v i else 0)
    (hΛ : ∀ i, FunctionalDelta.gridIncrements Λ i ≠ 1) :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) • (kmGridVector K (N n) (Y n) ω -
        FunctionalDelta.prodIntegral (-FunctionalDelta.gridIncrements Λ))) atTop
      (fun ω => -FunctionalDelta.duhamelDeriv (-FunctionalDelta.gridIncrements Λ) (W ω))
      (fun _ => P) P' ∧
    (∀ a b, cov[fun ω => G ω a, fun ω => G ω b; P'] = ∑ i ∈ Iic (min a b), v i) ∧
    ∀ a b,
      cov[fun ω => (-FunctionalDelta.duhamelDeriv (-FunctionalDelta.gridIncrements Λ) (W ω)) a,
        fun ω => (-FunctionalDelta.duhamelDeriv (-FunctionalDelta.gridIncrements Λ) (W ω)) b;
        P'] =
      FunctionalDelta.prodIntegral (-FunctionalDelta.gridIncrements Λ) a *
        FunctionalDelta.prodIntegral (-FunctionalDelta.gridIncrements Λ) b *
        ∑ i ∈ Iic (min a b), v i / (1 - FunctionalDelta.gridIncrements Λ i) ^ 2 := by
  have hG : ∀ ω, G ω = fun j => ∑ i ∈ Iic j, W ω i := fun ω => funext (hGW ω)
  have hΔG : ∀ ω, FunctionalDelta.gridIncrements (G ω) = W ω := fun ω => by
    rw [hG ω, FunctionalDelta.gridIncrements_cumsum]
  refine ⟨?_, fun a b => ?_, covariance_kmGridLimit Λ W v hW hcov hΛ⟩
  · simpa only [hΔG] using tendstoInDistribution_kmGridVector N Y hCLT
  · simp_rw [hGW]
    exact covariance_naGridLimit W v hW hcov a b

end KaplanMeierGrid

/-! ### Aalen–Johansen cumulative incidence on a supported grid: uniform topology -/

section AalenJohansenGrid

open MathlibExt.Probability.Statistics.CompetingRisks
  MathlibExt.Probability.Statistics.KaplanMeier

variable {K r : ℕ}

/-- The **Aalen–Johansen cumulative-incidence map on a fixed grid** (competing risks, one
transient state, `r` absorbing causes). From cause-specific hazard increments `x i c` at the grid
times, `ajIncidence x j c = ∑_{i ≤ j} S_{i-1} x i c` with the all-cause survival
`S_{i-1} = ∏_{l < i} (1 - ∑_e x l e)`. With `x i c = d_{i,c} / Y_i` it is the Aalen–Johansen
estimate (`cumulativeIncidence_time_eq_ajIncidence`). -/
def ajIncidence (x : Fin K → Fin r → ℝ) (j : Fin K) (c : Fin r) : ℝ :=
  ∑ i ∈ Iic j, (∏ l ∈ Iio i, (1 - ∑ e, x l e)) * x i c

/-- **The Aalen–Johansen estimate is the grid map of the cause-specific Nelson–Aalen
increments**: `F̂_c(t_j) = ajIncidence (d / Y) j c`. -/
theorem cumulativeIncidence_time_eq_ajIncidence (D : CompetingRiskData K r) (j : Fin K)
    (c : Fin r) :
    D.cumulativeIncidence c (D.time j) =
      ajIncidence (fun i e => (D.events i e : ℝ) / D.atRisk i) j c := by
  have hfilt : univ.filter (fun l => D.time l ≤ D.time j) = Iic j := by
    ext l
    simp [D.strictMono_time.le_iff_le]
  have hlt : ∀ i : Fin K, univ.filter (fun l => l < i) = Iio i := fun i => by
    ext l
    simp
  rw [CompetingRiskData.cumulativeIncidence, hfilt, ajIncidence]
  refine sum_congr rfl fun i _ => ?_
  rw [CompetingRiskData.cifIncrement, CompetingRiskData.survivalBefore, hlt]
  congr 1
  refine prod_congr rfl fun l _ => ?_
  simp [CensoredData.kmFactor, CompetingRiskData.totalEvents, Finset.sum_div]

/-- The coordinate functional `y ↦ y i c` on `Fin K → Fin r → ℝ`. -/
def ajCoord (i : Fin K) (c : Fin r) : (Fin K → Fin r → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin r => ℝ) c).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin K => Fin r → ℝ) i)

/-- Evaluation of `ajCoord`. -/
@[simp] theorem ajCoord_apply (i : Fin K) (c : Fin r) (y : Fin K → Fin r → ℝ) :
    ajCoord i c y = y i c := rfl

/-- The derivative of `ajIncidence` at `x`:
`ajDeriv x h j c = ∑_{i ≤ j} (S_{i-1} h i c - x i c ∑_{m < i} (∏_{l < i, l ≠ m} (1 - ∑_e x l e))
∑_e h m e)` (`ajDeriv_apply`): the first term perturbs the cause-`c` hazard, the second the
all-cause survival `S_{i-1}`. This is the grid form of the Aalen–Johansen functional derivative
(Andersen–Borgan–Gill–Keiding (1993), §IV.4). -/
def ajDeriv (x : Fin K → Fin r → ℝ) : (Fin K → Fin r → ℝ) →L[ℝ] (Fin K → Fin r → ℝ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun c => ∑ i ∈ Iic j,
    ((∏ l ∈ Iio i, (1 - ∑ e, x l e)) • ajCoord i c -
      x i c • ∑ m ∈ Iio i, (∏ l ∈ (Iio i).erase m, (1 - ∑ e, x l e)) • ∑ e, ajCoord m e)

/-- Coordinates of `ajDeriv`. -/
theorem ajDeriv_apply (x h : Fin K → Fin r → ℝ) (j : Fin K) (c : Fin r) :
    ajDeriv x h j c = ∑ i ∈ Iic j, ((∏ l ∈ Iio i, (1 - ∑ e, x l e)) * h i c -
      x i c * ∑ m ∈ Iio i, (∏ l ∈ (Iio i).erase m, (1 - ∑ e, x l e)) * ∑ e, h m e) := by
  simp [ajDeriv, Finset.mul_sum]

/-- The Aalen–Johansen grid map is Fréchet differentiable, with derivative `ajDeriv`. -/
theorem hasFDerivAt_ajIncidence (x : Fin K → Fin r → ℝ) :
    HasFDerivAt ajIncidence (ajDeriv x) x := by
  refine hasFDerivAt_pi'.2 fun j => hasFDerivAt_pi'.2 fun c => ?_
  set L : Fin K → (Fin K → Fin r → ℝ) →L[ℝ] ℝ := fun l => ∑ e, ajCoord l e with hL
  have hLapply : ∀ l y, L l y = ∑ e, y l e := fun l y => by
    simp [hL]
  have hg : ∀ l, HasFDerivAt (fun y : Fin K → Fin r → ℝ => 1 - ∑ e, y l e) (-L l) x := by
    intro l
    have h := ((L l).hasFDerivAt (x := x)).const_sub 1
    simp only [hLapply] at h
    exact h
  have hP : ∀ i : Fin K, HasFDerivAt (fun y : Fin K → Fin r → ℝ => ∏ l ∈ Iio i, (1 - ∑ e, y l e))
      (∑ m ∈ Iio i, (∏ l ∈ (Iio i).erase m, (1 - ∑ e, x l e)) • -L m) x := fun i =>
    HasFDerivAt.finsetProd (u := Iio i) (fun l _ => hg l)
  have hcoord : ∀ i : Fin K, HasFDerivAt (fun y : Fin K → Fin r → ℝ => y i c) (ajCoord i c) x :=
    fun i => (ajCoord i c).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (u := Iic j) fun i _ => (hP i).mul (hcoord i)
  refine hsum.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp only [_root_.sum_apply, _root_.add_apply,
    _root_.smul_apply, _root_.neg_apply, smul_eq_mul, hLapply,
    ajCoord_apply]
  change _ = ajDeriv x v j c
  rw [ajDeriv_apply]
  refine sum_congr rfl fun i _ => ?_
  simp only [Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The Aalen–Johansen grid map is continuous. -/
theorem continuous_ajIncidence : Continuous (ajIncidence (K := K) (r := r)) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_ajIncidence x).continuousAt

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- **Aalen–Johansen limit law on a supported grid (uniform topology).** If the cause-specific
Nelson–Aalen increments satisfy `√n (x̂_n - x) ⇒ G` in `Fin K → Fin r → ℝ` with the sup norm
(`hCLT`, the explicit counting-process CLT hypothesis), then the Aalen–Johansen
cumulative-incidence process satisfies `√n (F̂_n - F) ⇒ ajDeriv x G`, `F = ajIncidence x`. -/
theorem tendstoInDistribution_ajIncidence {xhat : ℕ → Ω → Fin K → Fin r → ℝ}
    {x : Fin K → Fin r → ℝ} {G : Ω' → Fin K → Fin r → ℝ}
    (hCLT : TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (xhat n ω - x)) atTop G
      (fun _ => P) P') :
    TendstoInDistribution (fun (n : ℕ) ω => √(n : ℝ) • (ajIncidence (xhat n ω) - ajIncidence x))
      atTop (fun ω => ajDeriv x (G ω)) (fun _ => P) P' :=
  hCLT.functional_delta_of_continuous (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    ((hasFDerivAt_ajIncidence x).hasHadamardDerivWithinAt Set.univ Set.univ)
    (fun _ => ae_of_all _ fun _ => trivial) (ae_of_all _ fun _ => trivial)
    continuous_ajIncidence (ContinuousLinearMap.continuous _)

/-- **Aalen–Johansen limit law for grouped competing-risks data.** For random competing-risks
data sets `Dn n` sharing the fixed grid times, if the cause-specific Nelson–Aalen increments
`d_{i,c} / Y_i` satisfy `√n (· - x) ⇒ G` (sup norm), then the Aalen–Johansen estimates at the
grid times satisfy `√n (F̂_n(t_j) - F_j) ⇒ ajDeriv x G`. -/
theorem tendstoInDistribution_cumulativeIncidence_grid {Dn : ℕ → Ω → CompetingRiskData K r}
    {x : Fin K → Fin r → ℝ} {G : Ω' → Fin K → Fin r → ℝ}
    (hCLT : TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) •
        ((fun i e => ((Dn n ω).events i e : ℝ) / (Dn n ω).atRisk i) - x)) atTop G
      (fun _ => P) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => √(n : ℝ) •
        ((fun j c => (Dn n ω).cumulativeIncidence c ((Dn n ω).time j)) - ajIncidence x))
      atTop (fun ω => ajDeriv x (G ω)) (fun _ => P) P' := by
  refine (tendstoInDistribution_ajIncidence hCLT).congr (fun n => ae_of_all _ fun ω => ?_)
    (ae_of_all _ fun _ => rfl)
  congr 2
  funext j c
  exact (cumulativeIncidence_time_eq_ajIncidence _ j c).symm

omit [IsProbabilityMeasure P'] in
private lemma eq_sum_single (y : Fin K → Fin r → ℝ) :
    y = ∑ p : Fin K × Fin r, y p.1 p.2 • Pi.single p.1 (Pi.single p.2 (1 : ℝ)) := by
  funext i e
  rw [Finset.sum_apply, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i,
    Finset.sum_eq_single e]
  · simp
  · intro b _ hb; simp [hb]
  · simp
  · intro b _ hb
    exact Finset.sum_eq_zero fun e' _ => by simp [hb]
  · simp

/-- **Covariance of the Aalen–Johansen grid limit.** For any square-integrable cause-specific
Nelson–Aalen limit `G` with covariance matrix `Γ p q = Cov(G p, G q)`,
`Cov((ajDeriv x G) j c, (ajDeriv x G) j' c') = ∑_p ∑_q a(j, c; p) a(j', c'; q) Γ p q`
with the explicit coefficients `a(j, c; p) = ajDeriv x δ_p j c` (`ajDeriv_apply`). For grouped
competing-risks data the cause-specific counts at one grid time are multinomial, giving
`Γ (i, c) (i', e) = δ_{i i'} (x i c δ_{c e} - x i c x i e) / y i` (`y i` the limiting at-risk
fraction): coordinates at different grid times are uncorrelated, but two causes with positive
hazard at the same time are negatively correlated, so `Γ` is not diagonal. -/
theorem covariance_ajLimit (x : Fin K → Fin r → ℝ) (G : Ω' → Fin K → Fin r → ℝ)
    (Γ : Fin K × Fin r → Fin K × Fin r → ℝ)
    (hG : ∀ p : Fin K × Fin r, MemLp (fun ω => G ω p.1 p.2) 2 P')
    (hcov : ∀ p q : Fin K × Fin r, cov[fun ω => G ω p.1 p.2, fun ω => G ω q.1 q.2; P'] = Γ p q)
    (j j' : Fin K) (c c' : Fin r) :
    cov[fun ω => ajDeriv x (G ω) j c, fun ω => ajDeriv x (G ω) j' c'; P'] =
      ∑ p : Fin K × Fin r, ∑ q : Fin K × Fin r,
        ajDeriv x (Pi.single p.1 (Pi.single p.2 1)) j c *
          ajDeriv x (Pi.single q.1 (Pi.single q.2 1)) j' c' * Γ p q := by
  have hexp : ∀ ω (a : Fin K) (b : Fin r), ajDeriv x (G ω) a b =
      ∑ p : Fin K × Fin r, ajDeriv x (Pi.single p.1 (Pi.single p.2 1)) a b * G ω p.1 p.2 := by
    intro ω a b
    conv_lhs => rw [eq_sum_single (G ω)]
    simp [map_sum, map_smul, Finset.sum_apply, mul_comm]
  simp_rw [hexp]
  rw [covariance_fun_sum_fun_sum'
    (X := fun (p : Fin K × Fin r) ω => ajDeriv x (Pi.single p.1 (Pi.single p.2 1)) j c *
      G ω p.1 p.2)
    (Y := fun (q : Fin K × Fin r) ω => ajDeriv x (Pi.single q.1 (Pi.single q.2 1)) j' c' *
      G ω q.1 q.2)
    (fun p _ => (hG p).const_mul _) (fun q _ => (hG q).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, hcov]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

end AalenJohansenGrid

end

end MathlibExt.Probability.Statistics.ProcessAsymptotics
