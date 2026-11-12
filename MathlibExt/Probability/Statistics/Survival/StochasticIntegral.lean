/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Centering
public import MathlibExt.Probability.DoobLpInequality
public import MathlibExt.Probability.Statistics.Survival.NelsonAalen

/-!
# Predictable integrands, stochastic integrals and counting-process martingales

The martingale calculus behind the Nelson–Aalen and Kaplan–Meier estimators, on a fixed
deterministic time grid `0, 1, 2, …` (grouped or discrete-hazard data, or a fixed discretization
of continuous time). The pathwise identities below (the Nelson–Aalen and Kaplan–Meier
representations, Duhamel's equation, the bridges to grouped data) hold on any grid, including the
observed event times; the martingale statements need a deterministic grid and a deterministic
cumulative hazard `α`, and do not give the continuous-time results. (On the observed event-time
grid without ties `Nₙ = n` surely up to the last event, so `ΔA ≡ 1` and the compensated
martingale vanishes.) A filtration `ℱ : Filtration ℕ m0` carries the history; an integrand `H`
is **predictable** in Mathlib's sense `IsStronglyPredictable ℱ H`, which on `ℕ` means `H (n + 1)` is
`ℱ n`-measurable (`IsStronglyPredictable.iff_measurable_add_one`). The **stochastic integral**
against a process `M` is `(H • M)ₙ = ∑_{k < n} H_{k+1} (M_{k+1} - M_k)`.

A **counting process** `N` has `N 0 = 0` and natural-number increments. Its compensator is Doob's
predictable part `A = predictablePart N ℱ μ`, `ΔA_{n+1} = E[ΔN_{n+1} | ℱₙ]`, and the compensated
process `M = N - A` is Mathlib's `martingalePart N ℱ μ`. It is a martingale
(`martingale_martingalePart`) only under the further hypotheses that `N` is adapted
(`StronglyAdapted ℱ N`) and integrable (`∀ n, Integrable (N n) μ`); `IsCountingProcess`
alone assumes neither.
In **Aalen's multiplicative intensity model** the compensator is `∫ Y dα` for a predictable
at-risk process `Y` and a deterministic cumulative hazard `α`
(`predictablePart_eq_aalenCompensator`).

## Main results

* `martingale_stochasticIntegral`, `martingale_stochasticIntegral_of_bdd`: `H • M` is a martingale
  for predictable `H` and a martingale `M`, under integrability of `H ΔM` (resp. bounded `H_{n+1}`).
* `stochasticIntegral_jump` (**jump formula**): `Δ(H • M)_{n+1} = H_{n+1} ΔM_{n+1}`.
* `predictableQuadraticVariation_stochasticIntegral`: `⟨H • M⟩ = H² • ⟨M⟩`.
* `HasUnitJumps.predictableQuadraticVariation_martingalePart`: for unit jumps,
  `⟨N - A⟩ₙ = ∑ ΔA (1 - ΔA)`, the discrete `⟨M⟩ = ∫ (1 - ΔΛ) dΛ`.
* `nelsonAalenProcess_sub_restrictedHazard`, `martingale_nelsonAalenProcess_sub`: the
  Nelson–Aalen process `Â = ∫ dN / Y` satisfies `Â - Λ* = ∫ Y⁻¹ dM`, a martingale.
* `integral_nelsonAalenProcess`: `E[Âₙ] = ∑ Δα P(Y ≠ 0)`, the bias from vanishing risk.
* `prodIntegral_sub_prodIntegral`, `prodIntegral_div_prodIntegral_sub_one`: **Duhamel's equation**
  for discrete product integrals, unconditional and in Gill's quotient form.
* `kaplanMeierProcess_div_sub_one`, `martingale_kaplanMeierProcess`,
  `martingale_kaplanMeierProcess_div`: `Ŝ/S - 1 = -∫ Ŝ₋ / (S Y) dM + ∫ Ŝ₋ / S 1{Y = 0} dα`, so
  `Ŝ/S` minus the vanishing-risk remainder is a martingale, and `Ŝ/S` is one if `Y` never vanishes.
* `nelsonAalen_time_eq_nelsonAalenProcess`, `kmSurvival_time_eq_kaplanMeierProcess`: the grouped
  estimators `CensoredData.nelsonAalen` and `CensoredData.kmSurvival` are these processes.

## Boundary cases

* **Jumps.** The integral jumps by `H ΔM` (`stochasticIntegral_jump`); compensator jumps reduce
  `⟨M⟩` from `A` to `∑ ΔA (1 - ΔA)`; a hazard jump `Δα = 1` kills `S = 𝒫(1 - dα)`, which is why the
  Kaplan–Meier representation assumes `Δα ≠ 1`.
* **Vanishing risk.** Convention: the integrand is the totalized inverse `Y⁻¹` (`0⁻¹ = 0`), i.e.
  `J / Y` with `J = 1{Y ≠ 0}`. A step with `Y = 0` contributes nothing to `Â` or `Ŝ` whatever `N`
  does (`nelsonAalenProcess_succ_of_atRisk_eq_zero`, and `kaplanMeierProcess_succ`, whose factor
  is `1 - 0⁻¹ ΔN = 1`); the cost is that `Â` estimates the
  restricted hazard `Λ* = ∫ J dα` (`restrictedHazard`), not `α`, and the Kaplan–Meier
  representation carries an explicit remainder `∫ Ŝ₋ / S · 1{Y = 0} dα`.
* **Non-predictable integrands.** For an adapted `N`, the integrand `H = ΔN` is adapted but
  anticipating (adaptation of `N` is a separate hypothesis, not implied by
  `IsCountingProcess`); `H • M` is a
  martingale only if `N` jumps solely where `ΔA = 1`
  (`HasUnitJumps.ae_jump_mul_eq_zero_of_martingale`); any unpredicted jump of positive
  probability makes it fail (`HasUnitJumps.not_martingale_of_unpredicted_jump`).

## Scope

Time is discrete. The continuous-time integral over `ℝ≥0` (predictable σ-algebra on
`ℝ≥0 × Ω`, Doob–Meyer compensators, local martingales and localization) is not built here; with
finitely many subjects the counting-process part of `∫ H dN` over `[0, t]` is a finite sum over
jump times, and the grid results above are its discrete-hazard form. The martingale central
limit theorem for these integrals is not proved here.

## Reused API (source receipts)

* `MeasureTheory.IsStronglyPredictable`, `IsStronglyPredictable.measurable_add_one`,
  `IsStronglyPredictable.of_measurable_add_one` (`Mathlib/Probability/Process/Predictable.lean`).
* `MeasureTheory.predictablePart`, `martingalePart`, `martingale_martingalePart`,
  `predictablePart_add_ae_eq` (`Mathlib/Probability/Martingale/Centering.lean`).
* `MeasureTheory.predictableQuadraticVariation` (`MathlibExt/Probability/DoobLpInequality.lean`).
* `KaplanMeier.CensoredData.nelsonAalen`, `kmSurvival`, `kmFactor`
  (`MathlibExt/Probability/Statistics/Survival/{NelsonAalen,KaplanMeier}.lean`).

The continuous-time Brownian integral in `MathlibExt/Probability/ElementaryItoIntegral.lean` is
specific to Brownian integrators and is not reused.

## References

* O. O. Aalen, *Nonparametric inference for a family of counting processes*, Ann. Statist. 6
  (1978), 701–726.
* R. D. Gill, *Censoring and Stochastic Integrals*, Mathematical Centre Tracts 124, Amsterdam
  (1980).
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Sections II.3–II.4 (stochastic integrals, predictable variation),
  II.6 (product integrals, Duhamel's equation), IV.1 (Nelson–Aalen), IV.3 (Kaplan–Meier).
* T. R. Fleming and D. P. Harrington, *Counting Processes and Survival Analysis*, Wiley (1991),
  Chapter 2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess

open MeasureTheory Finset

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### The stochastic integral of a predictable integrand -/

/-- The **stochastic integral** `(H • M)ₙ = ∑_{k < n} H_{k+1} (M_{k+1} - M_k)` of an integrand `H`
against a process `M` on the time grid `0, 1, 2, …`. The integrand is evaluated at the *right*
end `k + 1` of the step `(k, k + 1]`; it is meant to be predictable (`H (k + 1)` known at time `k`,
Mathlib's `IsStronglyPredictable`), the convention of `Submartingale.sum_mul_sub'`. -/
def stochasticIntegral (H M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ range n, H (k + 1) ω * (M (k + 1) ω - M k ω)

/-- The integral over the empty time range vanishes. -/
@[simp] theorem stochasticIntegral_zero (H M : ℕ → Ω → ℝ) : stochasticIntegral H M 0 = 0 := by
  funext ω; simp [stochasticIntegral]

/-- One more step adds `H_{n+1} (M_{n+1} - Mₙ)`. -/
theorem stochasticIntegral_succ (H M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stochasticIntegral H M (n + 1) ω =
      stochasticIntegral H M n ω + H (n + 1) ω * (M (n + 1) ω - M n ω) := by
  simp [stochasticIntegral, sum_range_succ]

/-- **Jump formula**: the integral jumps by `H_{n+1} ΔM_{n+1}` across the step `(n, n + 1]`, the
discrete form of `Δ(∫ H dM)_t = H_t ΔM_t`. -/
theorem stochasticIntegral_jump (H M : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stochasticIntegral H M (n + 1) ω - stochasticIntegral H M n ω =
      H (n + 1) ω * (M (n + 1) ω - M n ω) := by
  rw [stochasticIntegral_succ, add_sub_cancel_left]

/-- Where the integrator does not jump, neither does the integral. -/
theorem stochasticIntegral_succ_of_eq {H M : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : M (n + 1) ω = M n ω) : stochasticIntegral H M (n + 1) ω = stochasticIntegral H M n ω := by
  rw [stochasticIntegral_succ, h, sub_self, mul_zero, add_zero]

/-- The integral is linear in the integrator. -/
theorem stochasticIntegral_sub_right (H M M' : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stochasticIntegral H (fun k ω => M k ω - M' k ω) n ω =
      stochasticIntegral H M n ω - stochasticIntegral H M' n ω := by
  simp only [stochasticIntegral, ← sum_sub_distrib]
  exact sum_congr rfl fun _ _ => by ring

private lemma stochasticIntegral_eq_sum (H M : ℕ → Ω → ℝ) (n : ℕ) :
    stochasticIntegral H M n = ∑ k ∈ range n, fun ω => H (k + 1) ω * (M (k + 1) ω - M k ω) := by
  funext ω; simp [stochasticIntegral]

/-- The stochastic integral of a predictable integrand against an adapted process is adapted. -/
theorem stronglyAdapted_stochasticIntegral {H M : ℕ → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    (hM : StronglyAdapted ℱ M) : StronglyAdapted ℱ (stochasticIntegral H M) := by
  intro n
  rw [stochasticIntegral_eq_sum]
  refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
  have hk : k + 1 ≤ n := mem_range.1 hk
  exact ((hH.measurable_add_one k).mono (ℱ.mono (by omega))).mul
    (((hM (k + 1)).mono (ℱ.mono hk)).sub ((hM k).mono (ℱ.mono (by omega))))

/-- A martingale increment has conditional mean zero. -/
private lemma condExp_increment_eq_zero [SigmaFiniteFiltration μ ℱ] {M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (n : ℕ) : μ[M (n + 1) - M n | ℱ n] =ᵐ[μ] 0 := by
  have h1 := condExp_sub (hM.integrable (n + 1)) (hM.integrable n) (ℱ n)
  have h2 := hM.condExp_ae_eq (Nat.le_succ n)
  rw [condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyAdapted n) (hM.integrable n)] at h1
  filter_upwards [h1, h2] with ω h1 h2
  simp [h1, h2]

/-- **Martingale property of the stochastic integral.** If `M` is a martingale and `H` is
predictable with `H_{n+1} ΔM_{n+1}` integrable for every `n`, then `H • M` is a martingale. On a
finite horizon this is the discrete form of "`∫ H dM` is a (local) martingale"; the integrability
hypothesis replaces localization. -/
theorem martingale_stochasticIntegral [IsFiniteMeasure μ] {H M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hH : IsStronglyPredictable ℱ H)
    (hint : ∀ n, Integrable (fun ω => H (n + 1) ω * (M (n + 1) ω - M n ω)) μ) :
    Martingale (stochasticIntegral H M) ℱ μ := by
  refine martingale_of_condExp_sub_eq_zero_nat
    (stronglyAdapted_stochasticIntegral hH hM.stronglyAdapted) (fun n => ?_) fun n => ?_
  · exact integrable_finsetSum _ fun k _ => hint k
  · have heq : stochasticIntegral H M (n + 1) - stochasticIntegral H M n =
        H (n + 1) * fun ω => M (n + 1) ω - M n ω := by
      funext ω; simp [stochasticIntegral_jump]
    rw [heq]
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := ℱ n) (hH.measurable_add_one n)
      (hint n) ((hM.integrable _).sub (hM.integrable _))
    have h2 : μ[fun ω => M (n + 1) ω - M n ω | ℱ n] =ᵐ[μ] 0 := condExp_increment_eq_zero hM n
    filter_upwards [h1, h2] with ω h1 h2
    rw [h1, Pi.mul_apply, h2, Pi.zero_apply, mul_zero]

/-- **Martingale property for locally bounded predictable integrands**: if each `H_{n+1}` is
bounded, `H • M` is a martingale. -/
theorem martingale_stochasticIntegral_of_bdd [IsFiniteMeasure μ] {H M : ℕ → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hH : IsStronglyPredictable ℱ H)
    (hbdd : ∀ n, ∃ C, ∀ ω, |H (n + 1) ω| ≤ C) : Martingale (stochasticIntegral H M) ℱ μ := by
  refine martingale_stochasticIntegral hM hH fun n => ?_
  obtain ⟨C, hC⟩ := hbdd n
  exact ((hM.integrable _).sub (hM.integrable _)).bdd_mul
    ((hH.measurable_add_one n).mono (ℱ.le n)).aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.norm_eq_abs _).trans_le (hC ω))

/-- **Predictable quadratic variation of the stochastic integral**: `⟨H • M⟩ = H² • ⟨M⟩`, where
`⟨M⟩ₙ = ∑_{k < n} E[(ΔM_{k+1})² | ℱ_k]` is `predictableQuadraticVariation`. This is the discrete
form of `⟨∫ H dM⟩ = ∫ H² d⟨M⟩`. -/
theorem predictableQuadraticVariation_stochasticIntegral {H M : ℕ → Ω → ℝ}
    (hH : IsStronglyPredictable ℱ H)
    (hint : ∀ n, Integrable (fun ω => H (n + 1) ω ^ 2 * (M (n + 1) ω - M n ω) ^ 2) μ)
    (hint' : ∀ n, Integrable (fun ω => (M (n + 1) ω - M n ω) ^ 2) μ) (n : ℕ) :
    predictableQuadraticVariation μ ℱ (stochasticIntegral H M) n =ᵐ[μ]
      stochasticIntegral (fun k ω => H k ω ^ 2) (predictableQuadraticVariation μ ℱ M) n := by
  have hk : ∀ k, μ[(fun ω => (H (k + 1) ω * (M (k + 1) ω - M k ω)) ^ 2) | ℱ k] =ᵐ[μ]
      fun ω => H (k + 1) ω ^ 2 * μ[(fun ω => (M (k + 1) ω - M k ω) ^ 2) | ℱ k] ω := by
    intro k
    have heq : (fun ω => (H (k + 1) ω * (M (k + 1) ω - M k ω)) ^ 2) =
        (fun ω => H (k + 1) ω ^ 2) * fun ω => (M (k + 1) ω - M k ω) ^ 2 := by
      funext ω; simp only [Pi.mul_apply]; ring
    rw [heq]
    exact condExp_mul_of_stronglyMeasurable_left ((hH.measurable_add_one k).pow 2) (hint k)
      (hint' k)
  filter_upwards [ae_all_iff.2 hk] with ω hω
  simp only [predictableQuadraticVariation, stochasticIntegral, sum_range_succ,
    add_sub_cancel_left]
  exact sum_congr rfl fun k _ => hω k

/-- **Associativity**: `H • (K • X) = (H K) • X`, the discrete form of
`∫ H d(∫ K dX) = ∫ H K dX`. -/
theorem stochasticIntegral_stochasticIntegral (H K X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    stochasticIntegral H (stochasticIntegral K X) n ω =
      stochasticIntegral (fun k ω => H k ω * K k ω) X n ω := by
  simp only [stochasticIntegral]
  refine sum_congr rfl fun k _ => ?_
  rw [← stochasticIntegral, ← stochasticIntegral, stochasticIntegral_jump, mul_assoc]

/-! ### Counting processes and their compensators -/

/-- A discrete-time **counting process**: `N 0 = 0` and every increment `N (n + 1) - N n` is a
natural number (several events may occur in one step, e.g. tied event times). This assumes
neither adaptation nor integrability: a martingale conclusion for `martingalePart N` needs
`StronglyAdapted ℱ N` and `∀ n, Integrable (N n) μ` as separate hypotheses. -/
structure IsCountingProcess (N : ℕ → Ω → ℝ) : Prop where
  /-- The process starts at `0`. -/
  zero : ∀ ω, N 0 ω = 0
  /-- Every increment is a natural number. -/
  increment_nat : ∀ n ω, ∃ m : ℕ, N (n + 1) ω - N n ω = m

/-- A process **has unit jumps** if each increment is `0` or `1` (no two events in one step). -/
def HasUnitJumps (N : ℕ → Ω → ℝ) : Prop :=
  ∀ n ω, N (n + 1) ω - N n ω = 0 ∨ N (n + 1) ω - N n ω = 1

/-- A process with unit jumps started at `0` is a counting process. -/
theorem HasUnitJumps.isCountingProcess {N : ℕ → Ω → ℝ} (hN : HasUnitJumps N)
    (h0 : ∀ ω, N 0 ω = 0) : IsCountingProcess N :=
  ⟨h0, fun n ω => (hN n ω).elim (fun h => ⟨0, by simp [h]⟩) fun h => ⟨1, by simp [h]⟩⟩

/-- The increments of a counting process are non-negative. -/
theorem IsCountingProcess.increment_nonneg {N : ℕ → Ω → ℝ} (hN : IsCountingProcess N) (n : ℕ)
    (ω : Ω) : 0 ≤ N (n + 1) ω - N n ω := by
  obtain ⟨m, hm⟩ := hN.increment_nat n ω
  rw [hm]; positivity

/-- A counting process has non-decreasing paths. -/
theorem IsCountingProcess.monotone {N : ℕ → Ω → ℝ} (hN : IsCountingProcess N) (ω : Ω) :
    Monotone fun n => N n ω :=
  monotone_nat_of_le_succ fun n => sub_nonneg.1 (hN.increment_nonneg n ω)

/-- The increment of the compensated process `M = N - A` (Mathlib's `martingalePart`, with the
compensator `A = predictablePart N`) is `ΔN_{n+1} - E[ΔN_{n+1} | ℱₙ]`. -/
theorem martingalePart_succ_sub (N : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    martingalePart N ℱ μ (n + 1) ω - martingalePart N ℱ μ n ω =
      N (n + 1) ω - N n ω - μ[N (n + 1) - N n | ℱ n] ω := by
  simp only [martingalePart, predictablePart_add_one, Pi.sub_apply, Pi.add_apply]
  ring

/-- The **compensator** `A = predictablePart N` of a counting process is a.e. non-decreasing:
its increment `E[ΔN_{n+1} | ℱₙ]` is a.e. non-negative. -/
theorem IsCountingProcess.compensator_increment_nonneg {N : ℕ → Ω → ℝ} (hN : IsCountingProcess N)
    (n : ℕ) : 0 ≤ᵐ[μ] μ[N (n + 1) - N n | ℱ n] :=
  condExp_nonneg (ae_of_all _ fun ω => hN.increment_nonneg n ω)

/-- For unit jumps the compensator increment is a.e. at most `1`. -/
theorem HasUnitJumps.compensator_increment_le_one [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ}
    (hN : HasUnitJumps N) (hint : ∀ n, Integrable (N n) μ) (n : ℕ) :
    μ[N (n + 1) - N n | ℱ n] ≤ᵐ[μ] fun _ => 1 := by
  have h := condExp_mono (m := ℱ n) ((hint (n + 1)).sub (hint n)) (integrable_const (1 : ℝ))
    (ae_of_all μ fun ω => (show N (n + 1) ω - N n ω ≤ 1 by rcases hN n ω with h | h <;> simp [h]))
  rwa [condExp_const (ℱ.le n)] at h

/-- **Predictable quadratic variation of a compensated counting process with unit jumps**:
`⟨M⟩ₙ = ∑_{k < n} ΔA_{k+1} (1 - ΔA_{k+1})` with `ΔA_{k+1} = E[ΔN_{k+1} | ℱ_k]`. This is the
discrete form of `⟨M⟩ = ∫ (1 - ΔΛ) dΛ`: a compensator jump `ΔA` reduces the variance from `ΔA` to
`ΔA (1 - ΔA)`, and `⟨M⟩ = A` only in the limit of a continuous compensator. -/
theorem HasUnitJumps.predictableQuadraticVariation_martingalePart [IsFiniteMeasure μ]
    {N : ℕ → Ω → ℝ} (hN : HasUnitJumps N) (hadapt : StronglyAdapted ℱ N)
    (hint : ∀ n, Integrable (N n) μ) (n : ℕ) :
    predictableQuadraticVariation μ ℱ (martingalePart N ℱ μ) n =ᵐ[μ]
      fun ω => ∑ k ∈ range n, μ[N (k + 1) - N k | ℱ k] ω * (1 - μ[N (k + 1) - N k | ℱ k] ω) := by
  have hk : ∀ k, μ[(fun ω => (martingalePart N ℱ μ (k + 1) ω - martingalePart N ℱ μ k ω) ^ 2) |
      ℱ k] =ᵐ[μ] fun ω => μ[N (k + 1) - N k | ℱ k] ω * (1 - μ[N (k + 1) - N k | ℱ k] ω) := by
    intro k
    set D : Ω → ℝ := N (k + 1) - N k with hD
    set a : Ω → ℝ := μ[D | ℱ k] with ha
    have hDint : Integrable D μ := (hint (k + 1)).sub (hint k)
    have hDsm : StronglyMeasurable[m0] D :=
      ((hadapt (k + 1)).mono (ℱ.le _)).sub ((hadapt k).mono (ℱ.le _))
    have hDbdd : ∀ ω, ‖D ω‖ ≤ 1 := fun ω => by
      rcases hN k ω with h | h <;> simp [hD, h]
    have hasm : StronglyMeasurable[ℱ k] a := stronglyMeasurable_condExp
    have hDsq : ∀ ω, D ω ^ 2 = D ω := fun ω => by rcases hN k ω with h | h <;> simp [hD, h]
    have hlo : 0 ≤ᵐ[μ] a := condExp_nonneg (ae_of_all _ fun ω => by
      rcases hN k ω with h | h <;> simp [hD, h])
    have hhi : a ≤ᵐ[μ] fun _ => 1 := hN.compensator_increment_le_one hint k
    have habdd : ∀ᵐ ω ∂μ, ‖a ω‖ ≤ 1 := by
      filter_upwards [hlo, hhi] with ω h0 h1
      rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
    have haint : Integrable a μ := integrable_condExp
    have hcint : Integrable (fun ω => 1 - 2 * a ω) μ :=
      (integrable_const (1 : ℝ)).sub (haint.const_mul 2)
    have hcsm : StronglyMeasurable[ℱ k] fun ω => 1 - 2 * a ω :=
      stronglyMeasurable_const.sub (hasm.const_mul 2)
    have hfint : Integrable ((fun ω => 1 - 2 * a ω) * D) μ :=
      hcint.mul_bdd hDsm.aestronglyMeasurable (ae_of_all _ hDbdd)
    have hgint : Integrable (a * a) μ :=
      haint.mul_bdd (hasm.mono (ℱ.le k)).aestronglyMeasurable habdd
    have heq : (fun ω => (martingalePart N ℱ μ (k + 1) ω - martingalePart N ℱ μ k ω) ^ 2) =
        (fun ω => 1 - 2 * a ω) * D + a * a := by
      funext ω
      rw [martingalePart_succ_sub]
      simp only [Pi.add_apply, Pi.mul_apply]
      have := hDsq ω
      simp only [hD, Pi.sub_apply] at this ⊢
      rw [← ha]
      nlinarith [this]
    rw [heq]
    have h1 := condExp_add hfint hgint (ℱ k)
    have h2 := condExp_mul_of_stronglyMeasurable_left hcsm hfint hDint
    have h3 := condExp_of_stronglyMeasurable (ℱ.le k) (hasm.mul hasm) hgint
    filter_upwards [h1, h2] with ω h1 h2
    rw [h1, Pi.add_apply, h2, h3, Pi.mul_apply, Pi.mul_apply, ← ha]
    ring
  filter_upwards [ae_all_iff.2 hk] with ω hω
  simp only [predictableQuadraticVariation]
  exact sum_congr rfl fun k _ => hω k

/-! ### The multiplicative intensity model and the Nelson–Aalen estimator -/

/-- The **Aalen compensator** `Aₙ = ∑_{k < n} Y_{k+1} (α_{k+1} - α_k)`, i.e. `∫ Y dα`, of a
counting process with at-risk process `Y` and deterministic cumulative hazard `α` in Aalen's
multiplicative intensity model. -/
def aalenCompensator (Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) : ℕ → Ω → ℝ :=
  stochasticIntegral Y fun k _ => α k

/-- The **Nelson–Aalen process** `Âₙ = ∑_{k < n} ΔN_{k+1} / Y_{k+1}`, i.e. `∫ dN / Y`.

**Vanishing-risk convention**: the integrand is the totalized inverse `Y⁻¹`, so a step with
nobody at risk (`Y_{k+1} = 0`) contributes `ΔN_{k+1} · 0⁻¹ = 0`, whatever `ΔN_{k+1}` is
(`nelsonAalenProcess_succ_of_atRisk_eq_zero`). This is the indicator convention `J / Y` with
`J = 1{Y ≠ 0}` of Andersen–Borgan–Gill–Keiding (`1{Y > 0}` there, the same for `Y ≥ 0`). -/
noncomputable def nelsonAalenProcess (N Y : ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  stochasticIntegral (fun k ω => (Y k ω)⁻¹) N

/-- The cumulative hazard **restricted to the risk set**, `Λ*ₙ = ∑_{k < n} 1{Y_{k+1} ≠ 0} Δα_{k+1}`,
i.e. `∫ J dα` with `J = 1{Y ≠ 0}`: the quantity the Nelson–Aalen estimator is unbiased for. -/
noncomputable def restrictedHazard (Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) : ℕ → Ω → ℝ :=
  stochasticIntegral (fun k ω => if Y k ω = 0 then 0 else 1) fun k _ => α k

/-- **Vanishing risk produces no spurious jump**: if nobody is at risk at step `n + 1`, the
Nelson–Aalen process does not move, even if the counting process does. -/
theorem nelsonAalenProcess_succ_of_atRisk_eq_zero {N Y : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω}
    (h : Y (n + 1) ω = 0) : nelsonAalenProcess N Y (n + 1) ω = nelsonAalenProcess N Y n ω := by
  simp [nelsonAalenProcess, stochasticIntegral_succ, h]

/-- Likewise the restricted hazard does not accumulate where nobody is at risk. -/
theorem restrictedHazard_succ_of_atRisk_eq_zero {Y : ℕ → Ω → ℝ} {α : ℕ → ℝ} {n : ℕ} {ω : Ω}
    (h : Y (n + 1) ω = 0) : restrictedHazard Y α (n + 1) ω = restrictedHazard Y α n ω := by
  simp [restrictedHazard, stochasticIntegral_succ, h]

/-- **Martingale representation of the Nelson–Aalen estimator** (pathwise identity):
`Â - Λ* = Y⁻¹ • M` with `M = N - ∫ Y dα`, i.e. `Â(t) - Λ*(t) = ∫_0^t J(s) / Y(s) dM(s)`. -/
theorem nelsonAalenProcess_sub_restrictedHazard (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (n : ℕ) (ω : Ω) :
    nelsonAalenProcess N Y n ω - restrictedHazard Y α n ω =
      stochasticIntegral (fun k ω => (Y k ω)⁻¹)
        (fun k ω => N k ω - aalenCompensator Y α k ω) n ω := by
  rw [stochasticIntegral_sub_right, aalenCompensator, stochasticIntegral_stochasticIntegral,
    nelsonAalenProcess, restrictedHazard]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  by_cases h : Y (k + 1) ω = 0 <;> simp [h]

/-- The (totalized) inverse of a real predictable process is predictable. (Mathlib's
`IsStronglyPredictable.inv` needs `ContinuousInv`, which `ℝ` lacks because of `0⁻¹ = 0`.) -/
theorem isStronglyPredictable_inv {Y : ℕ → Ω → ℝ} (hY : IsStronglyPredictable ℱ Y) :
    IsStronglyPredictable ℱ fun k ω => (Y k ω)⁻¹ :=
  .of_measurable_add_one (measurable_inv.comp (hY.stronglyAdapted 0).measurable).stronglyMeasurable
    fun n => (measurable_inv.comp (hY.measurable_add_one n).measurable).stronglyMeasurable

private lemma abs_inv_le_one {y : ℝ} (hy : y = 0 ∨ 1 ≤ y) : |y⁻¹| ≤ 1 := by
  rcases hy with h | h
  · simp [h]
  · rw [abs_of_pos (inv_pos.2 (by linarith))]; exact inv_le_one_of_one_le₀ h

/-- **Nelson–Aalen martingale.** In Aalen's model (`N - ∫ Y dα` is a martingale) with a
predictable at-risk process taking values in `{0} ∪ [1, ∞)` (e.g. a count of subjects),
`Â - Λ*` is a martingale. -/
theorem martingale_nelsonAalenProcess_sub [IsFiniteMeasure μ] {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hM : Martingale (fun n ω => N n ω - aalenCompensator Y α n ω) ℱ μ)
    (hY : IsStronglyPredictable ℱ Y) (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω) :
    Martingale (fun n ω => nelsonAalenProcess N Y n ω - restrictedHazard Y α n ω) ℱ μ := by
  have heq : (fun n ω => nelsonAalenProcess N Y n ω - restrictedHazard Y α n ω) =
      stochasticIntegral (fun k ω => (Y k ω)⁻¹)
        (fun k ω => N k ω - aalenCompensator Y α k ω) := by
    funext n ω; exact nelsonAalenProcess_sub_restrictedHazard N Y α n ω
  rw [heq]
  exact martingale_stochasticIntegral_of_bdd hM (isStronglyPredictable_inv hY) fun n =>
    ⟨1, fun ω => abs_inv_le_one (hY1 _ ω)⟩

/-- **Mean of the Nelson–Aalen estimator under vanishing risk**: `E[Âₙ] = ∑_{k < n} Δα_{k+1}
P(Y_{k+1} ≠ 0)`. So `Â` is unbiased for `Λ*`; its bias for the cumulative hazard `αₙ - α₀` is
`-∑ Δα_{k+1} P(Y_{k+1} = 0)`, which vanishes in particular when the risk set is a.s. non-empty. -/
theorem integral_nelsonAalenProcess [IsProbabilityMeasure μ] {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hM : Martingale (fun n ω => N n ω - aalenCompensator Y α n ω) ℱ μ)
    (hY : IsStronglyPredictable ℱ Y) (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω) (n : ℕ) :
    ∫ ω, nelsonAalenProcess N Y n ω ∂μ =
      ∑ k ∈ range n, (α (k + 1) - α k) * μ.real {ω | Y (k + 1) ω ≠ 0} := by
  have hmart := martingale_nelsonAalenProcess_sub hM hY hY1
  have hset : ∀ k, MeasurableSet {ω | Y (k + 1) ω ≠ 0} := fun k =>
    (((hY.measurable_add_one k).mono (ℱ.le k)).measurable (measurableSet_singleton 0)).compl
  have hΛ : restrictedHazard Y α n =
      ∑ k ∈ range n, {ω | Y (k + 1) ω ≠ 0}.indicator fun _ => α (k + 1) - α k := by
    funext ω
    simp only [restrictedHazard, stochasticIntegral, Finset.sum_apply]
    refine sum_congr rfl fun k _ => ?_
    by_cases h : Y (k + 1) ω = 0 <;> simp [h]
  have hΛint : Integrable (restrictedHazard Y α n) μ := by
    rw [hΛ]
    exact integrable_finsetSum' _ fun k _ => (integrable_const _).indicator (hset k)
  have h0 : ∫ ω, (nelsonAalenProcess N Y n ω - restrictedHazard Y α n ω) ∂μ = 0 := by
    have := hmart.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
    simp only [setIntegral_univ] at this
    rw [← this]
    simp [nelsonAalenProcess, restrictedHazard]
  have hAint : Integrable (nelsonAalenProcess N Y n) μ := by
    have := (hmart.integrable n).add hΛint
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp
  rw [integral_sub hAint hΛint, sub_eq_zero] at h0
  simp only [h0, hΛ, Finset.sum_apply]
  rw [integral_finsetSum _ fun k _ => (integrable_const _).indicator (hset k)]
  refine sum_congr rfl fun k _ => ?_
  rw [integral_indicator_const _ (hset k), smul_eq_mul, mul_comm]

/-- **Identification of the compensator**: in Aalen's model the Doob compensator
`predictablePart N` of the counting process is a.e. the Aalen compensator `∫ Y dα`, so the
compensated martingale `martingalePart N` is a.e. `N - ∫ Y dα`. -/
theorem predictablePart_eq_aalenCompensator [IsFiniteMeasure μ] {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hM : Martingale (fun n ω => N n ω - aalenCompensator Y α n ω) ℱ μ)
    (hY : IsStronglyPredictable ℱ Y) (hYint : ∀ n, Integrable (Y n) μ) (n : ℕ) :
    predictablePart N ℱ μ n =ᵐ[μ] aalenCompensator Y α n := by
  have h := predictablePart_add_ae_eq hM (g := aalenCompensator Y α)
    (fun n => ?_) (by simp [aalenCompensator]) (fun n => ?_) n
  · have hN : ((fun n ω => N n ω - aalenCompensator Y α n ω) + aalenCompensator Y α) = N := by
      funext n ω; simp
    rwa [hN] at h
  · dsimp only
    rw [aalenCompensator, stochasticIntegral_eq_sum]
    refine Finset.stronglyMeasurable_sum _ fun k hk => ?_
    have hk : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
    exact ((hY.measurable_add_one k).mono (ℱ.mono hk)).mul stronglyMeasurable_const
  · exact integrable_finsetSum (range n) fun k _ => (hYint (k + 1)).mul_const (α (k + 1) - α k)

/-! ### Product integrals, Duhamel's equation and the Kaplan–Meier estimator -/

/-- The discrete **product integral** `∏_{k < n} (1 - (A_{k+1} - A_k))` of `1 - dA`, the
product-limit transform of a cumulative hazard `A` into a survival function. -/
def prodIntegral (A : ℕ → ℝ) (n : ℕ) : ℝ := ∏ k ∈ range n, (1 - (A (k + 1) - A k))

/-- The empty product integral is `1`. -/
@[simp] theorem prodIntegral_zero (A : ℕ → ℝ) : prodIntegral A 0 = 1 := by simp [prodIntegral]

/-- One more step multiplies by `1 - ΔA_{n+1}`. -/
theorem prodIntegral_succ (A : ℕ → ℝ) (n : ℕ) :
    prodIntegral A (n + 1) = prodIntegral A n * (1 - (A (n + 1) - A n)) := by
  simp [prodIntegral, prod_range_succ]

/-- The product integral does not vanish as long as no hazard increment equals `1`. -/
theorem prodIntegral_ne_zero {A : ℕ → ℝ} {n : ℕ} (hA : ∀ k < n, A (k + 1) - A k ≠ 1) :
    prodIntegral A n ≠ 0 :=
  prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 (hA k (mem_range.1 hk)).symm

/-- **Duhamel's equation** (no hypotheses): the difference of two product integrals is
`𝒫_A(n) - 𝒫_B(n) = -∑_{k < n} 𝒫_A(k) (ΔA_{k+1} - ΔB_{k+1}) ∏_{k < i < n} (1 - ΔB_{i+1})`,
the discrete form of
`𝒫(1 - dA) - 𝒫(1 - dB) = -∫ 𝒫_{[0,s)}(1 - dA) d(A - B)(s) 𝒫_{(s,t]}(1 - dB)`. -/
theorem prodIntegral_sub_prodIntegral (A B : ℕ → ℝ) (n : ℕ) :
    prodIntegral A n - prodIntegral B n = -∑ k ∈ range n, prodIntegral A k *
      ((A (k + 1) - A k) - (B (k + 1) - B k)) * ∏ i ∈ Ico (k + 1) n, (1 - (B (i + 1) - B i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Ico_self, prod_empty, mul_one]
    have hsum : ∑ k ∈ range n, prodIntegral A k * ((A (k + 1) - A k) - (B (k + 1) - B k)) *
        ∏ i ∈ Ico (k + 1) (n + 1), (1 - (B (i + 1) - B i)) =
        (∑ k ∈ range n, prodIntegral A k * ((A (k + 1) - A k) - (B (k + 1) - B k)) *
          ∏ i ∈ Ico (k + 1) n, (1 - (B (i + 1) - B i))) * (1 - (B (n + 1) - B n)) := by
      rw [sum_mul]
      refine sum_congr rfl fun k hk => ?_
      rw [prod_Ico_succ_top (by have := mem_range.1 hk; omega)]
      ring
    rw [hsum, prodIntegral_succ, prodIntegral_succ]
    linear_combination (1 - (B (n + 1) - B n)) * ih

/-- **Duhamel's equation, Gill's quotient form**: if no increment of `B` equals `1`,
`𝒫_A(n) / 𝒫_B(n) - 1 = -∑_{k < n} 𝒫_A(k) / 𝒫_B(k+1) (ΔA_{k+1} - ΔB_{k+1})`, the discrete form of
`Ŝ/S - 1 = -∫ Ŝ₋ / S d(Â - Λ)`. -/
theorem prodIntegral_div_prodIntegral_sub_one (A B : ℕ → ℝ) {n : ℕ}
    (hB : ∀ k < n, B (k + 1) - B k ≠ 1) :
    prodIntegral A n / prodIntegral B n - 1 = -∑ k ∈ range n,
      prodIntegral A k / prodIntegral B (k + 1) * ((A (k + 1) - A k) - (B (k + 1) - B k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : prodIntegral B n ≠ 0 := prodIntegral_ne_zero fun k hk => hB k (by omega)
    have hb : 1 - (B (n + 1) - B n) ≠ 0 := sub_ne_zero.2 (hB n (by omega)).symm
    rw [sum_range_succ, neg_add, ← ih fun k hk => hB k (by omega), prodIntegral_succ,
      prodIntegral_succ]
    field_simp
    ring

/-- The **Kaplan–Meier process** `Ŝₙ = ∏_{k < n} (1 - ΔN_{k+1} / Y_{k+1})`, the product integral of
the Nelson–Aalen process (with the same vanishing-risk convention: a step with `Y = 0` contributes
the factor `1`). -/
noncomputable def kaplanMeierProcess (N Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  prodIntegral (fun k => nelsonAalenProcess N Y k ω) n

/-- The Kaplan–Meier recursion `Ŝ_{n+1} = Ŝₙ (1 - ΔN_{n+1} / Y_{n+1})`. -/
theorem kaplanMeierProcess_succ (N Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    kaplanMeierProcess N Y (n + 1) ω =
      kaplanMeierProcess N Y n ω * (1 - (Y (n + 1) ω)⁻¹ * (N (n + 1) ω - N n ω)) := by
  rw [kaplanMeierProcess, prodIntegral_succ, nelsonAalenProcess, stochasticIntegral_jump]
  rfl

private lemma kmFactor_mem_Icc {y d : ℝ} (hy : y = 0 ∨ 1 ≤ y) (hd : 0 ≤ d ∧ d ≤ y) :
    0 ≤ 1 - y⁻¹ * d ∧ 1 - y⁻¹ * d ≤ 1 := by
  rcases hy with h | h
  · simp [h]
  · have hy0 : 0 < y := by linarith
    have h1 : y⁻¹ * d ≤ 1 := by rw [inv_mul_le_iff₀ hy0]; linarith
    have h2 : 0 ≤ y⁻¹ * d := mul_nonneg (inv_nonneg.2 hy0.le) hd.1
    constructor <;> linarith

/-- The Kaplan–Meier process takes values in `[0, 1]` when deaths never exceed the number at
risk. -/
theorem kaplanMeierProcess_mem_Icc {N Y : ℕ → Ω → ℝ} (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω) (n : ℕ) (ω : Ω) :
    0 ≤ kaplanMeierProcess N Y n ω ∧ kaplanMeierProcess N Y n ω ≤ 1 := by
  induction n with
  | zero => simp [kaplanMeierProcess]
  | succ n ih =>
    rw [kaplanMeierProcess_succ]
    have h := kmFactor_mem_Icc (hY1 (n + 1) ω) (hNY n ω)
    exact ⟨mul_nonneg ih.1 h.1, by nlinarith [ih.1, ih.2, h.1, h.2]⟩

/-- The Kaplan–Meier process is adapted when `N` is adapted and `Y` is predictable. -/
theorem stronglyAdapted_kaplanMeierProcess {N Y : ℕ → Ω → ℝ} (hN : StronglyAdapted ℱ N)
    (hY : IsStronglyPredictable ℱ Y) : StronglyAdapted ℱ (kaplanMeierProcess N Y) := by
  have hA := stronglyAdapted_stochasticIntegral (isStronglyPredictable_inv hY) hN
  intro n
  change StronglyMeasurable[ℱ n] fun ω =>
    ∏ k ∈ range n, (1 - (nelsonAalenProcess N Y (k + 1) ω - nelsonAalenProcess N Y k ω))
  refine Finset.stronglyMeasurable_fun_prod
    (f := fun k ω => 1 - (nelsonAalenProcess N Y (k + 1) ω - nelsonAalenProcess N Y k ω)) _
    fun k hk => ?_
  have hk := mem_range.1 hk
  exact stronglyMeasurable_const.sub (((hA (k + 1)).mono (ℱ.mono hk)).sub
    ((hA k).mono (ℱ.mono hk.le)))

/-- The integrand `Ŝ_{k-1} / (S_k Y_k)` of Gill's martingale representation of Kaplan–Meier. -/
noncomputable def kaplanMeierIntegrand (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  kaplanMeierProcess N Y (k - 1) ω / prodIntegral α k * (Y k ω)⁻¹

/-- The vanishing-risk remainder integrand `Ŝ_{k-1} / S_k · 1{Y_k = 0}`. -/
noncomputable def kaplanMeierRemainder (N Y : ℕ → Ω → ℝ) (α : ℕ → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  kaplanMeierProcess N Y (k - 1) ω / prodIntegral α k * if Y k ω = 0 then 1 else 0

/-- **Martingale representation of the Kaplan–Meier estimator** (pathwise, from Duhamel's
equation): with `S = 𝒫(1 - dα)` and `M = N - ∫ Y dα`,
`Ŝ/S - 1 = -∫ Ŝ₋ / (S Y) dM + ∫ Ŝ₋ / S · 1{Y = 0} dα`.
The second term is the vanishing-risk remainder; it is `0` while the risk set is non-empty. -/
theorem kaplanMeierProcess_div_sub_one (N Y : ℕ → Ω → ℝ) {α : ℕ → ℝ}
    (hα : ∀ k, α (k + 1) - α k ≠ 1) (n : ℕ) (ω : Ω) :
    kaplanMeierProcess N Y n ω / prodIntegral α n - 1 =
      -stochasticIntegral (kaplanMeierIntegrand N Y α)
          (fun k ω => N k ω - aalenCompensator Y α k ω) n ω +
        stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω := by
  rw [kaplanMeierProcess, prodIntegral_div_prodIntegral_sub_one _ _ fun k _ => hα k]
  simp only [stochasticIntegral]
  rw [← sum_neg_distrib, ← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hK : kaplanMeierProcess N Y k ω = prodIntegral (fun k => nelsonAalenProcess N Y k ω) k :=
    rfl
  have hJ : nelsonAalenProcess N Y (k + 1) ω - nelsonAalenProcess N Y k ω =
      (Y (k + 1) ω)⁻¹ * (N (k + 1) ω - N k ω) := stochasticIntegral_jump _ _ _ _
  have hA : aalenCompensator Y α (k + 1) ω =
      aalenCompensator Y α k ω + Y (k + 1) ω * (α (k + 1) - α k) := stochasticIntegral_succ _ _ _ _
  have hS : prodIntegral α (k + 1) ≠ 0 := prodIntegral_ne_zero fun j _ => hα j
  simp only [kaplanMeierIntegrand, kaplanMeierRemainder, Nat.add_sub_cancel, hK, hJ, hA]
  generalize prodIntegral (fun k => nelsonAalenProcess N Y k ω) k = P
  by_cases h : Y (k + 1) ω = 0
  · simp [h]
    ring
  · simp only [h, ite_false, mul_zero]
    field_simp
    ring

/-- **Gill's Kaplan–Meier martingale.** In Aalen's model with deterministic cumulative hazard `α`
(no increment equal to `1`), a predictable at-risk process with values in `{0} ∪ [1, ∞)`, and
deaths `0 ≤ ΔN ≤ Y`, the process `Ŝ/S - 1 - ∫ Ŝ₋ / S · 1{Y = 0} dα` is a martingale. -/
theorem martingale_kaplanMeierProcess [IsFiniteMeasure μ] {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hM : Martingale (fun n ω => N n ω - aalenCompensator Y α n ω) ℱ μ)
    (hN : StronglyAdapted ℱ N) (hY : IsStronglyPredictable ℱ Y)
    (hY1 : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω)
    (hα : ∀ k, α (k + 1) - α k ≠ 1) :
    Martingale (fun n ω => kaplanMeierProcess N Y n ω / prodIntegral α n - 1 -
      stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω) ℱ μ := by
  have heq : (fun n ω => kaplanMeierProcess N Y n ω / prodIntegral α n - 1 -
      stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω) =
      -stochasticIntegral (kaplanMeierIntegrand N Y α)
        (fun k ω => N k ω - aalenCompensator Y α k ω) := by
    funext n ω
    rw [kaplanMeierProcess_div_sub_one N Y hα]
    simp only [Pi.neg_apply]
    ring
  rw [heq]
  refine (martingale_stochasticIntegral_of_bdd hM ?_ fun n => ⟨|(prodIntegral α (n + 1))⁻¹|,
    fun ω => ?_⟩).neg
  · have hS := stronglyAdapted_kaplanMeierProcess hN hY
    have hYi := isStronglyPredictable_inv hY
    refine .of_measurable_add_one ?_ fun n => ?_
    · exact (((hS 0).measurable.div_const _).stronglyMeasurable).mul (hYi.stronglyAdapted 0)
    · change StronglyMeasurable[ℱ n] fun ω =>
        kaplanMeierProcess N Y n ω / prodIntegral α (n + 1) * (Y (n + 1) ω)⁻¹
      exact (((hS n).measurable.div_const _).stronglyMeasurable).mul (hYi.measurable_add_one n)
  · simp only [kaplanMeierIntegrand, Nat.add_sub_cancel]
    have h1 := kaplanMeierProcess_mem_Icc hY1 hNY n ω
    rw [abs_mul, abs_div, div_eq_mul_inv, ← abs_inv]
    calc |kaplanMeierProcess N Y n ω| * |(prodIntegral α (n + 1))⁻¹| * |(Y (n + 1) ω)⁻¹|
        ≤ 1 * |(prodIntegral α (n + 1))⁻¹| * 1 := by
          gcongr
          · rw [abs_of_nonneg h1.1]; exact h1.2
          · exact abs_inv_le_one (hY1 _ ω)
      _ = |(prodIntegral α (n + 1))⁻¹| := by ring

/-- **Kaplan–Meier martingale without vanishing risk**: if the risk set never empties, `Ŝ / S` is
a martingale (Gill 1980). -/
theorem martingale_kaplanMeierProcess_div [IsFiniteMeasure μ] {N Y : ℕ → Ω → ℝ} {α : ℕ → ℝ}
    (hM : Martingale (fun n ω => N n ω - aalenCompensator Y α n ω) ℱ μ)
    (hN : StronglyAdapted ℱ N) (hY : IsStronglyPredictable ℱ Y)
    (hY1 : ∀ n ω, 1 ≤ Y (n + 1) ω) (hY0 : ∀ ω, Y 0 ω = 0 ∨ 1 ≤ Y 0 ω)
    (hNY : ∀ n ω, 0 ≤ N (n + 1) ω - N n ω ∧ N (n + 1) ω - N n ω ≤ Y (n + 1) ω)
    (hα : ∀ k, α (k + 1) - α k ≠ 1) :
    Martingale (fun n ω => kaplanMeierProcess N Y n ω / prodIntegral α n) ℱ μ := by
  have hY1' : ∀ n ω, Y n ω = 0 ∨ 1 ≤ Y n ω := fun n ω => by
    cases n with
    | zero => exact hY0 ω
    | succ n => exact Or.inr (hY1 n ω)
  have h := (martingale_kaplanMeierProcess hM hN hY hY1' hNY hα).add (martingale_const ℱ μ 1)
  have heq : ((fun n ω => kaplanMeierProcess N Y n ω / prodIntegral α n - 1 -
      stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω) +
      fun _ _ => (1 : ℝ)) = fun n ω => kaplanMeierProcess N Y n ω / prodIntegral α n := by
    funext n ω
    have h0 : stochasticIntegral (kaplanMeierRemainder N Y α) (fun k _ => α k) n ω = 0 :=
      sum_eq_zero fun k _ => by
        simp [kaplanMeierRemainder, (by linarith [hY1 k ω] : Y (k + 1) ω ≠ 0)]
    simp [h0]
  rwa [heq] at h

/-! ### What fails without predictability -/

/-- **An adapted but anticipating integrand breaks the martingale property.** Let `N` have unit
jumps and `M = martingalePart N` be its compensated martingale. If `N` is adapted, the
integrand `H_k = ΔN_k` is adapted but not predictable (adaptation is not implied by
`IsCountingProcess` or `HasUnitJumps`). If `H • M` is nevertheless a martingale, then a.e. `N`
can only jump
at steps where its compensator jumps by exactly `1` (`ΔN_{k+1} (1 - ΔA_{k+1}) = 0`): the
anticipating integral picks up `∑ ΔN (1 - ΔA) ≥ 0`, which has positive mean as soon as `N` has a
jump that is not fully predicted. -/
theorem HasUnitJumps.ae_jump_mul_eq_zero_of_martingale [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ}
    (hN : HasUnitJumps N) (hint : ∀ n, Integrable (N n) μ)
    (hmart : Martingale (stochasticIntegral (fun k ω => N k ω - N (k - 1) ω)
      (martingalePart N ℱ μ)) ℱ μ) (k : ℕ) :
    ∀ᵐ ω ∂μ, (N (k + 1) ω - N k ω) * (1 - μ[N (k + 1) - N k | ℱ k] ω) = 0 := by
  set X := stochasticIntegral (fun k ω => N k ω - N (k - 1) ω) (martingalePart N ℱ μ) with hX
  have heq : ∀ ω, X (k + 1) ω - X k ω =
      (N (k + 1) ω - N k ω) * (1 - μ[N (k + 1) - N k | ℱ k] ω) := fun ω => by
    rw [hX, stochasticIntegral_jump, Nat.add_sub_cancel, martingalePart_succ_sub]
    rcases hN k ω with h | h <;> rw [h]; ring
  have hXint : Integrable (fun ω => X (k + 1) ω - X k ω) μ :=
    (hmart.integrable _).sub (hmart.integrable _)
  have h0 : ∫ ω, (X (k + 1) ω - X k ω) ∂μ = 0 := by
    rw [integral_sub (hmart.integrable _) (hmart.integrable _)]
    have := hmart.setIntegral_eq (Nat.le_succ k) MeasurableSet.univ
    simp only [setIntegral_univ] at this
    rw [this, sub_self]
  have hnn : 0 ≤ᵐ[μ] fun ω => X (k + 1) ω - X k ω := by
    filter_upwards [hN.compensator_increment_le_one (ℱ := ℱ) hint k] with ω hω
    rw [heq]
    refine mul_nonneg ?_ (sub_nonneg.2 hω)
    rcases hN k ω with h | h <;> simp [h]
  filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hXint).1 h0] with ω hω
  rw [← heq]; exact hω

/-- **Counterexample form**: if with positive probability `N` jumps at step `k + 1` while its
compensator jump is `< 1`, then integrating the anticipating integrand `ΔN` against the
compensated martingale does **not** give a martingale. Predictability of the integrand is
therefore necessary for `martingale_stochasticIntegral`. -/
theorem HasUnitJumps.not_martingale_of_unpredicted_jump [IsFiniteMeasure μ] {N : ℕ → Ω → ℝ}
    (hN : HasUnitJumps N) (hint : ∀ n, Integrable (N n) μ) {k : ℕ}
    (hk : μ {ω | N (k + 1) ω - N k ω = 1 ∧ μ[N (k + 1) - N k | ℱ k] ω < 1} ≠ 0) :
    ¬ Martingale (stochasticIntegral (fun k ω => N k ω - N (k - 1) ω)
      (martingalePart N ℱ μ)) ℱ μ := by
  intro hmart
  refine hk (measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hN.ae_jump_mul_eq_zero_of_martingale
    hint hmart k)))
  obtain ⟨h1, h2⟩ := hω
  simp only [Set.mem_ofPred_eq, h1, one_mul]
  linarith

/-! ### Bridge to the grouped-data estimators -/

@[to_additive]
private lemma prod_fin_le_eq_prod_range {M : Type*} [CommMonoid M] {k : ℕ} (f : ℕ → M)
    (j : Fin k) : ∏ l : Fin k with l ≤ j, f l = ∏ i ∈ range (j + 1), f i := by
  refine prod_bij' (fun l _ => (l : ℕ)) (fun i hi => ⟨i, by
      have := mem_range.1 hi; omega⟩) (fun l hl => ?_) (fun i hi => ?_) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
  · simp only [mem_filter, mem_univ, true_and] at hl
    exact mem_range.2 (by rw [Fin.le_def] at hl; omega)
  · simp only [mem_filter, mem_univ, true_and, Fin.le_def]
    have := mem_range.1 hi; omega

open KaplanMeier in
/-- The counting process of grouped censored data on the step grid: `Nₙ = ∑_{i < n} dᵢ`. -/
noncomputable def gridDeaths {k : ℕ} (D : CensoredData k) : ℕ → Ω → ℝ := fun n _ =>
  ∑ i ∈ range n, if h : i < k then (D.deaths ⟨i, h⟩ : ℝ) else 0

open KaplanMeier in
/-- The at-risk process of grouped censored data on the step grid: `Yₙ = n_{n-1}` (the number at
risk at the `n`-th observation time), and `0` past the last one. -/
noncomputable def gridAtRisk {k : ℕ} (D : CensoredData k) : ℕ → Ω → ℝ := fun n _ =>
  if h : n - 1 < k then (D.atRisk ⟨n - 1, h⟩ : ℝ) else 0

open KaplanMeier in
private lemma gridAtRisk_inv_mul {k : ℕ} (D : CensoredData k) (i : ℕ) (ω : Ω) :
    (gridAtRisk D (i + 1) ω)⁻¹ * (gridDeaths D (i + 1) ω - gridDeaths D i ω) =
      if h : i < k then (D.deaths ⟨i, h⟩ : ℝ) / D.atRisk ⟨i, h⟩ else 0 := by
  simp only [gridAtRisk, gridDeaths, sum_range_succ, add_sub_cancel_left, Nat.add_sub_cancel]
  split_ifs <;> simp [div_eq_inv_mul]

open KaplanMeier in
/-- **Nelson–Aalen bridge**: the grouped-data Nelson–Aalen estimate at the `j`-th observation time
is the stochastic integral `∫ dN / Y` of the grid processes up to step `j + 1`. -/
theorem nelsonAalen_time_eq_nelsonAalenProcess {k : ℕ} (D : CensoredData k) (j : Fin k)
    (ω : Ω) :
    D.nelsonAalen (D.time j) = nelsonAalenProcess (gridDeaths D) (gridAtRisk D) (j + 1) ω := by
  have hfilter : (univ.filter fun l => D.time l ≤ D.time j) = univ.filter (· ≤ j) := by
    ext l; simp [D.strictMono_time.le_iff_le]
  rw [CensoredData.nelsonAalen, hfilter, nelsonAalenProcess, stochasticIntegral]
  simp only [gridAtRisk_inv_mul]
  rw [← sum_fin_le_eq_sum_range]
  exact sum_congr rfl fun l _ => by simp

open KaplanMeier in
/-- **Kaplan–Meier bridge**: the grouped-data Kaplan–Meier estimate at the `j`-th observation time
is the product integral of the grid Nelson–Aalen process up to step `j + 1`. -/
theorem kmSurvival_time_eq_kaplanMeierProcess {k : ℕ} (D : CensoredData k) (j : Fin k)
    (ω : Ω) :
    D.kmSurvival (D.time j) = kaplanMeierProcess (gridDeaths D) (gridAtRisk D) (j + 1) ω := by
  have hfilter : (univ.filter fun l => D.time l ≤ D.time j) = univ.filter (· ≤ j) := by
    ext l; simp [D.strictMono_time.le_iff_le]
  rw [CensoredData.kmSurvival, hfilter, kaplanMeierProcess, prodIntegral]
  have hJ : ∀ i, nelsonAalenProcess (gridDeaths D) (gridAtRisk D) (i + 1) ω -
      nelsonAalenProcess (gridDeaths D) (gridAtRisk D) i ω =
      if h : i < k then (D.deaths ⟨i, h⟩ : ℝ) / D.atRisk ⟨i, h⟩ else 0 := fun i => by
    rw [← gridAtRisk_inv_mul]; exact stochasticIntegral_jump _ _ _ _
  simp only [hJ]
  rw [← prod_fin_le_eq_prod_range (fun i => 1 - if h : i < k then
    (D.deaths ⟨i, h⟩ : ℝ) / D.atRisk ⟨i, h⟩ else 0)]
  exact prod_congr rfl fun l _ => by simp [CensoredData.kmFactor]

end MathlibExt.Probability.Statistics.CountingProcess
