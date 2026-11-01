/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Monotone likelihood ratio and posterior stochastic ordering

Let `L n θ` be the likelihood of a count observation `n : ℕ` under a real parameter `θ`. The
family has a *monotone likelihood ratio* (MLR, total positivity of order two) on a parameter set
`S` if `L m θ * L n θ' ≤ L n θ * L m θ'` whenever `n ≤ m` and `θ ≤ θ'` lie in `S`; for positive
likelihoods this says `L m θ / L n θ` is nondecreasing in `θ`. For such a family and for
**every** prior `μ` on the parameter, the posterior probability of `{θ > t}` given `n` is
nondecreasing in `n` (Milgrom 1981, Propositions 1–2; Karlin–Rubin 1956 for the MLR theory).
The reversed (antitone) condition gives a posterior that is nonincreasing in `n`.

The posterior comparison is stated in cross-multiplied form (no division), and also for the
Bayes-formula posterior tail `posteriorTail` under positive marginal likelihoods. The prior is an
arbitrary measure concentrated on `S`; only integrability of the likelihoods is assumed.

The Poisson family with a nonnegative mean `λ θ` that is monotone in `θ` is an MLR family, and
with an antitone mean it has an antitone likelihood ratio; the binomial family with a success
probability `p θ ∈ [0, 1]` monotone in `θ` is an MLR family.

## Main results

* `ProbabilityTheory.HasMonotoneLikelihoodRatioOn`, `HasAntitoneLikelihoodRatioOn`.
* `ProbabilityTheory.setIntegral_Ioi_mul_integral_le_of_hasMLR`: cross-multiplied posterior tail
  ordering for an MLR family; `..._of_hasAntitoneLR` for the reversed family.
* `ProbabilityTheory.posteriorTail_mono_of_hasMLR`,
  `ProbabilityTheory.posteriorTail_anti_of_hasAntitoneLR`: posterior tails.
* `ProbabilityTheory.poissonLik_hasMLR`, `poissonLik_hasAntitoneLR`, `binomialLik_hasMLR`.

## References

* P. R. Milgrom, *Good news and bad news: representation theorems and applications*,
  Bell J. Econ. 12 (1981) 380–391, Propositions 1 and 2.
* S. Karlin and H. Rubin, *The theory of decision procedures for distributions with monotone
  likelihood ratio*, Ann. Math. Statist. 27 (1956) 272–299.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped Nat

namespace ProbabilityTheory

/-- The likelihood family `L : ℕ → ℝ → ℝ` (observation, parameter) has a **monotone
likelihood ratio** on the parameter set `S`: for observations `n ≤ m` and parameters
`θ ≤ θ'` in `S`, `L m θ * L n θ' ≤ L n θ * L m θ'` (total positivity of order two). For positive
likelihoods this is monotonicity of `θ ↦ L m θ / L n θ`. -/
def HasMonotoneLikelihoodRatioOn (L : ℕ → ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ⦃n m : ℕ⦄, n ≤ m → ∀ ⦃θ θ' : ℝ⦄, θ ∈ S → θ' ∈ S → θ ≤ θ' →
    L m θ * L n θ' ≤ L n θ * L m θ'

/-- The likelihood family has an **antitone likelihood ratio** on `S`: for `n ≤ m` and
`θ ≤ θ'` in `S`, `L n θ * L m θ' ≤ L m θ * L n θ'`. For positive likelihoods this says
`θ ↦ L m θ / L n θ` is nonincreasing (larger counts favor smaller parameters). -/
def HasAntitoneLikelihoodRatioOn (L : ℕ → ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ⦃n m : ℕ⦄, n ≤ m → ∀ ⦃θ θ' : ℝ⦄, θ ∈ S → θ' ∈ S → θ ≤ θ' →
    L n θ * L m θ' ≤ L m θ * L n θ'

/-- **Posterior stochastic ordering, cross-multiplied form** (Milgrom 1981, Prop. 1). If the
family `L` has a monotone likelihood ratio on a set `S` carrying the prior `μ`
(`μ Sᶜ = 0`), and every `L n` is `μ`-integrable, then for `n ≤ m` and every threshold `t`,
`(∫_{θ > t} L n dμ) (∫ L m dμ) ≤ (∫_{θ > t} L m dμ) (∫ L n dμ)`. -/
theorem setIntegral_Ioi_mul_integral_le_of_hasMLR {μ : Measure ℝ}
    {L : ℕ → ℝ → ℝ} {S : Set ℝ} (hμS : μ Sᶜ = 0)
    (hL : HasMonotoneLikelihoodRatioOn L S) (hint : ∀ n, Integrable (L n) μ)
    {n m : ℕ} (hnm : n ≤ m) (t : ℝ) :
    (∫ θ in Ioi t, L n θ ∂μ) * ∫ θ, L m θ ∂μ ≤ (∫ θ in Ioi t, L m θ ∂μ) * ∫ θ, L n θ ∂μ := by
  have hS : ∀ᵐ θ ∂μ, θ ∈ S := mem_ae_iff.mpr hμS
  set A : Set ℝ := Ioi t
  have hsplit : ∀ k, ∫ θ, L k θ ∂μ = (∫ θ in A, L k θ ∂μ) + ∫ θ in Aᶜ, L k θ ∂μ := fun k =>
    (integral_add_compl measurableSet_Ioi (hint k)).symm
  -- for a.e. `y ≤ t`: `L m y ∫_A L n ≤ L n y ∫_A L m`
  have hy : ∀ᵐ y ∂μ.restrict Aᶜ,
      (∫ θ in A, L n θ ∂μ) * L m y ≤ (∫ θ in A, L m θ ∂μ) * L n y := by
    filter_upwards [ae_restrict_mem₀ measurableSet_Ioi.compl.nullMeasurableSet,
      ae_restrict_of_ae hS] with y hyA hyS
    rw [mul_comm, mul_comm _ (L n y), ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_ae_restrict ((hint n).integrableOn.const_mul _)
      ((hint m).integrableOn.const_mul _) ?_
    filter_upwards [ae_restrict_mem₀ measurableSet_Ioi.nullMeasurableSet,
      ae_restrict_of_ae hS] with x hxA hxS
    have hyx : y ≤ x := (not_lt.mp hyA).trans (le_of_lt hxA)
    exact hL hnm hyS hxS hyx
  have hint2 := setIntegral_mono_ae_restrict ((hint m).integrableOn.const_mul _)
    ((hint n).integrableOn.const_mul _) hy
  rw [integral_const_mul, integral_const_mul] at hint2
  rw [hsplit m, hsplit n]
  nlinarith [hint2]

/-- **Posterior stochastic ordering for an antitone likelihood ratio, cross-multiplied form.**
Under the hypotheses of `setIntegral_Ioi_mul_integral_le_of_hasMLR` with the reversed ratio
condition, for `n ≤ m`:
`(∫_{θ > t} L m dμ) (∫ L n dμ) ≤ (∫_{θ > t} L n dμ) (∫ L m dμ)`. -/
theorem setIntegral_Ioi_mul_integral_le_of_hasAntitoneLR {μ : Measure ℝ}
    {L : ℕ → ℝ → ℝ} {S : Set ℝ} (hμS : μ Sᶜ = 0)
    (hL : HasAntitoneLikelihoodRatioOn L S) (hint : ∀ n, Integrable (L n) μ)
    {n m : ℕ} (hnm : n ≤ m) (t : ℝ) :
    (∫ θ in Ioi t, L m θ ∂μ) * ∫ θ, L n θ ∂μ ≤ (∫ θ in Ioi t, L n θ ∂μ) * ∫ θ, L m θ ∂μ := by
  have hS : ∀ᵐ θ ∂μ, θ ∈ S := mem_ae_iff.mpr hμS
  set A : Set ℝ := Ioi t
  have hsplit : ∀ k, ∫ θ, L k θ ∂μ = (∫ θ in A, L k θ ∂μ) + ∫ θ in Aᶜ, L k θ ∂μ := fun k =>
    (integral_add_compl measurableSet_Ioi (hint k)).symm
  have hy : ∀ᵐ y ∂μ.restrict Aᶜ,
      (∫ θ in A, L m θ ∂μ) * L n y ≤ (∫ θ in A, L n θ ∂μ) * L m y := by
    filter_upwards [ae_restrict_mem₀ measurableSet_Ioi.compl.nullMeasurableSet,
      ae_restrict_of_ae hS] with y hyA hyS
    rw [mul_comm, mul_comm _ (L m y), ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_mono_ae_restrict ((hint m).integrableOn.const_mul _)
      ((hint n).integrableOn.const_mul _) ?_
    filter_upwards [ae_restrict_mem₀ measurableSet_Ioi.nullMeasurableSet,
      ae_restrict_of_ae hS] with x hxA hxS
    have hyx : y ≤ x := (not_lt.mp hyA).trans (le_of_lt hxA)
    exact hL hnm hyS hxS hyx
  have hint2 := setIntegral_mono_ae_restrict ((hint n).integrableOn.const_mul _)
    ((hint m).integrableOn.const_mul _) hy
  rw [integral_const_mul, integral_const_mul] at hint2
  rw [hsplit m, hsplit n]
  nlinarith [hint2]

/-- Posterior probability of `{θ > t}` after observing `n`, by Bayes' formula for the prior
`μ` and likelihood `L`: `(∫_{θ > t} L n θ dμ) / ∫ L n θ dμ`. Meaningful when the marginal
likelihood `∫ L n dμ` is positive (otherwise the division returns the junk value `0`). -/
noncomputable def posteriorTail (μ : Measure ℝ) (L : ℕ → ℝ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (∫ θ in Ioi t, L n θ ∂μ) / ∫ θ, L n θ ∂μ

/-- **The posterior is stochastically nondecreasing in the observation** for an MLR family and
every prior (Milgrom 1981, Prop. 2): if `n ≤ m` and both marginal likelihoods are positive, then
`P(θ > t ∣ n) ≤ P(θ > t ∣ m)` for every `t`. -/
theorem posteriorTail_mono_of_hasMLR {μ : Measure ℝ}
    {L : ℕ → ℝ → ℝ} {S : Set ℝ} (hμS : μ Sᶜ = 0)
    (hL : HasMonotoneLikelihoodRatioOn L S) (hint : ∀ n, Integrable (L n) μ)
    {n m : ℕ} (hnm : n ≤ m) (hn : 0 < ∫ θ, L n θ ∂μ) (hm : 0 < ∫ θ, L m θ ∂μ) (t : ℝ) :
    posteriorTail μ L n t ≤ posteriorTail μ L m t := by
  unfold posteriorTail
  rw [div_le_div_iff₀ hn hm]
  exact setIntegral_Ioi_mul_integral_le_of_hasMLR hμS hL hint hnm t

/-- **The posterior is stochastically nonincreasing in the observation** for a family with an
antitone likelihood ratio and every prior: if `n ≤ m` and both marginal likelihoods are
positive, then `P(θ > t ∣ m) ≤ P(θ > t ∣ n)` for every `t`. -/
theorem posteriorTail_anti_of_hasAntitoneLR {μ : Measure ℝ}
    {L : ℕ → ℝ → ℝ} {S : Set ℝ} (hμS : μ Sᶜ = 0)
    (hL : HasAntitoneLikelihoodRatioOn L S) (hint : ∀ n, Integrable (L n) μ)
    {n m : ℕ} (hnm : n ≤ m) (hn : 0 < ∫ θ, L n θ ∂μ) (hm : 0 < ∫ θ, L m θ ∂μ) (t : ℝ) :
    posteriorTail μ L m t ≤ posteriorTail μ L n t := by
  unfold posteriorTail
  rw [div_le_div_iff₀ hm hn]
  exact setIntegral_Ioi_mul_integral_le_of_hasAntitoneLR hμS hL hint hnm t

/-- Poisson likelihood with parameter-dependent mean `λ θ`:
`L n θ = e^{-λ θ} λ θ ^ n / (n !)`. -/
noncomputable def poissonLik (lam : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  exp (-lam θ) * lam θ ^ n / n !

/-- A Poisson family whose mean is nonnegative and monotone on `S` has a monotone likelihood
ratio on `S`. -/
theorem poissonLik_hasMLR {lam : ℝ → ℝ} {S : Set ℝ} (hmono : MonotoneOn lam S)
    (hnn : ∀ θ ∈ S, 0 ≤ lam θ) : HasMonotoneLikelihoodRatioOn (poissonLik lam) S := by
  intro n m hnm θ θ' hθ hθ' hle
  have ha := hnn θ hθ
  have hab := hmono hθ hθ' hle
  have key : lam θ ^ m * lam θ' ^ n ≤ lam θ ^ n * lam θ' ^ m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, pow_add]
    have h1 := pow_le_pow_left₀ ha hab k
    have h2 : 0 ≤ lam θ ^ n * lam θ' ^ n := by have := ha.trans hab; positivity
    nlinarith
  unfold poissonLik
  calc exp (-lam θ) * lam θ ^ m / m ! * (exp (-lam θ') * lam θ' ^ n / n !)
      = exp (-lam θ) * exp (-lam θ') / (m ! * n !) * (lam θ ^ m * lam θ' ^ n) := by ring
    _ ≤ exp (-lam θ) * exp (-lam θ') / (m ! * n !) * (lam θ ^ n * lam θ' ^ m) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = exp (-lam θ) * lam θ ^ n / n ! * (exp (-lam θ') * lam θ' ^ m / m !) := by ring

/-- A Poisson family whose mean is nonnegative and antitone on `S` has an antitone likelihood
ratio on `S`. -/
theorem poissonLik_hasAntitoneLR {lam : ℝ → ℝ} {S : Set ℝ} (hanti : AntitoneOn lam S)
    (hnn : ∀ θ ∈ S, 0 ≤ lam θ) : HasAntitoneLikelihoodRatioOn (poissonLik lam) S := by
  intro n m hnm θ θ' hθ hθ' hle
  have hb := hnn θ' hθ'
  have hba := hanti hθ hθ' hle
  have key : lam θ ^ n * lam θ' ^ m ≤ lam θ ^ m * lam θ' ^ n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, pow_add]
    have h1 := pow_le_pow_left₀ hb hba k
    have h2 : 0 ≤ lam θ ^ n * lam θ' ^ n := by have := hb.trans hba; positivity
    nlinarith
  unfold poissonLik
  calc exp (-lam θ) * lam θ ^ n / n ! * (exp (-lam θ') * lam θ' ^ m / m !)
      = exp (-lam θ) * exp (-lam θ') / (m ! * n !) * (lam θ ^ n * lam θ' ^ m) := by ring
    _ ≤ exp (-lam θ) * exp (-lam θ') / (m ! * n !) * (lam θ ^ m * lam θ' ^ n) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = exp (-lam θ) * lam θ ^ m / m ! * (exp (-lam θ') * lam θ' ^ n / n !) := by ring

/-- Binomial likelihood with `N` trials and parameter-dependent success probability `p θ`:
`L n θ = C(N, n) p θ ^ n (1 - p θ) ^ (N - n)` (zero for `n > N`, since `C(N, n) = 0`). -/
noncomputable def binomialLik (N : ℕ) (p : ℝ → ℝ) (n : ℕ) (θ : ℝ) : ℝ :=
  (N.choose n : ℝ) * p θ ^ n * (1 - p θ) ^ (N - n)

/-- A binomial family whose success probability lies in `[0, 1]` and is monotone on `S` has a
monotone likelihood ratio on `S`. -/
theorem binomialLik_hasMLR {N : ℕ} {p : ℝ → ℝ} {S : Set ℝ} (hmono : MonotoneOn p S)
    (hp : ∀ θ ∈ S, p θ ∈ Icc (0 : ℝ) 1) : HasMonotoneLikelihoodRatioOn (binomialLik N p) S := by
  intro n m hnm θ θ' hθ hθ' hle
  obtain ⟨hp0, hp1⟩ := hp θ hθ
  obtain ⟨hq0, hq1⟩ := hp θ' hθ'
  have hpq := hmono hθ hθ' hle
  unfold binomialLik
  rcases le_or_gt m N with hmN | hmN
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have hNn : N - n = (N - (n + k)) + k := by omega
    rw [hNn]
    have hbase : p θ * (1 - p θ') ≤ p θ' * (1 - p θ) := by nlinarith
    have key : (p θ * (1 - p θ')) ^ k ≤ (p θ' * (1 - p θ)) ^ k :=
      pow_le_pow_left₀ (mul_nonneg hp0 (by linarith)) hbase k
    rw [mul_pow, mul_pow] at key
    have hC : 0 ≤ (N.choose (n + k) : ℝ) * N.choose n * (p θ ^ n * p θ' ^ n) *
        ((1 - p θ) ^ (N - (n + k)) * (1 - p θ') ^ (N - (n + k))) := by
      have : 0 ≤ 1 - p θ := by linarith
      have : 0 ≤ 1 - p θ' := by linarith
      positivity
    calc _ = ((N.choose (n + k) : ℝ) * N.choose n * (p θ ^ n * p θ' ^ n) *
          ((1 - p θ) ^ (N - (n + k)) * (1 - p θ') ^ (N - (n + k)))) *
            (p θ ^ k * (1 - p θ') ^ k) := by ring
      _ ≤ ((N.choose (n + k) : ℝ) * N.choose n * (p θ ^ n * p θ' ^ n) *
          ((1 - p θ) ^ (N - (n + k)) * (1 - p θ') ^ (N - (n + k)))) *
            (p θ' ^ k * (1 - p θ) ^ k) := mul_le_mul_of_nonneg_left key hC
      _ = _ := by ring
  · simp [Nat.choose_eq_zero_of_lt hmN]

end ProbabilityTheory
