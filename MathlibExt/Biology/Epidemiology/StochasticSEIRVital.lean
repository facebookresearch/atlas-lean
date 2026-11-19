/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SEIRGlobalStability
public import MathlibExt.Biology.Dynamics.StochasticCRNLLN

/-!
# Kurtz's law of large numbers for the stochastic SEIR epidemic with vital dynamics

The deterministic SEIR model with vital dynamics of
`MathlibExt.Biology.Epidemiology.SEIRGlobalStability` (`SEIRVital.IsSolution`) is

  `S' = μ N - β S I / N - μ S`,   `E' = β S I / N - (μ + σ) E`,
  `I' = σ E - (μ + γ) I`,          `R' = γ I - μ R`.

Its stochastic counterpart at population scale `N` is the continuous-time Markov chain on counts
`(S, E, I, R) ∈ ℕ⁴` with eight reaction channels (`Channel`):

| channel | jump | rate |
|---|---|---|
| birth | `S → S + 1` | `μ N` |
| infection | `(S, E) → (S - 1, E + 1)` | `β S I / N` |
| progression | `(E, I) → (E - 1, I + 1)` | `σ E` |
| recovery | `(I, R) → (I - 1, R + 1)` | `γ I` |
| deaths | `X → X - 1` for `X ∈ {S, E, I, R}` | `μ X` |

Every rate has Kurtz's density-dependent form `N · λ_c(S / N, E / N, I / N, R / N)`
(`rate`, `scaledRate`; `rate_birth`, `rate_infection`, …), so as `N → ∞` the scaled chain should
follow the ODE at scale `1`, `SEIRVital.IsSolution β σ γ μ 1 s e i r`.

## The chain

As for SIR we use Kurtz's random time-change representation (Ethier–Kurtz 1986, ch. 6, §4):
with unit-rate counting processes `Y_c` and internal clocks `A_c(t) = ∫₀ᵗ rate_c` (`clock`),

  `S(t) = S(0) + Y_birth(A_birth) - Y_infection(A_infection) - Y_deathS(A_deathS)`,

and similarly for `E`, `I`, `R` (`IsChainPath`).

## Reduction to the general mass-action theorem

The chain is the stochastic mass-action system (`StochasticCRNLLN.massAction`) of the reaction
network `network` on the species `Compartment = {S, E, I, R}`: birth `∅ → S`, infection
`S + I → E + I`, progression `E → I`, recovery `I → R` and deaths `X → ∅`, with rate constants
`rateConst = (μ, β, σ, γ, μ, μ, μ, μ)`. Kurtz's theorem is therefore derived from
`StochasticCRNLLN.tendsto_measure_deviation_massAction` through two bridges:

* **rates** (`propensity_chainCRN`): the mass-action propensities are exactly the chain's rates
  `μ N`, `β S I / N`, `σ E`, `γ I`, `μ X`, with no approximation error;
* **paths** (`IsChainPath.toCRN`): `toPath S E I R t = (S, E, I, R)(max t 0)` is a chain path of
  `StochasticCRNLLN`, whose definition also asks for integrable propensities on `[t, 0]` for
  `t < 0`. On `[0, t]` integrability follows from `IsChainPath.total_le` once the birth counting
  path is nondecreasing, which unit Poisson paths are almost surely;
* **ODE** (`hasDerivAt_odePath`): `massActionField` of the network at scale `1` is the
  `SEIRVital` vector field, and both deviations are the same `ℓ¹` distance (`deviation_toPath`).

## What is specific to vital dynamics

The population is not conserved: births and deaths change `S + E + I + R`. The birth rate `μ N`
does not depend on the state, so the birth clock is `μ N t` (`clock_birth`), and the total count
is at most the initial total plus the births (`IsChainPath.total_le`). Once the birth counting
process is within `η` of its mean, every scaled count stays below
`K = (initial total) / N + μ T + η` on `[0, T]`. This a priori bound makes the pathwise estimate
`IsChainPath.deviation_le` hold for every path with explicit constants, not only near the ODE
trajectory as `StochasticCRNLLN.IsChainPath.deviation_le` does.

## Main results

* `IsChainPath.total_le`: the total count is at most the initial total plus the births.
* `IsChainPath.deviation_le`: Kurtz's pathwise estimate with explicit constants. If the scaled
  clocks satisfy `|y_c(N a) / N - a| ≤ η` on the clock range and `M` bounds the `ℓ¹` norm of the
  ODE solution on `[0, T]`, then on `[0, T]` the `ℓ¹` distance between the scaled chain and the
  ODE solution is at most `(initial distance + 11 η) e^{11 (β (K + 3 M + 1) + σ + γ + μ) t}`.
* `tendsto_measure_deviation`: **Kurtz's theorem for SEIR with vital dynamics.** If the scaled
  initial state converges in probability, then for every `T` and `ε > 0`,
  `P(∃ t ∈ [0, T], |S/N - s| + |E/N - e| + |I/N - i| + |R/N - r| ≥ ε) → 0`.
* `tendsto_measure_iSup_deviation`: the same for the supremum over `[0, T]`.
* `tendsto_measure_deviation_zero_of_initial`: the initial-condition hypothesis for deterministic
  initial counts with `S₀(N) / N → s(0)`, etc.
* `eventually_tendsto_measure_endemic`: combined with the global stability of the endemic
  equilibrium (`SEIRVital.IsSolution.tendsto_endemic`): when `R₀ > 1` and the ODE starts in the
  open positive orthant, for every `ε > 0` there is `t₀` such that at each fixed `t ≥ t₀` the
  scaled chain is within `ε` of `(S*, E*, I*)` with probability tending to `1`.

## Scope

* The theorems take the chain as given: a family of paths satisfying the time-change equations
  almost surely. **Existence of chain paths for `μ > 0` is not proved**, nor is the
  identification of their law with the jump chain (`StochasticSIRChain` does this for SIR only).
* Independence of the eight driving processes is not used, so it is not assumed.
* Only the law of large numbers is proved; no diffusion correction, and no statement uniform over
  infinite time horizons: the endemic corollary is at fixed times `t ≥ t₀`, with `N → ∞` first.
* The events over `[0, T]` are not assumed measurable; their probabilities are outer measures.

## References

* T. G. Kurtz, *Solutions of ordinary differential equations as limits of pure jump Markov
  processes*, J. Appl. Probab. 7 (1970) 49–58.
* S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley
  (1986), ch. 6, §4 and ch. 11, §2.
* H. Andersson and T. Britton, *Stochastic Epidemic Models and Their Statistical Analysis*,
  Lecture Notes in Statistics 151, Springer (2000), ch. 5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ENNReal

namespace MathlibExt.Biology.Epidemiology.StochasticSEIRVital

open MathlibExt.Biology.Dynamics

/-! ### Channels and intensities -/

/-- The eight reaction channels of the SEIR chain with vital dynamics. -/
inductive Channel where
  /-- A birth into `S`. -/
  | birth
  /-- Infection, `S → E`. -/
  | infection
  /-- End of the latent period, `E → I`. -/
  | progression
  /-- Recovery, `I → R`. -/
  | recovery
  /-- Death of a susceptible. -/
  | deathS
  /-- Death of a latent individual. -/
  | deathE
  /-- Death of an infective. -/
  | deathI
  /-- Death of a removed individual. -/
  | deathR
  deriving DecidableEq

instance : Fintype Channel where
  elems := {Channel.birth, Channel.infection, Channel.progression, Channel.recovery,
    Channel.deathS, Channel.deathE, Channel.deathI, Channel.deathR}
  complete c := by cases c <;> simp

/-- The **scaled intensity** `λ_c(s, e, i, r)` of channel `c` at the scaled state
`(s, e, i, r)`: births `μ`, infection `β s i`, progression `σ e`, recovery `γ i`, and deaths
`μ s`, `μ e`, `μ i`, `μ r`. These are the terms of the ODE at population scale `1`. -/
noncomputable def scaledRate (β σ γ μ s e i r : ℝ) : Channel → ℝ
  | .birth => μ
  | .infection => β * s * i
  | .progression => σ * e
  | .recovery => γ * i
  | .deathS => μ * s
  | .deathE => μ * e
  | .deathI => μ * i
  | .deathR => μ * r

/-- A bound for every scaled intensity on the box `[0, K]⁴` (`scaledRate_le`). -/
noncomputable def rateBound (β σ γ μ K : ℝ) : ℝ := μ + β * K ^ 2 + (σ + γ + μ) * K

section ScaledRate

variable {β σ γ μ : ℝ}

theorem scaledRate_nonneg {s e i r : ℝ} (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hs : 0 ≤ s) (he : 0 ≤ e) (hi : 0 ≤ i) (hr : 0 ≤ r) (c : Channel) :
    0 ≤ scaledRate β σ γ μ s e i r c := by
  cases c <;> simp only [scaledRate]
  · exact hμ
  · exact mul_nonneg (mul_nonneg hβ hs) hi
  · exact mul_nonneg hσ he
  · exact mul_nonneg hγ hi
  · exact mul_nonneg hμ hs
  · exact mul_nonneg hμ he
  · exact mul_nonneg hμ hi
  · exact mul_nonneg hμ hr

/-- On the box `[0, K]⁴` every scaled intensity is at most `rateBound β σ γ μ K`. -/
theorem scaledRate_le {K s e i r : ℝ} (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hs0 : 0 ≤ s) (hi0 : 0 ≤ i) (hs : s ≤ K) (he : e ≤ K)
    (hi : i ≤ K) (hr : r ≤ K) (c : Channel) :
    scaledRate β σ γ μ s e i r c ≤ rateBound β σ γ μ K := by
  have hK : 0 ≤ K := hs0.trans hs
  have h1 : 0 ≤ β * K ^ 2 := mul_nonneg hβ (sq_nonneg K)
  have h2 : 0 ≤ σ * K := mul_nonneg hσ hK
  have h3 : 0 ≤ γ * K := mul_nonneg hγ hK
  have h4 : 0 ≤ μ * K := mul_nonneg hμ hK
  have hexp : rateBound β σ γ μ K = μ + β * K ^ 2 + σ * K + γ * K + μ * K := by
    rw [rateBound]; ring
  rw [hexp]
  cases c <;> simp only [scaledRate]
  · linarith
  · have h5 : s * i ≤ K * K := mul_le_mul hs hi hi0 hK
    have h6 : β * (s * i) ≤ β * (K * K) := mul_le_mul_of_nonneg_left h5 hβ
    nlinarith
  · have := mul_le_mul_of_nonneg_left he hσ; linarith
  · have := mul_le_mul_of_nonneg_left hi hγ; linarith
  · have := mul_le_mul_of_nonneg_left hs hμ; linarith
  · have := mul_le_mul_of_nonneg_left he hμ; linarith
  · have := mul_le_mul_of_nonneg_left hi hμ; linarith
  · have := mul_le_mul_of_nonneg_left hr hμ; linarith

/-- **Lipschitz bound for the scaled intensities.** If `0 ≤ s ≤ K` and `|i'| ≤ M`, then every
channel's intensity at `(s, e, i, r)` differs from that at `(s', e', i', r')` by at most
`(β (K + M) + σ + γ + μ)` times the `ℓ¹` distance. Only the infection term `β s i` is nonlinear;
it needs the two bounds. -/
theorem abs_scaledRate_sub_le {K M s e i r s' e' i' r' : ℝ} (hβ : 0 ≤ β) (hσ : 0 ≤ σ)
    (hγ : 0 ≤ γ) (hμ : 0 ≤ μ) (hs0 : 0 ≤ s) (hsK : s ≤ K) (hi' : |i'| ≤ M) (c : Channel) :
    |scaledRate β σ γ μ s e i r c - scaledRate β σ γ μ s' e' i' r' c| ≤
      (β * (K + M) + σ + γ + μ) * (|s - s'| + |e - e'| + |i - i'| + |r - r'|) := by
  have hK : 0 ≤ K := hs0.trans hsK
  have hM : 0 ≤ M := (abs_nonneg _).trans hi'
  set D := |s - s'| + |e - e'| + |i - i'| + |r - r'|
  have a1 := abs_nonneg (s - s')
  have a2 := abs_nonneg (e - e')
  have a3 := abs_nonneg (i - i')
  have a4 := abs_nonneg (r - r')
  have hDs : |s - s'| ≤ D := by linarith
  have hDe : |e - e'| ≤ D := by linarith
  have hDi : |i - i'| ≤ D := by linarith
  have hDr : |r - r'| ≤ D := by linarith
  have hD0 : 0 ≤ D := a1.trans hDs
  have hβKM : 0 ≤ β * (K + M) := mul_nonneg hβ (by linarith)
  have key : ∀ a, 0 ≤ a → a ≤ β * (K + M) + σ + γ + μ → ∀ d, 0 ≤ d → d ≤ D →
      a * d ≤ (β * (K + M) + σ + γ + μ) * D :=
    fun a _ haL d hd hdD => mul_le_mul haL hdD hd (by linarith)
  cases c <;> simp only [scaledRate]
  · rw [sub_self, abs_zero]
    exact mul_nonneg (by linarith) hD0
  · have h1 : β * s * i - β * s' * i' = β * (s * (i - i') + i' * (s - s')) := by ring
    rw [h1, abs_mul, abs_of_nonneg hβ]
    have h2 : |s * (i - i') + i' * (s - s')| ≤ (K + M) * D := by
      calc _ ≤ |s * (i - i')| + |i' * (s - s')| := abs_add_le _ _
        _ = s * |i - i'| + |i'| * |s - s'| := by rw [abs_mul, abs_mul, abs_of_nonneg hs0]
        _ ≤ K * D + M * D :=
            add_le_add (mul_le_mul hsK hDi a3 hK) (mul_le_mul hi' hDs a1 hM)
        _ = (K + M) * D := by ring
    calc _ ≤ β * ((K + M) * D) := mul_le_mul_of_nonneg_left h2 hβ
      _ = (β * (K + M)) * D := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hD0
  · rw [← mul_sub, abs_mul, abs_of_nonneg hσ]
    exact key σ hσ (by linarith) _ a2 hDe
  · rw [← mul_sub, abs_mul, abs_of_nonneg hγ]
    exact key γ hγ (by linarith) _ a3 hDi
  · rw [← mul_sub, abs_mul, abs_of_nonneg hμ]
    exact key μ hμ (by linarith) _ a1 hDs
  · rw [← mul_sub, abs_mul, abs_of_nonneg hμ]
    exact key μ hμ (by linarith) _ a2 hDe
  · rw [← mul_sub, abs_mul, abs_of_nonneg hμ]
    exact key μ hμ (by linarith) _ a3 hDi
  · rw [← mul_sub, abs_mul, abs_of_nonneg hμ]
    exact key μ hμ (by linarith) _ a4 hDr

end ScaledRate

/-! ### The chain -/

/-- The **intensity of channel `c` at time `x`** along the count paths `(S, E, I, R)` at
population scale `N`, in Kurtz's density-dependent form
`N · λ_c(S(x) / N, E(x) / N, I(x) / N, R(x) / N)`. For `N > 0` these are the Markov rates
`μ N`, `β S I / N`, `σ E`, `γ I`, `μ S`, `μ E`, `μ I`, `μ R` (`rate_birth`, `rate_infection`,
…). -/
noncomputable def rate (β σ γ μ : ℝ) (N : ℕ) (S E I R : ℝ → ℕ) (c : Channel) (x : ℝ) : ℝ :=
  N * scaledRate β σ γ μ ((S x : ℝ) / N) ((E x : ℝ) / N) ((I x : ℝ) / N) ((R x : ℝ) / N) c

/-- The **internal clock of channel `c`** at time `t`: the integrated intensity `∫₀ᵗ rate_c`
(truncated at `0` so it can be fed to a counting process indexed by `ℝ≥0`). -/
noncomputable def clock (β σ γ μ : ℝ) (N : ℕ) (S E I R : ℝ → ℕ) (c : Channel) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (∫ x in (0 : ℝ)..t, rate β σ γ μ N S E I R c x)

private theorem natCast_mul_div {N : ℕ} (hN : 0 < N) (a : ℝ) : (N : ℝ) * (a / N) = a := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  calc (N : ℝ) * (a / N) = a * ((N : ℝ) / N) := by ring
    _ = a := by rw [div_self hN', mul_one]

section Rates

variable {β σ γ μ : ℝ} {N : ℕ} {S E I R : ℝ → ℕ} {x : ℝ}

theorem rate_birth : rate β σ γ μ N S E I R .birth x = μ * N := by
  simp only [rate, scaledRate]; ring

theorem rate_infection (hN : 0 < N) :
    rate β σ γ μ N S E I R .infection x = β * S x * I x / N := by
  simp only [rate, scaledRate]
  calc _ = β * ((N : ℝ) * ((S x : ℝ) / N)) * I x / N := by ring
    _ = _ := by rw [natCast_mul_div hN]

theorem rate_progression (hN : 0 < N) : rate β σ γ μ N S E I R .progression x = σ * E x := by
  simp only [rate, scaledRate]
  calc _ = σ * ((N : ℝ) * ((E x : ℝ) / N)) := by ring
    _ = _ := by rw [natCast_mul_div hN]

theorem rate_recovery (hN : 0 < N) : rate β σ γ μ N S E I R .recovery x = γ * I x := by
  simp only [rate, scaledRate]
  calc _ = γ * ((N : ℝ) * ((I x : ℝ) / N)) := by ring
    _ = _ := by rw [natCast_mul_div hN]

theorem rate_deathS (hN : 0 < N) : rate β σ γ μ N S E I R .deathS x = μ * S x := by
  simp only [rate, scaledRate]
  calc _ = μ * ((N : ℝ) * ((S x : ℝ) / N)) := by ring
    _ = _ := by rw [natCast_mul_div hN]

theorem rate_deathE (hN : 0 < N) : rate β σ γ μ N S E I R .deathE x = μ * E x := by
  simp only [rate, scaledRate]
  calc _ = μ * ((N : ℝ) * ((E x : ℝ) / N)) := by ring
    _ = _ := by rw [natCast_mul_div hN]

theorem rate_deathI (hN : 0 < N) : rate β σ γ μ N S E I R .deathI x = μ * I x := by
  simp only [rate, scaledRate]
  calc _ = μ * ((N : ℝ) * ((I x : ℝ) / N)) := by ring
    _ = _ := by rw [natCast_mul_div hN]

theorem rate_deathR (hN : 0 < N) : rate β σ γ μ N S E I R .deathR x = μ * R x := by
  simp only [rate, scaledRate]
  calc _ = μ * ((N : ℝ) * ((R x : ℝ) / N)) := by ring
    _ = _ := by rw [natCast_mul_div hN]

/-- The clock in scaled form: `A_c(t) = N ∫₀ᵗ λ_c(S / N, E / N, I / N, R / N)`. -/
theorem clock_eq (c : Channel) (t : ℝ) :
    clock β σ γ μ N S E I R c t = Real.toNNReal (N * ∫ x in (0 : ℝ)..t,
      scaledRate β σ γ μ ((S x : ℝ) / N) ((E x : ℝ) / N) ((I x : ℝ) / N) ((R x : ℝ) / N) c) := by
  unfold clock rate
  rw [intervalIntegral.integral_const_mul]

end Rates

/-- The birth clock does not depend on the state: `A_birth(t) = N μ t`. -/
theorem clock_birth (β σ γ μ : ℝ) (N : ℕ) (S E I R : ℝ → ℕ) (t : ℝ) :
    clock β σ γ μ N S E I R .birth t = Real.toNNReal (N * (μ * t)) := by
  rw [clock_eq]
  congr 1
  simp only [scaledRate, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

/-- **One sample path of the stochastic SEIR chain with vital dynamics** at population scale `N`
(Kurtz's random time-change representation; Ethier–Kurtz 1986, ch. 6, (4.1) and ch. 11, (2.1)).
Given the paths `y c` of the eight driving unit-rate counting processes, the counts
`S, E, I, R : ℝ → ℕ` satisfy, for `t ≥ 0`, writing `Y_c = y c (clock c t)`,

  `S(t) = S(0) + Y_birth - Y_infection - Y_deathS`,
  `E(t) = E(0) + Y_infection - Y_progression - Y_deathE`,
  `I(t) = I(0) + Y_progression - Y_recovery - Y_deathI`,
  `R(t) = R(0) + Y_recovery - Y_deathR`.

When the `y c` are independent unit-rate Poisson processes this is the continuous-time Markov
chain with the jumps and rates of the module docstring. The counts are natural numbers, so they
are nonnegative by construction; the paths are required to be measurable (a càdlàg path is), so
that the clocks are genuine Lebesgue integrals. The population is not conserved, and `N` is the
scale of the birth rate `μ N` and of the incidence `β S I / N`, not the size of the initial
population. -/
structure IsChainPath (β σ γ μ : ℝ) (N : ℕ) (y : Channel → ℝ≥0 → ℕ) (S E I R : ℝ → ℕ) :
    Prop where
  /-- The susceptible path is measurable. -/
  measurable_susceptible : Measurable S
  /-- The latent path is measurable. -/
  measurable_exposed : Measurable E
  /-- The infective path is measurable. -/
  measurable_infected : Measurable I
  /-- The removed path is measurable. -/
  measurable_removed : Measurable R
  /-- Births enter `S`; susceptibles leave by infection and by death. -/
  susceptible_eq : ∀ t, 0 ≤ t → (S t : ℝ) = S 0 + y .birth (clock β σ γ μ N S E I R .birth t) -
    y .infection (clock β σ γ μ N S E I R .infection t) -
    y .deathS (clock β σ γ μ N S E I R .deathS t)
  /-- Newly infected individuals enter `E`, which they leave by progression and by death. -/
  exposed_eq : ∀ t, 0 ≤ t → (E t : ℝ) = E 0 +
    y .infection (clock β σ γ μ N S E I R .infection t) -
    y .progression (clock β σ γ μ N S E I R .progression t) -
    y .deathE (clock β σ γ μ N S E I R .deathE t)
  /-- Latent individuals become infective; infectives leave by recovery and by death. -/
  infected_eq : ∀ t, 0 ≤ t → (I t : ℝ) = I 0 +
    y .progression (clock β σ γ μ N S E I R .progression t) -
    y .recovery (clock β σ γ μ N S E I R .recovery t) -
    y .deathI (clock β σ γ μ N S E I R .deathI t)
  /-- Recovered individuals enter `R`, which they leave by death. -/
  removed_eq : ∀ t, 0 ≤ t → (R t : ℝ) = R 0 +
    y .recovery (clock β σ γ μ N S E I R .recovery t) -
    y .deathR (clock β σ γ μ N S E I R .deathR t)

/-- The `ℓ¹` distance at time `t` between the scaled chain `(S, E, I, R) / N` and a deterministic
path `(s, e, i, r)`. -/
noncomputable def deviation (N : ℕ) (S E I R : ℝ → ℕ) (s e i r : ℝ → ℝ) (t : ℝ) : ℝ :=
  |(S t : ℝ) / N - s t| + |(E t : ℝ) / N - e t| + |(I t : ℝ) / N - i t| +
    |(R t : ℝ) / N - r t|

/-! ### The reaction network -/

/-- The four compartments, the species of the reaction network. -/
inductive Compartment where
  /-- Susceptible. -/
  | S
  /-- Exposed (latent). -/
  | E
  /-- Infective. -/
  | I
  /-- Removed. -/
  | R
  deriving DecidableEq

instance : Fintype Compartment where
  elems := {Compartment.S, Compartment.E, Compartment.I, Compartment.R}
  complete c := by cases c <;> simp

/-- The vector with entries `a, b, c, d` at `S, E, I, R`. -/
def vec4 {α : Type*} (a b c d : α) : Compartment → α
  | .S => a
  | .E => b
  | .I => c
  | .R => d

theorem sum_compartment {M : Type*} [AddCommMonoid M] (f : Compartment → M) :
    ∑ c, f c = f .S + f .E + f .I + f .R := by
  change ∑ c ∈ {Compartment.S, Compartment.E, Compartment.I, Compartment.R}, f c = _
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_singleton]
  simp only [add_assoc]

theorem prod_compartment {M : Type*} [CommMonoid M] (f : Compartment → M) :
    ∏ c, f c = f .S * f .E * f .I * f .R := by
  change ∏ c ∈ {Compartment.S, Compartment.E, Compartment.I, Compartment.R}, f c = _
  rw [Finset.prod_insert (by simp), Finset.prod_insert (by simp), Finset.prod_insert (by simp),
    Finset.prod_singleton]
  simp only [mul_assoc]

theorem sum_channel {M : Type*} [AddCommMonoid M] (f : Channel → M) :
    ∑ c, f c = f .birth + f .infection + f .progression + f .recovery + f .deathS + f .deathE +
      f .deathI + f .deathR := by
  change ∑ c ∈ {Channel.birth, Channel.infection, Channel.progression, Channel.recovery,
    Channel.deathS, Channel.deathE, Channel.deathI, Channel.deathR}, f c = _
  rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp),
    Finset.sum_insert (by simp), Finset.sum_singleton]
  simp only [add_assoc]

/-- The reactant complexes: infection `S + I`, progression `E`, recovery `I`, each death its
compartment, birth nothing. -/
def networkSrc : Channel → Compartment → ℕ
  | .birth => vec4 0 0 0 0
  | .infection => vec4 1 0 1 0
  | .progression => vec4 0 1 0 0
  | .recovery => vec4 0 0 1 0
  | .deathS => vec4 1 0 0 0
  | .deathE => vec4 0 1 0 0
  | .deathI => vec4 0 0 1 0
  | .deathR => vec4 0 0 0 1

/-- The product complexes: birth `S`, infection `E + I`, progression `I`, recovery `R`, each
death nothing. -/
def networkProd : Channel → Compartment → ℕ
  | .birth => vec4 1 0 0 0
  | .infection => vec4 0 1 1 0
  | .progression => vec4 0 0 1 0
  | .recovery => vec4 0 0 0 1
  | .deathS => vec4 0 0 0 0
  | .deathE => vec4 0 0 0 0
  | .deathI => vec4 0 0 0 0
  | .deathR => vec4 0 0 0 0

/-- **The SEIR network with vital dynamics**: `∅ → S`, `S + I → E + I`, `E → I`, `I → R` and
`X → ∅` for each compartment `X`. -/
def network : ComplexBalanced.ReactionNetwork Compartment Channel :=
  ⟨networkSrc, networkProd⟩

/-- The rate constants `(μ, β, σ, γ, μ, μ, μ, μ)` of the eight reactions. -/
def rateConst (β σ γ μ : ℝ) : Channel → ℝ
  | .birth => μ
  | .infection => β
  | .progression => σ
  | .recovery => γ
  | .deathS => μ
  | .deathE => μ
  | .deathI => μ
  | .deathR => μ

theorem rateConst_nonneg {β σ γ μ : ℝ} (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (c : Channel) : 0 ≤ rateConst β σ γ μ c := by
  cases c <;> simp only [rateConst] <;> assumption

/-- The stochastic mass-action system of `network` at system size `N`. -/
noncomputable abbrev chainCRN (β σ γ μ : ℝ) (hκ : ∀ c, 0 ≤ rateConst β σ γ μ c) (N : ℕ) :
    StochasticCRNNonExplosion.StochasticCRN Compartment Channel :=
  StochasticCRNLLN.massAction network (rateConst β σ γ μ) hκ N

section Bridge

variable {β σ γ μ : ℝ} {N : ℕ}

theorem chainCRN_network (hκ : ∀ c, 0 ≤ rateConst β σ γ μ c) :
    (chainCRN β σ γ μ hκ N).network = network :=
  rfl

/-- The deterministic mass-action rate of each reaction is the scaled intensity `scaledRate`. -/
theorem networkRate_eq (u : Compartment → ℝ) (c : Channel) :
    network.rate (rateConst β σ γ μ) u c = scaledRate β σ γ μ (u .S) (u .E) (u .I) (u .R) c := by
  simp only [ComplexBalanced.ReactionNetwork.rate, prod_compartment]
  cases c <;> simp [network, networkSrc, vec4, rateConst, scaledRate]
  ring

/-- **The rates match exactly.** The stochastic mass-action propensity of each reaction is the
chain's intensity `N λ_c(z / N)`: `μ N`, `β S I / N`, `σ E`, `γ I`, `μ S`, `μ E`, `μ I`, `μ R`. -/
theorem propensity_chainCRN (hκ : ∀ c, 0 ≤ rateConst β σ γ μ c) (N : ℕ) (c : Channel)
    (z : Compartment → ℕ) :
    (chainCRN β σ γ μ hκ N).propensity c z = N * scaledRate β σ γ μ ((z .S : ℝ) / N)
      ((z .E : ℝ) / N) ((z .I : ℝ) / N) ((z .R : ℝ) / N) c := by
  change StochasticCRNLLN.massActionPropensity network (rateConst β σ γ μ) N c z = _
  rw [StochasticCRNLLN.massActionPropensity_eq_prod, prod_compartment]
  cases c <;> simp [network, networkSrc, vec4, rateConst, scaledRate] <;> ring

/-- The sum `Z = ∑_c ‖ζ_c‖₁` of the jump sizes is `1 + 2 + 2 + 2 + 1 + 1 + 1 + 1 = 11`. -/
theorem stoichNorm_network : StochasticCRNLLN.stoichNorm network = 11 := by
  simp [StochasticCRNLLN.stoichNorm, StochasticCRNLLN.l1Norm, StochasticCRNLLN.reactionVector,
    sum_channel, sum_compartment, network, networkSrc, networkProd, vec4]
  norm_num

theorem l1Norm_eq (u : Compartment → ℝ) :
    StochasticCRNLLN.l1Norm u = |u .S| + |u .E| + |u .I| + |u .R| :=
  sum_compartment _

theorem abs_le_l1Norm (u : Compartment → ℝ) (c : Compartment) :
    |u c| ≤ StochasticCRNLLN.l1Norm u :=
  Finset.single_le_sum (f := fun c => |u c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)

/-- The count path of `StochasticCRNLLN`: the counts `(S, E, I, R)` at time `max t 0`, so that it
is constant on `(-∞, 0]`, where `IsChainPath` says nothing. -/
noncomputable def toPath (S E I R : ℝ → ℕ) (t : ℝ) : Compartment → ℕ :=
  vec4 (S (max t 0)) (E (max t 0)) (I (max t 0)) (R (max t 0))

/-- A deterministic path `(s, e, i, r)` as a function into `Compartment → ℝ`. -/
def odePath (s e i r : ℝ → ℝ) (t : ℝ) : Compartment → ℝ :=
  vec4 (s t) (e t) (i t) (r t)

/-- **The deviations agree**: on `t ≥ 0` the `ℓ¹` deviation of `StochasticCRNLLN` is `deviation`. -/
theorem deviation_toPath {S E I R : ℝ → ℕ} {s e i r : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) :
    StochasticCRNLLN.deviation N (toPath S E I R) (odePath s e i r) t =
      deviation N S E I R s e i r t := by
  simp only [StochasticCRNLLN.deviation, l1Norm_eq, Pi.sub_apply, StochasticCRNLLN.scaled, toPath,
    odePath, vec4, max_eq_left ht, deviation]

/-- **The ODEs agree**: a solution of the SEIR system with vital dynamics at scale `1` solves the
deterministic mass-action system `x' = massActionField κ x` of `network`. -/
theorem hasDerivAt_odePath {s e i r : ℝ → ℝ} (hode : SEIRVital.IsSolution β σ γ μ 1 s e i r) :
    ∀ t, 0 ≤ t → ∀ c, HasDerivAt (fun τ => odePath s e i r τ c)
      (network.massActionField (rateConst β σ γ μ) (odePath s e i r t) c) t := by
  intro t ht c
  cases c
  · refine (hode.hasDerivAt_susceptible t ht).congr_deriv ?_
    simp [ComplexBalanced.ReactionNetwork.massActionField, sum_channel, prod_compartment, network,
      networkSrc, networkProd, vec4, rateConst, odePath]
    ring
  · refine (hode.hasDerivAt_exposed t ht).congr_deriv ?_
    simp [ComplexBalanced.ReactionNetwork.massActionField, sum_channel, prod_compartment, network,
      networkSrc, networkProd, vec4, rateConst, odePath]
    ring
  · refine (hode.hasDerivAt_infected t ht).congr_deriv ?_
    simp [ComplexBalanced.ReactionNetwork.massActionField, sum_channel, prod_compartment, network,
      networkSrc, networkProd, vec4, rateConst, odePath]
    ring
  · refine (hode.hasDerivAt_removed t ht).congr_deriv ?_
    simp [ComplexBalanced.ReactionNetwork.massActionField, sum_channel, prod_compartment, network,
      networkSrc, networkProd, vec4, rateConst, odePath]
    ring

variable {S E I R : ℝ → ℕ}

theorem propensity_toPath (hκ : ∀ c, 0 ≤ rateConst β σ γ μ c) {u : ℝ} (hu : 0 ≤ u)
    (c : Channel) :
    (chainCRN β σ γ μ hκ N).propensity c (toPath S E I R u) = rate β σ γ μ N S E I R c u := by
  rw [propensity_chainCRN]
  simp only [toPath, vec4, max_eq_left hu, rate]

/-- **The clocks agree** on `t ≥ 0`. -/
theorem clock_toPath (hκ : ∀ c, 0 ≤ rateConst β σ γ μ c) {c : Channel} {t : ℝ} (ht : 0 ≤ t) :
    StochasticCRNLLN.clock (chainCRN β σ γ μ hκ N) c (toPath S E I R) t =
      clock β σ γ μ N S E I R c t := by
  unfold StochasticCRNLLN.clock clock
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le ht] at hu
  exact propensity_toPath hκ hu.1 c

theorem measurable_scaledRate {a b c d : ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hc : Measurable c) (hd : Measurable d) (ch : Channel) :
    Measurable fun t => scaledRate β σ γ μ (a t) (b t) (c t) (d t) ch := by
  cases ch
  · exact measurable_const
  · exact (ha.const_mul β).mul hc
  · exact hb.const_mul σ
  · exact hc.const_mul γ
  · exact ha.const_mul μ
  · exact hb.const_mul μ
  · exact hc.const_mul μ
  · exact hd.const_mul μ

end Bridge

private theorem abs_sub_le_add_abs {a b : ℝ} (ha : 0 ≤ a) : |a - b| ≤ a + |b| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self b, neg_abs_le b]

namespace IsChainPath

variable {β σ γ μ : ℝ} {N : ℕ} {y : Channel → ℝ≥0 → ℕ} {S E I R : ℝ → ℕ}

/-- **The population grows only by births.** Along a chain path, at every `t ≥ 0`,
`S + E + I + R ≤ S(0) + E(0) + I(0) + R(0) + Y_birth(N μ t)`. -/
theorem total_le (h : IsChainPath β σ γ μ N y S E I R) {t : ℝ} (ht : 0 ≤ t) :
    (S t : ℝ) + E t + I t + R t ≤
      (S 0 : ℝ) + E 0 + I 0 + R 0 + y .birth (clock β σ γ μ N S E I R .birth t) := by
  have h1 := h.susceptible_eq t ht
  have h2 := h.exposed_eq t ht
  have h3 := h.infected_eq t ht
  have h4 := h.removed_eq t ht
  have d1 : (0 : ℝ) ≤ y .deathS (clock β σ γ μ N S E I R .deathS t) := Nat.cast_nonneg _
  have d2 : (0 : ℝ) ≤ y .deathE (clock β σ γ μ N S E I R .deathE t) := Nat.cast_nonneg _
  have d3 : (0 : ℝ) ≤ y .deathI (clock β σ γ μ N S E I R .deathI t) := Nat.cast_nonneg _
  have d4 : (0 : ℝ) ≤ y .deathR (clock β σ γ μ N S E I R .deathR t) := Nat.cast_nonneg _
  linarith

/-- **The path bridge.** A chain path whose birth counting path is nondecreasing (as unit Poisson
paths are, almost surely) gives a chain path `toPath S E I R` of the stochastic mass-action system
`chainCRN` in the sense of `StochasticCRNLLN.IsChainPath`. The propensities along `toPath` are
constant on `(-∞, 0]`; on `[0, t]` every count is at most the initial total plus the births up to
time `t` (`total_le`), so they are bounded. -/
theorem toCRN (h : IsChainPath β σ γ μ N y S E I R) (hκ : ∀ c, 0 ≤ rateConst β σ γ μ c)
    (hmono : Monotone (y .birth)) :
    StochasticCRNLLN.IsChainPath (chainCRN β σ γ μ hκ N) y (toPath S E I R) := by
  have hmax : Measurable fun t : ℝ => max t 0 := (continuous_id.max continuous_const).measurable
  have hS := h.measurable_susceptible.comp hmax
  have hE := h.measurable_exposed.comp hmax
  have hI := h.measurable_infected.comp hmax
  have hR := h.measurable_removed.comp hmax
  have hμ : 0 ≤ μ := hκ .birth
  have hβ : 0 ≤ β := hκ .infection
  have hσ : 0 ≤ σ := hκ .progression
  have hγ : 0 ≤ γ := hκ .recovery
  refine ⟨fun c => ?_, fun c t => ?_, fun t ht i => ?_⟩
  · cases c
    · exact hS
    · exact hE
    · exact hI
    · exact hR
  · -- every count at a time in `[0, max t 0]` is at most `tot`
    obtain ⟨tot, htot⟩ : ∃ tot : ℝ, tot = (S 0 : ℝ) + E 0 + I 0 + R 0 +
        y .birth (Real.toNNReal (N * (μ * max t 0))) := ⟨_, rfl⟩
    have hcount : ∀ x, max x 0 ≤ max t 0 → ∀ d, (toPath S E I R x d : ℝ) ≤ tot := by
      intro x hx d
      have htl := h.total_le (le_max_right x 0)
      rw [clock_birth] at htl
      have hy : (y .birth (Real.toNNReal (N * (μ * max x 0))) : ℝ) ≤
          y .birth (Real.toNNReal (N * (μ * max t 0))) :=
        Nat.cast_le.2 (hmono (Real.toNNReal_le_toNNReal
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx hμ) (Nat.cast_nonneg _))))
      have c1 : (0 : ℝ) ≤ S (max x 0) := Nat.cast_nonneg _
      have c2 : (0 : ℝ) ≤ E (max x 0) := Nat.cast_nonneg _
      have c3 : (0 : ℝ) ≤ I (max x 0) := Nat.cast_nonneg _
      have c4 : (0 : ℝ) ≤ R (max x 0) := Nat.cast_nonneg _
      cases d <;> simp only [toPath, vec4] <;> linarith
    have hprop : ∀ x, max x 0 ≤ max t 0 →
        0 ≤ (chainCRN β σ γ μ hκ N).propensity c (toPath S E I R x) ∧
          (chainCRN β σ γ μ hκ N).propensity c (toPath S E I R x) ≤
            N * rateBound β σ γ μ (tot / N) := by
      intro x hx
      refine ⟨(chainCRN β σ γ μ hκ N).propensity_nonneg c _, ?_⟩
      rw [propensity_chainCRN]
      have hdiv : ∀ d, (toPath S E I R x d : ℝ) / N ≤ tot / N := fun d =>
        div_le_div_of_nonneg_right (hcount x hx d) (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left (scaledRate_le hβ hσ hγ hμ (by positivity) (by positivity)
        (hdiv .S) (hdiv .E) (hdiv .I) (hdiv .R) c) (Nat.cast_nonneg _)
    have hS' : Measurable fun x => (S (max x 0) : ℝ) / N :=
      (measurable_from_nat.comp hS).div_const _
    have hE' : Measurable fun x => (E (max x 0) : ℝ) / N :=
      (measurable_from_nat.comp hE).div_const _
    have hI' : Measurable fun x => (I (max x 0) : ℝ) / N :=
      (measurable_from_nat.comp hI).div_const _
    have hR' : Measurable fun x => (R (max x 0) : ℝ) / N :=
      (measurable_from_nat.comp hR).div_const _
    have hmeas : Measurable fun x => (chainCRN β σ γ μ hκ N).propensity c (toPath S E I R x) := by
      have : (fun x => (chainCRN β σ γ μ hκ N).propensity c (toPath S E I R x)) = fun x =>
          (N : ℝ) * scaledRate β σ γ μ ((S (max x 0) : ℝ) / N) ((E (max x 0) : ℝ) / N)
            ((I (max x 0) : ℝ) / N) ((R (max x 0) : ℝ) / N) c :=
        funext fun x => propensity_chainCRN hκ N c _
      rw [this]
      exact (measurable_scaledRate hS' hE' hI' hR' c).const_mul _
    refine (intervalIntegrable_const (c := (N : ℝ) * rateBound β σ γ μ (tot / N))).mono_fun
      hmeas.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun x hx => ?_))
    have hxu : max x 0 ≤ max t 0 := by
      rcases Set.mem_uIcc.1 (Set.uIoc_subset_uIcc hx) with hx' | hx'
      · exact max_le_max hx'.2 le_rfl
      · exact max_le (hx'.2.trans (le_max_right _ _)) (le_max_right _ _)
    obtain ⟨h1, h2⟩ := hprop x hxu
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg h1, abs_of_nonneg (h1.trans h2)]
    exact h2
  · simp only [sum_channel, clock_toPath hκ ht]
    have ht' : max t 0 = t := max_eq_left ht
    cases i
    · have := h.susceptible_eq t ht
      simp [toPath, vec4, ht', StochasticCRNLLN.reactionVector, chainCRN_network, network,
        networkSrc, networkProd]
      linarith
    · have := h.exposed_eq t ht
      simp [toPath, vec4, ht', StochasticCRNLLN.reactionVector, chainCRN_network, network,
        networkSrc, networkProd]
      linarith
    · have := h.infected_eq t ht
      simp [toPath, vec4, ht', StochasticCRNLLN.reactionVector, chainCRN_network, network,
        networkSrc, networkProd]
      linarith
    · have := h.removed_eq t ht
      simp [toPath, vec4, ht', StochasticCRNLLN.reactionVector, chainCRN_network, network,
        networkSrc, networkProd]
      linarith

/-- **Kurtz's pathwise estimate for SEIR with vital dynamics**, for every path and with explicit
constants. Let `(S, E, I, R)` be a chain path at scale `N ≥ 1` with nondecreasing birth counting
path and `(s, e, i, r)` a solution of the SEIR system with vital dynamics at scale `1`. Suppose
that on `[0, T]`

* `|s| + |e| + |i| + |r| ≤ M`, and
* every scaled driving count stays within `η` of the identity on the clock range:
  `|y_c(N a) / N - a| ≤ η` for `a ∈ [0, (rateBound (K + 2 M + 1) + 1) T]`, where
  `K ≥ (S(0) + E(0) + I(0) + R(0)) / N + μ T + η`.

Then on `[0, T]`

  `deviation ≤ (initial deviation + 11 η) e^{11 (β (K + 3 M + 1) + σ + γ + μ) t}`.

Proof: the birth count bounds the total (`total_le`), so every scaled count is at most `K` and the
deviation at most `K + M` on `[0, T]`. The whole path therefore lies in the tube of radius
`K + M + 1` around the ODE solution, on which the scaled propensities are bounded by
`rateBound (K + 2 M + 1)` and Lipschitz with constant `β (K + 3 M + 1) + σ + γ + μ`
(`abs_scaledRate_sub_le`). Gronwall inside the tube
(`StochasticCRNLLN.IsChainPath.deviation_le_of_tube`, with `Z = stoichNorm network = 11`) gives
the bound. -/
theorem deviation_le (h : IsChainPath β σ γ μ N y S E I R) (hN : 0 < N) (hβ : 0 ≤ β)
    (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ) (hmono : Monotone (y .birth)) {s e i r : ℝ → ℝ}
    (hode : SEIRVital.IsSolution β σ γ μ 1 s e i r) {T K M η : ℝ} (hη : 0 ≤ η)
    (hK : ((S 0 : ℝ) + E 0 + I 0 + R 0) / N + μ * T + η ≤ K)
    (hM : ∀ x ∈ Icc 0 T, |s x| + |e x| + |i x| + |r x| ≤ M)
    (hy : ∀ c, ∀ a ∈ Icc 0 ((rateBound β σ γ μ (K + 2 * M + 1) + 1) * T),
      |(y c (Real.toNNReal (N * a)) : ℝ) / N - a| ≤ η) :
    ∀ t ∈ Icc 0 T, deviation N S E I R s e i r t ≤
      (deviation N S E I R s e i r 0 + 11 * η) *
        exp (11 * (β * (K + 3 * M + 1) + σ + γ + μ) * t) := by
  intro t₀ ht₀
  have hT : 0 ≤ T := ht₀.1.trans ht₀.2
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hM0 : 0 ≤ M :=
    (by positivity : (0 : ℝ) ≤ |s 0| + |e 0| + |i 0| + |r 0|).trans (hM 0 ⟨le_rfl, hT⟩)
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ((S 0 : ℝ) + E 0 + I 0 + R 0) / N := by positivity
    have := mul_nonneg hμ hT
    linarith
  have hκ := rateConst_nonneg hβ hσ hγ hμ
  have hμB : μ ≤ rateBound β σ γ μ (K + 2 * M + 1) := by
    have h1 := mul_nonneg hβ (sq_nonneg (K + 2 * M + 1))
    have h2 := mul_nonneg (add_nonneg (add_nonneg hσ hγ) hμ)
      (by linarith : (0 : ℝ) ≤ K + 2 * M + 1)
    unfold rateBound
    linarith
  have hB0 : 0 ≤ rateBound β σ γ μ (K + 2 * M + 1) := hμ.trans hμB
  have hL0 : 0 ≤ β * (K + 3 * M + 1) + σ + γ + μ := by
    have := mul_nonneg hβ (by linarith : (0 : ℝ) ≤ K + 3 * M + 1)
    linarith
  have hode' : StochasticCRNLLN.IsSolution (chainCRN β σ γ μ hκ N).network
      (fun c u => network.rate (rateConst β σ γ μ) u c) (odePath s e i r) :=
    ⟨fun t ht c => hasDerivAt_odePath hode t ht c⟩
  have hxM : ∀ τ ∈ Icc 0 T, ∀ c, |odePath s e i r τ c| ≤ M := fun τ hτ c =>
    (abs_le_l1Norm _ c).trans ((l1Norm_eq _).trans_le (hM τ hτ))
  -- a priori bound: the scaled total stays below `K` on `[0, T]`
  have htot : ∀ τ ∈ Icc 0 T, ((S τ : ℝ) + E τ + I τ + R τ) / N ≤ K := fun τ hτ => by
    have htl := h.total_le hτ.1
    rw [clock_birth] at htl
    have hb := hy .birth (μ * τ) ⟨mul_nonneg hμ hτ.1, (mul_le_mul_of_nonneg_left hτ.2 hμ).trans
      (mul_le_mul_of_nonneg_right (by linarith) hT)⟩
    rw [abs_le] at hb
    have h1 : ((S τ : ℝ) + E τ + I τ + R τ) / N ≤ ((S 0 : ℝ) + E 0 + I 0 + R 0) / N +
        (y .birth (Real.toNNReal (N * (μ * τ))) : ℝ) / N := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right htl hNr.le
    have h2 : μ * τ ≤ μ * T := mul_le_mul_of_nonneg_left hτ.2 hμ
    linarith [hb.2]
  -- so the path never leaves the tube of radius `K + M + 1`
  have htube : ∀ τ ∈ Ico 0 T,
      StochasticCRNLLN.deviation N (toPath S E I R) (odePath s e i r) τ < K + M + 1 := by
    intro τ hτ
    have hτ' : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.le⟩
    rw [deviation_toPath hτ.1]
    have h1 := htot τ hτ'
    have h2 := hM τ hτ'
    have hsplit : ((S τ : ℝ) + E τ + I τ + R τ) / N =
        (S τ : ℝ) / N + (E τ : ℝ) / N + (I τ : ℝ) / N + (R τ : ℝ) / N := by ring
    have a1 := abs_sub_le_add_abs (a := (S τ : ℝ) / N) (b := s τ) (by positivity)
    have a2 := abs_sub_le_add_abs (a := (E τ : ℝ) / N) (b := e τ) (by positivity)
    have a3 := abs_sub_le_add_abs (a := (I τ : ℝ) / N) (b := i τ) (by positivity)
    have a4 := abs_sub_le_add_abs (a := (R τ : ℝ) / N) (b := r τ) (by positivity)
    unfold deviation
    linarith
  -- inside the tube every scaled count is at most `K + 2 M + 1`
  have hz : ∀ τ ∈ Icc 0 T, ∀ z : Compartment → ℕ,
      StochasticCRNLLN.l1Norm (StochasticCRNLLN.scaled N z - odePath s e i r τ) < K + M + 1 →
        ∀ c, (z c : ℝ) / N ≤ K + 2 * M + 1 := by
    intro τ hτ z hzδ c
    have h1 := abs_le_l1Norm (StochasticCRNLLN.scaled N z - odePath s e i r τ) c
    have h3 := le_abs_self ((StochasticCRNLLN.scaled N z - odePath s e i r τ) c)
    have h4 := le_abs_self (odePath s e i r τ c)
    have h2 := hxM τ hτ c
    have e1 : (StochasticCRNLLN.scaled N z - odePath s e i r τ) c =
        (z c : ℝ) / N - odePath s e i r τ c := rfl
    rw [e1] at h1 h3
    linarith
  have hbound : ∀ c, ∀ τ ∈ Icc 0 T, ∀ z : Compartment → ℕ,
      StochasticCRNLLN.l1Norm (StochasticCRNLLN.scaled N z - odePath s e i r τ) < K + M + 1 →
        (chainCRN β σ γ μ hκ N).propensity c z / N ≤ rateBound β σ γ μ (K + 2 * M + 1) := by
    intro c τ hτ z hzδ
    rw [propensity_chainCRN, mul_div_cancel_left₀ _ hNr.ne']
    exact scaledRate_le hβ hσ hγ hμ (by positivity) (by positivity) (hz τ hτ z hzδ .S)
      (hz τ hτ z hzδ .E) (hz τ hτ z hzδ .I) (hz τ hτ z hzδ .R) c
  have hrate : ∀ c, ∀ τ ∈ Icc 0 T, ∀ z : Compartment → ℕ,
      StochasticCRNLLN.l1Norm (StochasticCRNLLN.scaled N z - odePath s e i r τ) < K + M + 1 →
        |(chainCRN β σ γ μ hκ N).propensity c z / N -
          network.rate (rateConst β σ γ μ) (odePath s e i r τ) c| ≤
          0 + (β * (K + 3 * M + 1) + σ + γ + μ) *
            StochasticCRNLLN.l1Norm (StochasticCRNLLN.scaled N z - odePath s e i r τ) := by
    intro c τ hτ z hzδ
    rw [propensity_chainCRN, mul_div_cancel_left₀ _ hNr.ne', networkRate_eq, zero_add, l1Norm_eq]
    simp only [Pi.sub_apply, StochasticCRNLLN.scaled]
    exact (abs_scaledRate_sub_le hβ hσ hγ hμ (by positivity) (hz τ hτ z hzδ .S) (hxM τ hτ .I)
      c).trans (le_of_eq (by ring))
  have hβx : ∀ c, ContinuousOn (fun τ => network.rate (rateConst β σ γ μ) (odePath s e i r τ) c)
      (Icc 0 T) := fun c =>
    (StochasticCRNLLN.locallyLipschitz_rate network _ c).continuous.comp_continuousOn
      (hode'.continuousOn.mono fun τ hτ => hτ.1)
  have hmain := (h.toCRN hκ hmono).deviation_le_of_tube (T := T) (δ := K + M + 1)
    (L := β * (K + 3 * M + 1) + σ + γ + μ) (e := 0) (B := rateBound β σ γ μ (K + 2 * M + 1))
    (η := η) hN hode' hL0 le_rfl hB0 hβx hrate hbound hy ⟨hT, le_rfl⟩ htube t₀ ht₀
  rw [deviation_toPath ht₀.1, deviation_toPath le_rfl, chainCRN_network, stoichNorm_network,
    show (β * (K + 3 * M + 1) + σ + γ + μ) * 11 * t₀ =
      11 * (β * (K + 3 * M + 1) + σ + γ + μ) * t₀ by ring] at hmain
  calc _ ≤ _ := hmain
    _ = _ := by ring

end IsChainPath

/-! ### Kurtz's theorem for SEIR with vital dynamics -/

section Kurtz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {β σ γ μ : ℝ} {Y : ℕ → Channel → ℝ≥0 → Ω → ℕ} {S E I R : ℕ → Ω → ℝ → ℕ}
  {s e i r : ℝ → ℝ}

/-- **Kurtz's law of large numbers for the stochastic SEIR epidemic with vital dynamics**
(Kurtz 1970, Thm 3.1; Ethier–Kurtz 1986, ch. 11, Thm 2.1). For each scale `N` let
`(S N, E N, I N, R N)` be the chain driven by unit-rate Poisson processes `Y N c`, one per
channel, i.e. almost every sample path solves the random time-change equations of `IsChainPath`.
Let `(s, e, i, r)` solve the SEIR system with vital dynamics at scale `1`,
`s' = μ - β s i - μ s`, `e' = β s i - (μ + σ) e`, `i' = σ e - (μ + γ) i`, `r' = γ i - μ r`.
If the scaled initial state converges to `(s 0, e 0, i 0, r 0)` in probability, then the scaled
chain converges to `(s, e, i, r)` in probability, uniformly on every time interval `[0, T]`:

  `P(∃ t ∈ [0, T], |S/N - s| + |E/N - e| + |I/N - i| + |R/N - r| ≥ ε) → 0`  as `N → ∞`.

No positivity or normalisation of the initial point is needed. The event is not assumed
measurable; `P` is applied as an outer measure. Derived from the mass-action theorem
`StochasticCRNLLN.tendsto_measure_deviation_massAction` through `IsChainPath.toCRN`,
`hasDerivAt_odePath` and `deviation_toPath`. -/
theorem tendsto_measure_deviation (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hY : ∀ N c, IsPoissonProcess (Y N c) 1 P)
    (hchain : ∀ N, ∀ᵐ ω ∂P, IsChainPath β σ γ μ N (fun c u => Y N c u ω) (S N ω) (E N ω)
      (I N ω) (R N ω))
    (hode : SEIRVital.IsSolution β σ γ μ 1 s e i r)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N =>
      P {ω | δ ≤ deviation N (S N ω) (E N ω) (I N ω) (R N ω) s e i r 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => P {ω | ∃ t ∈ Icc 0 T,
      ε ≤ deviation N (S N ω) (E N ω) (I N ω) (R N ω) s e i r t}) atTop (𝓝 0) := by
  have hκ := rateConst_nonneg hβ hσ hγ hμ
  have hchain' : ∀ N, ∀ᵐ ω ∂P, StochasticCRNLLN.IsChainPath
      (StochasticCRNLLN.massAction network (rateConst β σ γ μ) hκ N) (fun c u => Y N c u ω)
      (toPath (S N ω) (E N ω) (I N ω) (R N ω)) := fun N => by
    filter_upwards [hchain N, (hY N .birth).ae_monotone] with ω hω hm
    exact hω.toCRN hκ hm
  have hinit' : ∀ δ, 0 < δ → Tendsto (fun N => P {ω | δ ≤ StochasticCRNLLN.deviation N
      (toPath (S N ω) (E N ω) (I N ω) (R N ω)) (odePath s e i r) 0}) atTop (𝓝 0) :=
    fun δ hδ => by simpa only [deviation_toPath le_rfl] using hinit δ hδ
  refine (StochasticCRNLLN.tendsto_measure_deviation_massAction network hκ hY hchain'
    (hasDerivAt_odePath hode) hinit' T hε).congr fun N => ?_
  congr 1
  ext ω
  simp only [mem_ofPred_eq]
  exact exists_congr fun t => and_congr_right fun ht => by rw [deviation_toPath ht.1]

/-- **Kurtz's theorem for SEIR with vital dynamics, supremum form.** Under the hypotheses of
`tendsto_measure_deviation`, the supremum over `[0, T]` of the deviation between the scaled chain
and the ODE solution is at least `ε` with probability tending to `0`. The supremum is taken in
`ℝ≥0∞`, so it exists for every path and need not be attained; the event is not assumed
measurable. -/
theorem tendsto_measure_iSup_deviation (hβ : 0 ≤ β) (hσ : 0 ≤ σ) (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (hY : ∀ N c, IsPoissonProcess (Y N c) 1 P)
    (hchain : ∀ N, ∀ᵐ ω ∂P, IsChainPath β σ γ μ N (fun c u => Y N c u ω) (S N ω) (E N ω)
      (I N ω) (R N ω))
    (hode : SEIRVital.IsSolution β σ γ μ 1 s e i r)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N =>
      P {ω | δ ≤ deviation N (S N ω) (E N ω) (I N ω) (R N ω) s e i r 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => P {ω | ENNReal.ofReal ε ≤
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal (deviation N (S N ω) (E N ω) (I N ω) (R N ω) s e i r t)})
      atTop (𝓝 0) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_deviation hβ hσ hγ hμ hY hchain hode hinit T hε2)
    (fun _ => bot_le) (fun N => measure_mono fun ω hω => ?_)
  simp only [mem_ofPred_eq] at hω ⊢
  have hlt : ENNReal.ofReal (ε / 2) <
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal (deviation N (S N ω) (E N ω) (I N ω) (R N ω) s e i r t) :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)) hω
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hlt
  obtain ⟨htT, hdev⟩ := lt_iSup_iff.1 ht
  exact ⟨t, htT, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε2.le).1 hdev).le⟩

omit [IsProbabilityMeasure P] in
/-- Deterministic initial counts: if almost surely `S N 0 = S₀ N`, …, `R N 0 = R₀ N` and
`S₀ N / N → s 0`, …, `R₀ N / N → r 0`, then the scaled initial state converges to
`(s 0, e 0, i 0, r 0)` in probability (the hypothesis `hinit` of `tendsto_measure_deviation`).
Derived from `StochasticCRNLLN.tendsto_measure_deviation_zero_of_initial`. -/
theorem tendsto_measure_deviation_zero_of_initial {S₀ E₀ I₀ R₀ : ℕ → ℕ}
    (hS₀ : ∀ N, ∀ᵐ ω ∂P, S N ω 0 = S₀ N) (hE₀ : ∀ N, ∀ᵐ ω ∂P, E N ω 0 = E₀ N)
    (hI₀ : ∀ N, ∀ᵐ ω ∂P, I N ω 0 = I₀ N) (hR₀ : ∀ N, ∀ᵐ ω ∂P, R N ω 0 = R₀ N)
    (hS : Tendsto (fun N => (S₀ N : ℝ) / N) atTop (𝓝 (s 0)))
    (hE : Tendsto (fun N => (E₀ N : ℝ) / N) atTop (𝓝 (e 0)))
    (hI : Tendsto (fun N => (I₀ N : ℝ) / N) atTop (𝓝 (i 0)))
    (hR : Tendsto (fun N => (R₀ N : ℝ) / N) atTop (𝓝 (r 0))) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N => P {ω | δ ≤ deviation N (S N ω) (E N ω) (I N ω) (R N ω) s e i r 0})
      atTop (𝓝 0) := by
  have hX₀ : ∀ N, ∀ᵐ ω ∂P, toPath (S N ω) (E N ω) (I N ω) (R N ω) 0 =
      vec4 (S₀ N) (E₀ N) (I₀ N) (R₀ N) := fun N => by
    filter_upwards [hS₀ N, hE₀ N, hI₀ N, hR₀ N] with ω h1 h2 h3 h4
    simp only [toPath, max_self, h1, h2, h3, h4]
  have hz₀ : Tendsto (fun N => StochasticCRNLLN.scaled N (vec4 (S₀ N) (E₀ N) (I₀ N) (R₀ N)))
      atTop (𝓝 (odePath s e i r 0)) := by
    refine tendsto_pi_nhds.2 fun c => ?_
    cases c
    · exact hS
    · exact hE
    · exact hI
    · exact hR
  simpa only [deviation_toPath le_rfl] using
    StochasticCRNLLN.tendsto_measure_deviation_zero_of_initial
      (X := fun N ω => toPath (S N ω) (E N ω) (I N ω) (R N ω)) (x := odePath s e i r)
      (z₀ := fun N => vec4 (S₀ N) (E₀ N) (I₀ N) (R₀ N)) hX₀ hz₀ hδ

/-- **The scaled chain settles near the endemic equilibrium.** Combine Kurtz's theorem with the
global stability of the endemic equilibrium (`SEIRVital.IsSolution.tendsto_endemic`): if
`σ > 0`, `γ ≥ 0`, `μ > 0`, `R₀ = β σ / ((μ + σ) (μ + γ)) > 1`, the ODE solution starts in the
open positive orthant and the scaled initial state converges to it in probability, then for
every `ε > 0` there is `t₀` such that at each fixed time `t ≥ t₀`,

  `P(|S(t)/N - S*| + |E(t)/N - E*| + |I(t)/N - I*| ≥ ε) → 0`  as `N → ∞`,

where `(S*, E*, I*)` is the endemic equilibrium at scale `1`. The limit is `N → ∞` at fixed `t`;
nothing is claimed uniformly in `t`. -/
theorem eventually_tendsto_measure_endemic (hσ : 0 < σ) (hγ : 0 ≤ γ) (hμ : 0 < μ)
    (hR : 1 < SEIRVital.R0 β σ γ μ) (hY : ∀ N c, IsPoissonProcess (Y N c) 1 P)
    (hchain : ∀ N, ∀ᵐ ω ∂P, IsChainPath β σ γ μ N (fun c u => Y N c u ω) (S N ω) (E N ω)
      (I N ω) (R N ω))
    (hode : SEIRVital.IsSolution β σ γ μ 1 s e i r) (hs0 : 0 < s 0) (he0 : 0 < e 0)
    (hi0 : 0 < i 0)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N =>
      P {ω | δ ≤ deviation N (S N ω) (E N ω) (I N ω) (R N ω) s e i r 0}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t₀ : ℝ, ∀ t, t₀ ≤ t → Tendsto (fun N => P {ω | ε ≤
      |(S N ω t : ℝ) / N - SEIRVital.endemicS β σ γ μ 1| +
      |(E N ω t : ℝ) / N - SEIRVital.endemicE β σ γ μ 1| +
      |(I N ω t : ℝ) / N - SEIRVital.endemicI β σ γ μ 1|}) atTop (𝓝 0) := by
  have hβ : 0 ≤ β := (SEIRVital.beta_pos hσ hγ hμ hR).le
  have hlim := hode.tendsto_endemic hσ hγ hμ one_pos hR hs0 he0 hi0
  have hcont : Continuous fun p : ℝ × ℝ × ℝ =>
      |p.1 - SEIRVital.endemicS β σ γ μ 1| + |p.2.1 - SEIRVital.endemicE β σ γ μ 1| +
        |p.2.2 - SEIRVital.endemicI β σ γ μ 1| := by
    fun_prop
  have hd := (hcont.tendsto _).comp hlim
  simp only [sub_self, abs_zero, add_zero] at hd
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨t₁, ht₁⟩ := eventually_atTop.1 (hd.eventually (gt_mem_nhds hε2))
  refine ⟨max t₁ 0, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
  have hclose := ht₁ t ((le_max_left _ _).trans ht)
  simp only [Function.comp_apply] at hclose
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_deviation hβ hσ.le hγ hμ.le hY hchain hode hinit t hε2)
    (fun _ => bot_le) (fun N => measure_mono fun ω hω => ⟨t, ⟨ht0, le_rfl⟩, ?_⟩)
  simp only [mem_ofPred_eq] at hω
  unfold deviation
  have h1 := abs_sub_le ((S N ω t : ℝ) / N) (s t) (SEIRVital.endemicS β σ γ μ 1)
  have h2 := abs_sub_le ((E N ω t : ℝ) / N) (e t) (SEIRVital.endemicE β σ γ μ 1)
  have h3 := abs_sub_le ((I N ω t : ℝ) / N) (i t) (SEIRVital.endemicI β σ γ μ 1)
  linarith [abs_nonneg ((R N ω t : ℝ) / N - r t)]

end Kurtz

end MathlibExt.Biology.Epidemiology.StochasticSEIRVital
