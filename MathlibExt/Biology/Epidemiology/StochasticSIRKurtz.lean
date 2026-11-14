/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.SIRExistence
public import MathlibExt.Probability.Process.PoissonProcess
public import MathlibExt.Probability.Distributions.PoissonKernel
import MathlibExt.Analysis.ODE.GronwallIntegral

/-!
# Kurtz's law of large numbers for the stochastic SIR epidemic

In a closed population of size `N`, the stochastic SIR epidemic is the continuous-time Markov
chain on counts `(S, I, R)` with `S + I + R = N` that jumps

* `(S, I, R) → (S - 1, I + 1, R)` (infection) at rate `β S I / N`, and
* `(S, I, R) → (S, I - 1, R + 1)` (recovery) at rate `γ I`.

Both rates have the density-dependent form `N · λ(S / N, I / N)`, so as `N → ∞` the scaled chain
`(S, I, R) / N` should follow the deterministic Kermack–McKendrick system
`s' = -β s i`, `i' = β s i - γ i`, `r' = γ i` (`SIR.IsSolution β γ 1`). This is the SIR instance
of Kurtz's theorem (Kurtz 1970, Thm 3.1; Ethier–Kurtz 1986, ch. 11, Thm 2.1).

## The chain

We use Kurtz's random time-change representation (Ethier–Kurtz 1986, ch. 6, §4): with
independent unit-rate Poisson processes `Y₁`, `Y₂`,

  `S(t) = S(0) - Y₁(∫₀ᵗ β S I / N)`,  `I(t) = I(0) + Y₁(∫₀ᵗ β S I / N) - Y₂(∫₀ᵗ γ I)`,
  `R(t) = R(0) + Y₂(∫₀ᵗ γ I)`.

`IsChainPath β γ N y₁ y₂ S I R` states these equations for one sample path, with `ℕ`-valued
counts (so nonnegativity is part of the state space) and measurable paths. The driving processes
are `ProbabilityTheory.IsPoissonProcess` of rate `1`.

## Main results

* `IsChainPath.total_eq`: conservation, `S + I + R = N` for `t ≥ 0`.
* `IsChainPath.deviation_le`: Kurtz's pathwise estimate. If the scaled clocks satisfy
  `|y(N a) / N - a| ≤ η` on the relevant ranges, then on `[0, T]` the `ℓ¹` distance between the
  scaled chain and the ODE solution is at most `(initial distance + 4 η) e^{2 (β + γ) t}`.
* `exists_measure_poissonClock_le`, `tendsto_measure_poissonClock`: the uniform law of large
  numbers for a unit Poisson clock, `P(sup_{a ≤ B} |Y(N a) / N - a| > η) ≤ C / N`, uniformly over
  unit Poisson processes.
* `tendsto_measure_deviation`: **Kurtz's theorem for SIR.** If the scaled initial state
  converges in probability, then for every `T` and `ε > 0`, the probability that the deviation
  reaches `ε` at some time of `[0, T]` tends to `0`:
  `P(∃ t ∈ [0, T], |S/N - s| + |I/N - i| + |R/N - r| ≥ ε) → 0`.
* `tendsto_measure_iSup_deviation`: the same for the supremum event,
  `P(sup_{t ∈ [0, T]} |S/N - s| + |I/N - i| + |R/N - r| ≥ ε) → 0`; the supremum need not be
  attained.
* `tendsto_measure_deviation_zero_of_initial`: the initial-condition hypothesis for
  deterministic initial counts with `S₀(N) / N → s(0)`, etc.
* `tendsto_integral_infected`: consequently `E[I(t) / N] → i(t)` (via the general
  `tendsto_integral_of_tendsto_measure`).

## Scope

* The theorems take the chain as given: a family of paths satisfying the time-change equations
  almost surely. That such paths exist (the pathwise jump-by-jump construction), and that they
  have the law of the jump chain built in
  `MathlibExt.Probability.Process.ContinuousTimeMarkovChain.Path`, are not proved here.
* Independence of `Y₁` and `Y₂` is not used: the law of large numbers holds for any coupling of
  the two clocks, so it is not assumed.
* Only the law of large numbers is proved, with an `O(1/N)` Chebyshev bound for the clock
  errors; the central limit (diffusion) correction is not treated.
* The events over `[0, T]` (a time with deviation at least `ε`, or the supremum at least `ε`)
  are not assumed measurable; their probabilities are outer measures.

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

namespace MathlibExt.Biology.Epidemiology.StochasticSIR

/-! ### The chain -/

/-- The internal clock of the infection channel at time `t`: `∫₀ᵗ β S(s) I(s) / N ds`, the
integrated infection rate (truncated at `0` so it can be fed to a counting process indexed by
`ℝ≥0`). -/
noncomputable def infectionClock (β : ℝ) (N : ℕ) (S I : ℝ → ℕ) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (∫ s in (0 : ℝ)..t, β * S s * I s / N)

/-- The internal clock of the recovery channel at time `t`: `∫₀ᵗ γ I(s) ds`. -/
noncomputable def recoveryClock (γ : ℝ) (I : ℝ → ℕ) (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (∫ s in (0 : ℝ)..t, γ * I s)

/-- **One sample path of the stochastic SIR chain** of population size `N` (Kurtz's random
time-change representation; Ethier–Kurtz 1986, ch. 6, (4.1) and ch. 11, (2.1)). Given the
paths `y₁`, `y₂` of the two driving unit-rate counting processes, the counts `S, I, R : ℝ → ℕ`
satisfy, for `t ≥ 0`,

  `S(t) = S(0) - y₁(∫₀ᵗ β S I / N)`,
  `I(t) = I(0) + y₁(∫₀ᵗ β S I / N) - y₂(∫₀ᵗ γ I)`,
  `R(t) = R(0) + y₂(∫₀ᵗ γ I)`,

with `S(0) + I(0) + R(0) = N`. When `y₁`, `y₂` are independent unit-rate Poisson processes,
this is the continuous-time Markov chain that jumps `(S, I, R) → (S - 1, I + 1, R)` at rate
`β S I / N` (infection) and `(S, I, R) → (S, I - 1, R + 1)` at rate `γ I` (recovery). The
counts are natural numbers, so they are nonnegative by construction. The paths are required to
be measurable (a càdlàg path is), so that the clocks are genuine Lebesgue integrals. -/
structure IsChainPath (β γ : ℝ) (N : ℕ) (y₁ y₂ : ℝ≥0 → ℕ) (S I R : ℝ → ℕ) : Prop where
  /-- The initial population has size `N`. -/
  total_zero : S 0 + I 0 + R 0 = N
  /-- The susceptible path is measurable. -/
  measurable_susceptible : Measurable S
  /-- The infective path is measurable. -/
  measurable_infected : Measurable I
  /-- The removed path is measurable. -/
  measurable_removed : Measurable R
  /-- Susceptibles leave at the jumps of the infection channel. -/
  susceptible_eq : ∀ t, 0 ≤ t → (S t : ℝ) = S 0 - y₁ (infectionClock β N S I t)
  /-- Infectives arrive at infection jumps and leave at recovery jumps. -/
  infected_eq : ∀ t, 0 ≤ t →
    (I t : ℝ) = I 0 + y₁ (infectionClock β N S I t) - y₂ (recoveryClock γ I t)
  /-- Removed individuals arrive at the jumps of the recovery channel. -/
  removed_eq : ∀ t, 0 ≤ t → (R t : ℝ) = R 0 + y₂ (recoveryClock γ I t)

/-- The `ℓ¹` distance at time `t` between the scaled chain `(S, I, R) / N` and a deterministic
path `(s, i, r)`. -/
noncomputable def deviation (N : ℕ) (S I R : ℝ → ℕ) (s i r : ℝ → ℝ) (t : ℝ) : ℝ :=
  |(S t : ℝ) / N - s t| + |(I t : ℝ) / N - i t| + |(R t : ℝ) / N - r t|

namespace IsChainPath

variable {β γ : ℝ} {N : ℕ} {y₁ y₂ : ℝ≥0 → ℕ} {S I R : ℝ → ℕ}

/-- **Conservation of the population.** Along a chain path, `S + I + R = N` at every `t ≥ 0`. -/
theorem total_eq (h : IsChainPath β γ N y₁ y₂ S I R) {t : ℝ} (ht : 0 ≤ t) :
    S t + I t + R t = N := by
  have h1 := h.susceptible_eq t ht
  have h2 := h.infected_eq t ht
  have h3 := h.removed_eq t ht
  have : ((S t + I t + R t : ℕ) : ℝ) = ((S 0 + I 0 + R 0 : ℕ) : ℝ) := by
    push_cast
    linarith
  rw [← h.total_zero]
  exact_mod_cast this

end IsChainPath

/-! ### The pathwise estimate -/

/-- A measurable function bounded on `[0, ∞)` is integrable on `[0, T]`. -/
private theorem integrableOn_Icc_of_bound {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, 0 ≤ x → |f x| ≤ C) (T : ℝ) : IntegrableOn f (Icc 0 T) :=
  IntegrableOn.of_bound measure_Icc_lt_top hf.aestronglyMeasurable C
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun x hx => by
      rw [Real.norm_eq_abs]
      exact hC x hx.1))

private theorem uIcc_subset_Ici {t : ℝ} (ht : 0 ≤ t) : uIcc 0 t ⊆ Ici 0 := fun x hx => by
  rw [uIcc_of_le ht] at hx
  exact hx.1

namespace IsChainPath

variable {β γ : ℝ} {N : ℕ} {y₁ y₂ : ℝ≥0 → ℕ} {S I R : ℝ → ℕ}

/-- The scaled counts of a chain path lie in `[0, 1]` at every `t ≥ 0`. -/
theorem scaled_mem_Icc (h : IsChainPath β γ N y₁ y₂ S I R) (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    (S t : ℝ) / N ∈ Icc 0 1 ∧ (I t : ℝ) / N ∈ Icc 0 1 ∧ (R t : ℝ) / N ∈ Icc 0 1 := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have htot : (S t : ℝ) + I t + R t = N := by exact_mod_cast h.total_eq ht
  have h1 : (0 : ℝ) ≤ S t := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ I t := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ R t := Nat.cast_nonneg _
  refine ⟨⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩, ⟨by positivity, ?_⟩⟩ <;>
    rw [div_le_one hNr] <;> linarith

/-- **Kurtz's pathwise estimate.** Let `(S, I, R)` be a chain path of population size `N ≥ 1`
and `(s, i, r)` a solution of the SIR system `s' = -β s i`, `i' = β s i - γ i`, `r' = γ i`
started in the simplex. If on the clock ranges `[0, β T]` and `[0, γ T]` the scaled driving
counts stay within `η` of the identity, `|y(N a) / N - a| ≤ η`, then on `[0, T]`

  `|S/N - s| + |I/N - i| + |R/N - r| ≤ (initial distance + 4 η) e^{2 (β + γ) t}`.

Proof: subtracting the integral form of the ODE from the time-change equations leaves the
initial error, the clock errors (at most `η` each), and the integral of the drift difference,
which is `2 (β + γ)`-Lipschitz in `ℓ¹` on the simplex; Gronwall's inequality closes it. -/
theorem deviation_le (h : IsChainPath β γ N y₁ y₂ S I R) (hN : 0 < N) (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) {s i r : ℝ → ℝ} (hode : SIR.IsSolution β γ 1 s i r) (hs0 : 0 ≤ s 0)
    (hi0 : 0 ≤ i 0) (hr0 : 0 ≤ r 0) (hsum : s 0 + i 0 + r 0 = 1) {T η : ℝ}
    (hy₁ : ∀ a ∈ Icc 0 (β * T), |(y₁ (Real.toNNReal (N * a)) : ℝ) / N - a| ≤ η)
    (hy₂ : ∀ a ∈ Icc 0 (γ * T), |(y₂ (Real.toNNReal (N * a)) : ℝ) / N - a| ≤ η) :
    ∀ t ∈ Icc 0 T, deviation N S I R s i r t ≤
      (deviation N S I R s i r 0 + 4 * η) * exp (2 * (β + γ) * t) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hbd := fun {x : ℝ} (hx : 0 ≤ x) => h.scaled_mem_Icc hN hx
  -- measurability of the scaled paths
  have hSm : Measurable fun x => (S x : ℝ) / N :=
    (measurable_from_nat.comp h.measurable_susceptible).div_const _
  have hIm : Measurable fun x => (I x : ℝ) / N :=
    (measurable_from_nat.comp h.measurable_infected).div_const _
  have hRm : Measurable fun x => (R x : ℝ) / N :=
    (measurable_from_nat.comp h.measurable_removed).div_const _
  -- the deterministic solution
  have hsc : ContinuousOn s (Ici 0) := fun x hx =>
    (hode.hasDerivAt_susceptible x hx).continuousAt.continuousWithinAt
  have hic : ContinuousOn i (Ici 0) := fun x hx =>
    (hode.hasDerivAt_infected x hx).continuousAt.continuousWithinAt
  have hrc : ContinuousOn r (Ici 0) := fun x hx =>
    (hode.hasDerivAt_removed x hx).continuousAt.continuousWithinAt
  have hode_bd : ∀ x, 0 ≤ x → (0 ≤ s x ∧ s x ≤ 1) ∧ (0 ≤ i x ∧ i x ≤ 1) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hode.nonneg hγ hs0 hi0 hr0 hx
    have := hode.total_eq hx
    exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩
  have hsi_ii : ∀ t, 0 ≤ t → IntervalIntegrable (fun x => β * s x * i x) volume 0 t :=
    fun t ht => ContinuousOn.intervalIntegrable (by
      have := hsc.mono (uIcc_subset_Ici ht)
      have := hic.mono (uIcc_subset_Ici ht)
      fun_prop)
  have hi_ii : ∀ t, 0 ≤ t → IntervalIntegrable (fun x => γ * i x) volume 0 t :=
    fun t ht => ContinuousOn.intervalIntegrable (by
      have := hic.mono (uIcc_subset_Ici ht)
      fun_prop)
  have hs_int : ∀ t, 0 ≤ t → s t = s 0 - ∫ x in (0 : ℝ)..t, β * s x * i x := by
    intro t ht
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (f := s)
      (f' := fun x => -(β * s x * i x / 1))
      (fun x hx => hode.hasDerivAt_susceptible x (uIcc_subset_Ici ht hx))
      (by simp only [div_one]; exact (hsi_ii t ht).neg)
    simp only [div_one, intervalIntegral.integral_neg] at this
    linarith
  have hi_int : ∀ t, 0 ≤ t →
      i t = i 0 + ((∫ x in (0 : ℝ)..t, β * s x * i x) - ∫ x in (0 : ℝ)..t, γ * i x) := by
    intro t ht
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (f := i)
      (f' := fun x => β * s x * i x / 1 - γ * i x)
      (fun x hx => hode.hasDerivAt_infected x (uIcc_subset_Ici ht hx))
      (by simp only [div_one]; exact (hsi_ii t ht).sub (hi_ii t ht))
    simp only [div_one] at this
    rw [intervalIntegral.integral_sub (hsi_ii t ht) (hi_ii t ht)] at this
    linarith
  have hr_int : ∀ t, 0 ≤ t → r t = r 0 + ∫ x in (0 : ℝ)..t, γ * i x := by
    intro t ht
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) (f := r)
      (f' := fun x => γ * i x)
      (fun x hx => hode.hasDerivAt_removed x (uIcc_subset_Ici ht hx)) (hi_ii t ht)
    linarith
  -- integrability of the deviation
  have hu_int : IntegrableOn (deviation N S I R s i r) (Icc 0 T) := by
    have hS' := integrableOn_Icc_of_bound hSm (C := 1) (fun x hx => by
      rw [abs_of_nonneg (hbd hx).1.1]; exact (hbd hx).1.2) T
    have hI' := integrableOn_Icc_of_bound hIm (C := 1) (fun x hx => by
      rw [abs_of_nonneg (hbd hx).2.1.1]; exact (hbd hx).2.1.2) T
    have hR' := integrableOn_Icc_of_bound hRm (C := 1) (fun x hx => by
      rw [abs_of_nonneg (hbd hx).2.2.1]; exact (hbd hx).2.2.2) T
    have hsI := (hsc.mono fun x (hx : x ∈ Icc 0 T) => hx.1).integrableOn_compact
      (μ := volume) isCompact_Icc
    have hiI := (hic.mono fun x (hx : x ∈ Icc 0 T) => hx.1).integrableOn_compact
      (μ := volume) isCompact_Icc
    have hrI := (hrc.mono fun x (hx : x ∈ Icc 0 T) => hx.1).integrableOn_compact
      (μ := volume) isCompact_Icc
    exact (((hS'.sub hsI).abs.add (hI'.sub hiI).abs).add (hR'.sub hrI).abs)
  have hu0 : ∀ t ∈ Icc 0 T, 0 ≤ deviation N S I R s i r t := fun t _ => by
    unfold deviation
    positivity
  refine MathlibExt.Analysis.ODE.le_mul_exp_of_le_add_integral (by positivity) hu_int hu0 ?_
  intro t ht
  have ht0 := ht.1
  have hu_ii : IntervalIntegrable (deviation N S I R s i r) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).2
      (hu_int.mono_set (Icc_subset_Icc_right ht.2))
  -- the two clocks, in scaled form
  have hA₁ii : IntervalIntegrable (fun x => β * ((S x : ℝ) / N) * ((I x : ℝ) / N)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).2
    ((integrableOn_Icc_of_bound (f := fun x => β * ((S x : ℝ) / N) * ((I x : ℝ) / N))
      ((hSm.const_mul β).mul hIm) (C := β) (fun x hx => by
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := hbd hx
      rw [abs_of_nonneg (by positivity)]
      calc β * ((S x : ℝ) / N) * ((I x : ℝ) / N) ≤ β * 1 * 1 := by gcongr
        _ = β := by ring) t))
  have hA₂ii : IntervalIntegrable (fun x => γ * ((I x : ℝ) / N)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).2
    ((integrableOn_Icc_of_bound (f := fun x => γ * ((I x : ℝ) / N))
      (hIm.const_mul γ) (C := γ) (fun x hx => by
      obtain ⟨-, ⟨h3, h4⟩, -⟩ := hbd hx
      rw [abs_of_nonneg (by positivity)]
      calc γ * ((I x : ℝ) / N) ≤ γ * 1 := by gcongr
        _ = γ := by ring) t))
  have hc₁ : infectionClock β N S I t =
      Real.toNNReal (N * ∫ x in (0 : ℝ)..t, β * ((S x : ℝ) / N) * ((I x : ℝ) / N)) := by
    unfold infectionClock
    rw [← intervalIntegral.integral_const_mul]
    congr 2
    funext x
    field_simp
  have hc₂ : recoveryClock γ I t =
      Real.toNNReal (N * ∫ x in (0 : ℝ)..t, γ * ((I x : ℝ) / N)) := by
    unfold recoveryClock
    rw [← intervalIntegral.integral_const_mul]
    congr 2
    funext x
    field_simp
  have hA₁ : (∫ x in (0 : ℝ)..t, β * ((S x : ℝ) / N) * ((I x : ℝ) / N)) ∈ Icc 0 (β * T) := by
    refine ⟨intervalIntegral.integral_nonneg ht0 fun x hx => ?_, ?_⟩
    · obtain ⟨⟨h1, -⟩, ⟨h3, -⟩, -⟩ := hbd hx.1
      positivity
    · have := intervalIntegral.integral_mono_on ht0 hA₁ii
        (intervalIntegrable_const : IntervalIntegrable (fun _ => β) volume 0 t) fun x hx => by
          obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := hbd hx.1
          calc β * ((S x : ℝ) / N) * ((I x : ℝ) / N) ≤ β * 1 * 1 := by gcongr
            _ = β := by ring
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      nlinarith [ht.2]
  have hA₂ : (∫ x in (0 : ℝ)..t, γ * ((I x : ℝ) / N)) ∈ Icc 0 (γ * T) := by
    refine ⟨intervalIntegral.integral_nonneg ht0 fun x hx => ?_, ?_⟩
    · obtain ⟨-, ⟨h3, -⟩, -⟩ := hbd hx.1
      positivity
    · have := intervalIntegral.integral_mono_on ht0 hA₂ii
        (intervalIntegrable_const : IntervalIntegrable (fun _ => γ) volume 0 t) fun x hx => by
          obtain ⟨-, ⟨h3, h4⟩, -⟩ := hbd hx.1
          calc γ * ((I x : ℝ) / N) ≤ γ * 1 := by gcongr
            _ = γ := by ring
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
      nlinarith [ht.2]
  have hn₁ := hy₁ _ hA₁
  have hn₂ := hy₂ _ hA₂
  -- drift differences
  have hE₁ : |(∫ x in (0 : ℝ)..t, β * ((S x : ℝ) / N) * ((I x : ℝ) / N)) -
      ∫ x in (0 : ℝ)..t, β * s x * i x| ≤ β * ∫ x in (0 : ℝ)..t, deviation N S I R s i r x := by
    rw [← intervalIntegral.integral_sub hA₁ii (hsi_ii t ht0),
      ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht0 (ae_of_all _ fun x hx => ?_)
      (hu_ii.const_mul β)
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := hbd hx.1.le
    obtain ⟨-, ⟨h5, h6⟩⟩ := hode_bd x hx.1.le
    rw [Real.norm_eq_abs, show β * ((S x : ℝ) / N) * ((I x : ℝ) / N) - β * s x * i x =
      β * (((S x : ℝ) / N) * ((I x : ℝ) / N - i x) + i x * ((S x : ℝ) / N - s x)) by ring,
      abs_mul, abs_of_nonneg hβ]
    unfold deviation
    gcongr
    calc _ ≤ |((S x : ℝ) / N) * ((I x : ℝ) / N - i x)| + |i x * ((S x : ℝ) / N - s x)| :=
          abs_add_le _ _
      _ = ((S x : ℝ) / N) * |(I x : ℝ) / N - i x| + i x * |(S x : ℝ) / N - s x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h5]
      _ ≤ 1 * |(I x : ℝ) / N - i x| + 1 * |(S x : ℝ) / N - s x| := by gcongr
      _ ≤ _ := by linarith [abs_nonneg ((R x : ℝ) / N - r x)]
  have hE₂ : |(∫ x in (0 : ℝ)..t, γ * ((I x : ℝ) / N)) - ∫ x in (0 : ℝ)..t, γ * i x| ≤
      γ * ∫ x in (0 : ℝ)..t, deviation N S I R s i r x := by
    rw [← intervalIntegral.integral_sub hA₂ii (hi_ii t ht0),
      ← intervalIntegral.integral_const_mul, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le ht0 (ae_of_all _ fun x hx => ?_)
      (hu_ii.const_mul γ)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hγ]
    unfold deviation
    gcongr
    linarith [abs_nonneg ((R x : ℝ) / N - r x), abs_nonneg ((S x : ℝ) / N - s x)]
  -- assemble
  have hS := h.susceptible_eq t ht0
  have hI := h.infected_eq t ht0
  have hR := h.removed_eq t ht0
  have hs := hs_int t ht0
  have hi := hi_int t ht0
  have hr := hr_int t ht0
  rw [hc₁] at hS hI
  rw [hc₂] at hI hR
  generalize (∫ x in (0 : ℝ)..t, deviation N S I R s i r x) = U at hE₁ hE₂ ⊢
  generalize (∫ x in (0 : ℝ)..t, β * ((S x : ℝ) / N) * ((I x : ℝ) / N)) = A₁ at hS hI hn₁ hE₁
  generalize (∫ x in (0 : ℝ)..t, γ * ((I x : ℝ) / N)) = A₂ at hI hR hn₂ hE₂
  generalize (∫ x in (0 : ℝ)..t, β * s x * i x) = B₁ at hs hi hE₁
  generalize (∫ x in (0 : ℝ)..t, γ * i x) = B₂ at hi hr hE₂
  generalize ((y₁ (Real.toNNReal (N * A₁)) : ℕ) : ℝ) = Y₁ at hS hI hn₁
  generalize ((y₂ (Real.toNNReal (N * A₂)) : ℕ) : ℝ) = Y₂ at hI hR hn₂
  have hSt : (S t : ℝ) / N = (S 0 : ℝ) / N - Y₁ / N := by rw [hS]; ring
  have hIt : (I t : ℝ) / N = (I 0 : ℝ) / N + Y₁ / N - Y₂ / N := by rw [hI]; ring
  have hRt : (R t : ℝ) / N = (R 0 : ℝ) / N + Y₂ / N := by rw [hR]; ring
  unfold deviation
  rw [hSt, hIt, hRt, hs, hi, hr]
  rw [abs_le] at hn₁ hn₂ hE₁ hE₂
  have k1 := abs_sub_abs_le_abs_sub ((S 0 : ℝ) / N - Y₁ / N - (s 0 - B₁))
    ((S 0 : ℝ) / N - s 0)
  have k2 := abs_sub_abs_le_abs_sub ((I 0 : ℝ) / N + Y₁ / N - Y₂ / N - (i 0 + (B₁ - B₂)))
    ((I 0 : ℝ) / N - i 0)
  have k3 := abs_sub_abs_le_abs_sub ((R 0 : ℝ) / N + Y₂ / N - (r 0 + B₂)) ((R 0 : ℝ) / N - r 0)
  have e1 : |((S 0 : ℝ) / N - Y₁ / N - (s 0 - B₁)) - ((S 0 : ℝ) / N - s 0)| ≤ η + β * U := by
    rw [abs_le]; constructor <;> linarith
  have e2 : |((I 0 : ℝ) / N + Y₁ / N - Y₂ / N - (i 0 + (B₁ - B₂))) - ((I 0 : ℝ) / N - i 0)| ≤
      2 * η + β * U + γ * U := by
    rw [abs_le]; constructor <;> linarith
  have e3 : |((R 0 : ℝ) / N + Y₂ / N - (r 0 + B₂)) - ((R 0 : ℝ) / N - r 0)| ≤ η + γ * U := by
    rw [abs_le]; constructor <;> linarith
  linarith

end IsChainPath

/-! ### The law of large numbers for a unit Poisson clock -/

section PoissonClock

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Chebyshev at one time.** For a unit-rate Poisson process `Y`, `N ≥ 1`, `a ≥ 0` and
`c > 0`, the scaled increment `(Y(N a) - Y(0)) / N` is at distance `≥ c` from `a` with
probability at most `a / (N c²)`. -/
theorem measure_le_abs_div_sub_le {Y : ℝ≥0 → Ω → ℕ} (hY : IsPoissonProcess Y 1 μ) {N : ℕ}
    (hN : 0 < N) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    μ {ω | c ≤ |((Y (Real.toNNReal (N * a)) ω - Y 0 ω : ℕ) : ℝ) / N - a|} ≤
      ENNReal.ofReal (a / (N * c ^ 2)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set t : ℝ≥0 := Real.toNNReal (N * a) with ht_def
  have ht : (t : ℝ) = N * a := Real.coe_toNNReal _ (by positivity)
  have hlaw : HasLaw (fun ω => Y t ω - Y 0 ω) (poissonMeasure t) μ := by
    simpa using hY.hasLaw_sub (bot_le : (0 : ℝ≥0) ≤ t)
  have hcast : Measurable (fun x : ℕ => (x : ℝ)) := Measurable.of_discrete
  set Z : Ω → ℝ := fun ω => ((Y t ω - Y 0 ω : ℕ) : ℝ) with hZ
  have hmem : MemLp Z 2 μ :=
    hlaw.memLp_comp ((memLp_two_iff_integrable_sq hcast.aestronglyMeasurable).2
      (integrable_natCast_sq_poissonMeasure t))
  have hmean : μ[Z] = N * a := by
    have := hlaw.integral_comp (f := fun n : ℕ => (n : ℝ)) hcast.aestronglyMeasurable
    rw [integral_natCast_poissonMeasure, ht] at this
    exact this
  have hvar : variance Z μ = N * a := by
    have h := variance_map (μ := μ) (X := fun n : ℕ => (n : ℝ)) (Y := fun ω => Y t ω - Y 0 ω)
      (hlaw.map_eq ▸ hcast.aemeasurable) hlaw.aemeasurable
    rw [hlaw.map_eq, variance_natCast_poissonMeasure, ht] at h
    rw [h]
    rfl
  have hcheb := meas_ge_le_variance_div_sq hmem (c := N * c) (by positivity)
  rw [hvar, hmean] at hcheb
  refine le_trans (measure_mono fun ω hω => ?_) (hcheb.trans_eq ?_)
  · simp only [mem_ofPred_eq] at hω ⊢
    have : (Z ω) / N - a = (Z ω - N * a) / N := by field_simp
    rw [this, abs_div, abs_of_pos hNr, le_div_iff₀ hNr] at hω
    linarith
  · congr 1
    field_simp

/-- **Uniform law of large numbers for a unit Poisson clock**, with an explicit Chebyshev
rate: for every `B` and `η > 0` there is `C` such that, for every unit-rate Poisson process `Y`
and every `N ≥ 1`, `sup_{a ∈ [0, B]} |Y(N a) / N - a| > η` has probability at most `C / N`.

Proof: on the grid `a_k = k η / 4` (`k ≤ ⌈4 B / η⌉ + 1`) Chebyshev bounds each
`|Y(N a_k) / N - a_k| ≥ η / 2`; off the union of these events (and the null event where `Y` is
not a nondecreasing path from `0`) monotonicity of `Y` squeezes `Y(N a) / N` between two
consecutive grid values, which keeps it within `3 η / 4` of `a`. -/
theorem exists_measure_poissonClock_le (B : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, ∀ (Y : ℝ≥0 → Ω → ℕ), IsPoissonProcess Y 1 μ → ∀ N : ℕ, 0 < N →
      μ {ω | ∃ a ∈ Icc 0 B, η < |(Y (Real.toNNReal (N * a)) ω : ℝ) / N - a|} ≤
        ENNReal.ofReal (C / N) := by
  set h : ℝ := η / 4 with hh
  have hh0 : 0 < h := by positivity
  set M : ℕ := ⌈B / h⌉₊ with hM
  refine ⟨(M + 2 : ℕ) * ((M + 1 : ℕ) * h / (η / 2) ^ 2), fun Y hY N hN => ?_⟩
  have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
  set F : ℕ → Set Ω := fun k =>
    {ω | η / 2 ≤ |((Y (Real.toNNReal (N * (k * h))) ω - Y 0 ω : ℕ) : ℝ) / N - k * h|}
  set Null : Set Ω := {ω | ¬ (Y 0 ω = 0 ∧ Monotone fun u => Y u ω)}
  have hNull : μ Null = 0 := by
    have := hY.ae_zero.and hY.ae_monotone
    rwa [ae_iff] at this
  have hsub : {ω | ∃ a ∈ Icc 0 B, η < |(Y (Real.toNNReal (N * a)) ω : ℝ) / N - a|} ⊆
      Null ∪ ⋃ k ∈ Finset.range (M + 2), F k := by
    intro ω ⟨a, ha, hlt⟩
    by_contra hcon
    simp only [mem_union, mem_iUnion, Finset.mem_range, not_or, not_exists, Null,
      mem_ofPred_eq, not_not, F, not_le] at hcon
    obtain ⟨⟨hY0, hmono⟩, hgrid⟩ := hcon
    simp only [hY0, Nat.sub_zero] at hgrid
    set k : ℕ := ⌊a / h⌋₊
    have hk1 : (k : ℝ) * h ≤ a := by
      have := Nat.floor_le (div_nonneg ha.1 hh0.le)
      rwa [le_div_iff₀ hh0] at this
    have hk2 : a < ((k + 1 : ℕ) : ℝ) * h := by
      have := Nat.lt_floor_add_one (a / h)
      push_cast
      rwa [div_lt_iff₀ hh0] at this
    have hkM : k ≤ M := Nat.floor_le_ceil _ |>.trans (Nat.ceil_mono (by gcongr; exact ha.2))
    have hlo := hgrid k (by omega)
    have hhi := hgrid (k + 1) (by omega)
    have hm1 : (Y (Real.toNNReal (N * (k * h))) ω : ℝ) ≤ Y (Real.toNNReal (N * a)) ω := by
      exact_mod_cast hmono (Real.toNNReal_le_toNNReal (by gcongr))
    have hm2 : (Y (Real.toNNReal (N * a)) ω : ℝ) ≤
        Y (Real.toNNReal (N * (((k + 1 : ℕ) : ℝ) * h))) ω := by
      exact_mod_cast hmono (Real.toNNReal_le_toNNReal (by gcongr))
    have hd1 := div_le_div_of_nonneg_right hm1 hNr.le
    have hd2 := div_le_div_of_nonneg_right hm2 hNr.le
    rw [abs_lt] at hlo hhi
    rw [lt_abs] at hlt
    push_cast at hhi hk2 hd2
    rcases hlt with hlt | hlt <;> linarith
  calc μ {ω | ∃ a ∈ Icc 0 B, η < |(Y (Real.toNNReal (N * a)) ω : ℝ) / N - a|}
      ≤ μ (Null ∪ ⋃ k ∈ Finset.range (M + 2), F k) := measure_mono hsub
    _ ≤ μ Null + μ (⋃ k ∈ Finset.range (M + 2), F k) := measure_union_le _ _
    _ ≤ 0 + ∑ k ∈ Finset.range (M + 2), μ (F k) := by
        rw [hNull]; gcongr; exact measure_biUnion_finset_le _ _
    _ ≤ 0 + ∑ _k ∈ Finset.range (M + 2),
          ENNReal.ofReal ((M + 1 : ℕ) * h / (N * (η / 2) ^ 2)) := by
        gcongr with k hk
        refine (measure_le_abs_div_sub_le hY hN (by positivity) (by positivity)).trans ?_
        gcongr
        rw [Finset.mem_range] at hk
        exact_mod_cast (show k ≤ M + 1 by omega)
    _ = ENNReal.ofReal ((M + 2 : ℕ) * ((M + 1 : ℕ) * h / (η / 2) ^ 2) / N) := by
        rw [zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- **Uniform law of large numbers for unit Poisson clocks** (in probability, uniformly over
families): if each `Y N` is a unit-rate Poisson process, then for every `B` and `η > 0`,
`P(sup_{a ∈ [0, B]} |Y N (N a) / N - a| > η) → 0` as `N → ∞`. -/
theorem tendsto_measure_poissonClock {Y : ℕ → ℝ≥0 → Ω → ℕ}
    (hY : ∀ N, IsPoissonProcess (Y N) 1 μ) (B : ℝ) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun N : ℕ =>
      μ {ω | ∃ a ∈ Icc 0 B, η < |(Y N (Real.toNNReal (N * a)) ω : ℝ) / N - a|})
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_measure_poissonClock_le (μ := μ) B hη
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (C / N)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact hC (Y N) (hY N) N hN

end PoissonClock

/-! ### Kurtz's theorem for the SIR epidemic -/

section Kurtz

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {β γ : ℝ} {Y₁ Y₂ : ℕ → ℝ≥0 → Ω → ℕ} {S I R : ℕ → Ω → ℝ → ℕ} {s i r : ℝ → ℝ}

/-- **Kurtz's law of large numbers for the stochastic SIR epidemic** (Kurtz 1970, Thm 3.1;
Ethier–Kurtz 1986, ch. 11, Thm 2.1, SIR instance). For each population size `N` let
`(S N, I N, R N)` be the SIR chain driven by unit-rate Poisson processes `Y₁ N` (infection) and
`Y₂ N` (recovery), i.e. almost every sample path solves the random time-change equations of
`IsChainPath` with infection rate `β S I / N` and recovery rate `γ I`. Let `(s, i, r)` solve the
SIR system `s' = -β s i`, `i' = β s i - γ i`, `r' = γ i` from a point of the simplex. If the
scaled initial state converges to `(s 0, i 0, r 0)` in probability, then the scaled chain
converges to `(s, i, r)` in probability, uniformly on every time interval `[0, T]`: the
probability that the deviation reaches `ε` at some time of `[0, T]` tends to `0`,

  `P(∃ t ∈ [0, T], |S/N - s| + |I/N - i| + |R/N - r| ≥ ε) → 0`  as `N → ∞`.

This event contains the strict supremum event `sup_{t ∈ [0, T]} deviation > ε`. A supremum need
not be attained, so the non-strict supremum event `sup deviation ≥ ε` is the separate corollary
`tendsto_measure_iSup_deviation`. The event is not assumed measurable; `μ` is applied as an outer
measure. -/
theorem tendsto_measure_deviation (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hY₁ : ∀ N, IsPoissonProcess (Y₁ N) 1 μ) (hY₂ : ∀ N, IsPoissonProcess (Y₂ N) 1 μ)
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath β γ N (fun u => Y₁ N u ω) (fun u => Y₂ N u ω)
      (S N ω) (I N ω) (R N ω))
    (hode : SIR.IsSolution β γ 1 s i r) (hs0 : 0 ≤ s 0) (hi0 : 0 ≤ i 0) (hr0 : 0 ≤ r 0)
    (hsum : s 0 + i 0 + r 0 = 1)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N =>
      μ {ω | δ ≤ deviation N (S N ω) (I N ω) (R N ω) s i r 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ∃ t ∈ Icc 0 T,
      ε ≤ deviation N (S N ω) (I N ω) (R N ω) s i r t}) atTop (𝓝 0) := by
  set E : ℝ := exp (2 * (β + γ) * T) with hE
  have hE0 : 0 < E := exp_pos _
  set δ : ℝ := ε / (2 * E)
  set η : ℝ := ε / (8 * E)
  have hδ : 0 < δ := by positivity
  have hη : 0 < η := by positivity
  set Bad₀ : ℕ → Set Ω := fun N => {ω | ¬ IsChainPath β γ N (fun u => Y₁ N u ω)
    (fun u => Y₂ N u ω) (S N ω) (I N ω) (R N ω)}
  set Bad₁ : ℕ → Set Ω := fun N => {ω | δ ≤ deviation N (S N ω) (I N ω) (R N ω) s i r 0}
  set Bad₂ : ℕ → Set Ω := fun N =>
    {ω | ∃ a ∈ Icc 0 (β * T), η < |(Y₁ N (Real.toNNReal (N * a)) ω : ℝ) / N - a|}
  set Bad₃ : ℕ → Set Ω := fun N =>
    {ω | ∃ a ∈ Icc 0 (γ * T), η < |(Y₂ N (Real.toNNReal (N * a)) ω : ℝ) / N - a|}
  have hBad₀ : ∀ N, μ (Bad₀ N) = 0 := fun N => by
    have := hchain N
    rwa [ae_iff] at this
  have hsub : ∀ N, 0 < N → {ω | ∃ t ∈ Icc 0 T,
      ε ≤ deviation N (S N ω) (I N ω) (R N ω) s i r t} ⊆
      ((Bad₀ N ∪ Bad₁ N) ∪ Bad₂ N) ∪ Bad₃ N := by
    intro N hN ω ⟨t, ht, hle⟩
    by_contra hcon
    simp only [mem_union, not_or, Bad₀, Bad₁, Bad₂, Bad₃, mem_ofPred_eq, not_not, not_le,
      not_exists, not_and, not_lt] at hcon
    obtain ⟨⟨⟨hpath, hdev0⟩, hn₁⟩, hn₂⟩ := hcon
    have hbound := hpath.deviation_le hN hβ hγ hode hs0 hi0 hr0 hsum
      (T := T) (η := η) hn₁ hn₂ t ht
    have hexp : exp (2 * (β + γ) * t) ≤ E := exp_le_exp.2 (by nlinarith [ht.2])
    have hd0 : 0 ≤ deviation N (S N ω) (I N ω) (R N ω) s i r 0 := by
      unfold deviation; positivity
    have : (deviation N (S N ω) (I N ω) (R N ω) s i r 0 + 4 * η) * exp (2 * (β + γ) * t) <
        ε := by
      calc _ ≤ (deviation N (S N ω) (I N ω) (R N ω) s i r 0 + 4 * η) * E := by gcongr
        _ < (δ + 4 * η) * E := by gcongr
        _ = ε := by simp only [δ, η]; field_simp; ring
    linarith
  have hlim : Tendsto (fun N => ((μ (Bad₀ N) + μ (Bad₁ N)) + μ (Bad₂ N)) + μ (Bad₃ N))
      atTop (𝓝 (((0 + 0) + 0) + 0)) := by
    refine ((Tendsto.add ?_ (hinit δ hδ)).add ?_).add ?_
    · simp only [hBad₀]; exact tendsto_const_nhds
    · exact tendsto_measure_poissonClock hY₁ (β * T) hη
    · exact tendsto_measure_poissonClock hY₂ (γ * T) hη
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  refine (measure_mono (hsub N hN)).trans ((measure_union_le _ _).trans ?_)
  gcongr
  refine (measure_union_le _ _).trans ?_
  gcongr
  exact measure_union_le _ _

/-- **Kurtz's theorem for SIR, supremum form.** Under the hypotheses of
`tendsto_measure_deviation`, the supremum over `[0, T]` of the deviation between the scaled chain
and the ODE solution is at least `ε` with probability tending to `0`:

  `P(sup_{t ∈ [0, T]} |S/N - s| + |I/N - i| + |R/N - r| ≥ ε) → 0`  as `N → ∞`.

The supremum is taken in `ℝ≥0∞` (the deviation is nonnegative), so it exists for every path,
bounded or not, and need not be attained. The event lies inside the event of
`tendsto_measure_deviation` at threshold `ε / 2`; it is not assumed measurable, and `μ` is applied
as an outer measure. -/
theorem tendsto_measure_iSup_deviation (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hY₁ : ∀ N, IsPoissonProcess (Y₁ N) 1 μ) (hY₂ : ∀ N, IsPoissonProcess (Y₂ N) 1 μ)
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath β γ N (fun u => Y₁ N u ω) (fun u => Y₂ N u ω)
      (S N ω) (I N ω) (R N ω))
    (hode : SIR.IsSolution β γ 1 s i r) (hs0 : 0 ≤ s 0) (hi0 : 0 ≤ i 0) (hr0 : 0 ≤ r 0)
    (hsum : s 0 + i 0 + r 0 = 1)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N =>
      μ {ω | δ ≤ deviation N (S N ω) (I N ω) (R N ω) s i r 0}) atTop (𝓝 0))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N => μ {ω | ENNReal.ofReal ε ≤
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal (deviation N (S N ω) (I N ω) (R N ω) s i r t)})
      atTop (𝓝 0) := by
  have hε2 : 0 < ε / 2 := half_pos hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_deviation hβ hγ hY₁ hY₂ hchain hode hs0 hi0 hr0 hsum hinit T hε2)
    (fun _ => bot_le) (fun N => measure_mono fun ω hω => ?_)
  simp only [mem_ofPred_eq] at hω ⊢
  have hlt : ENNReal.ofReal (ε / 2) <
      ⨆ t ∈ Icc 0 T, ENNReal.ofReal (deviation N (S N ω) (I N ω) (R N ω) s i r t) :=
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)) hω
  obtain ⟨t, ht⟩ := lt_iSup_iff.1 hlt
  obtain ⟨htT, hdev⟩ := lt_iSup_iff.1 ht
  exact ⟨t, htT, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε2.le).1 hdev).le⟩

omit [IsProbabilityMeasure μ] in
/-- Deterministic initial counts: if almost surely `S N 0 = S₀ N`, `I N 0 = I₀ N`,
`R N 0 = R₀ N` and `S₀ N / N → s 0`, `I₀ N / N → i 0`, `R₀ N / N → r 0`, then the scaled initial
state converges to `(s 0, i 0, r 0)` in probability (the hypothesis `hinit` of
`tendsto_measure_deviation`). -/
theorem tendsto_measure_deviation_zero_of_initial {S₀ I₀ R₀ : ℕ → ℕ}
    (hS₀ : ∀ N, ∀ᵐ ω ∂μ, S N ω 0 = S₀ N) (hI₀ : ∀ N, ∀ᵐ ω ∂μ, I N ω 0 = I₀ N)
    (hR₀ : ∀ N, ∀ᵐ ω ∂μ, R N ω 0 = R₀ N)
    (hS : Tendsto (fun N => (S₀ N : ℝ) / N) atTop (𝓝 (s 0)))
    (hI : Tendsto (fun N => (I₀ N : ℝ) / N) atTop (𝓝 (i 0)))
    (hR : Tendsto (fun N => (R₀ N : ℝ) / N) atTop (𝓝 (r 0))) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N => μ {ω | δ ≤ deviation N (S N ω) (I N ω) (R N ω) s i r 0}) atTop (𝓝 0) := by
  have hdet : Tendsto (fun N => |(S₀ N : ℝ) / N - s 0| + |(I₀ N : ℝ) / N - i 0| +
      |(R₀ N : ℝ) / N - r 0|) atTop (𝓝 (|s 0 - s 0| + |i 0 - i 0| + |r 0 - r 0|)) :=
    (((hS.sub_const _).abs.add (hI.sub_const _).abs).add (hR.sub_const _).abs)
  simp only [sub_self, abs_zero, add_zero] at hdet
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hdet.eventually (gt_mem_nhds hδ)] with N hN
  symm
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (((hS₀ N).and (hI₀ N)).and (hR₀ N)))
  simp only [mem_ofPred_eq] at hω ⊢
  rintro ⟨⟨h1, h2⟩, h3⟩
  unfold deviation at hω
  rw [h1, h2, h3] at hω
  linarith

/-- **Convergence of means from convergence in probability.** If `X N` are measurable,
`|X N - x| ≤ 1` almost surely for large `N`, and `X N → x` in probability, then
`E[X N] → x`. -/
theorem tendsto_integral_of_tendsto_measure {X : ℕ → Ω → ℝ} {x : ℝ}
    (hX : ∀ N, Measurable (X N)) (hbd : ∀ᶠ N in atTop, ∀ᵐ ω ∂μ, |X N ω - x| ≤ 1)
    (hprob : ∀ ε, 0 < ε → Tendsto (fun N => μ {ω | ε ≤ |X N ω - x|}) atTop (𝓝 0)) :
    Tendsto (fun N => ∫ ω, X N ω ∂μ) atTop (𝓝 x) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have h2 : 0 < ε / 2 := by positivity
  have hev := (hprob (ε / 2) h2).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 h2))
  obtain ⟨N₀, hN₀⟩ := (hev.and hbd).exists_forall_of_atTop
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hμ, hb⟩ := hN₀ N hN
  set A : Set Ω := {ω | ε / 2 ≤ |X N ω - x|}
  have hXN := hX N
  have hA : MeasurableSet A := measurableSet_le measurable_const (by fun_prop)
  have hint : Integrable (X N) μ := by
    refine Integrable.of_bound (hX N).aestronglyMeasurable (|x| + 1) ?_
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs]
    calc |X N ω| = |(X N ω - x) + x| := by ring_nf
      _ ≤ |X N ω - x| + |x| := abs_add_le _ _
      _ ≤ |x| + 1 := by linarith
  have hpt : ∀ᵐ ω ∂μ, |X N ω - x| ≤ ε / 2 + A.indicator (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hb] with ω hω
    by_cases hω' : ω ∈ A
    · rw [indicator_of_mem hω']; linarith
    · rw [indicator_of_notMem hω']
      simp only [A, mem_ofPred_eq, not_le] at hω'
      linarith
  have hAreal : μ.real A < ε / 2 := by
    rw [measureReal_def]
    exact ENNReal.toReal_lt_of_lt_ofReal hμ
  have hmain : |(∫ ω, X N ω ∂μ) - x| ≤ ε / 2 + μ.real A := by
    have hsub : (∫ ω, X N ω ∂μ) - x = ∫ ω, (X N ω - x) ∂μ := by
      rw [integral_sub hint (integrable_const x), integral_const, probReal_univ, one_smul]
    rw [hsub]
    calc |∫ ω, (X N ω - x) ∂μ| ≤ ∫ ω, |X N ω - x| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (ε / 2 + A.indicator (fun _ => (1 : ℝ)) ω) ∂μ := by
          refine integral_mono_ae (hint.sub (integrable_const x)).abs ?_ hpt
          exact (integrable_const _).add ((integrable_const _).indicator hA)
      _ = ε / 2 + μ.real A := by
          rw [integral_add (integrable_const _) ((integrable_const _).indicator hA),
            integral_const, probReal_univ, one_smul,
            show (fun _ : Ω => (1 : ℝ)) = 1 from rfl, integral_indicator_one hA]
  rw [Real.dist_eq]
  linarith

/-- **The expected infected fraction converges** (Kurtz's theorem, consequence for means):
under the hypotheses of `tendsto_measure_deviation`, if the infective counts at time `t ≥ 0` are
measurable, then `E[I N (t) / N] → i(t)`. -/
theorem tendsto_integral_infected (hβ : 0 ≤ β) (hγ : 0 ≤ γ)
    (hY₁ : ∀ N, IsPoissonProcess (Y₁ N) 1 μ) (hY₂ : ∀ N, IsPoissonProcess (Y₂ N) 1 μ)
    (hchain : ∀ N, ∀ᵐ ω ∂μ, IsChainPath β γ N (fun u => Y₁ N u ω) (fun u => Y₂ N u ω)
      (S N ω) (I N ω) (R N ω))
    (hode : SIR.IsSolution β γ 1 s i r) (hs0 : 0 ≤ s 0) (hi0 : 0 ≤ i 0) (hr0 : 0 ≤ r 0)
    (hsum : s 0 + i 0 + r 0 = 1)
    (hinit : ∀ δ, 0 < δ → Tendsto (fun N =>
      μ {ω | δ ≤ deviation N (S N ω) (I N ω) (R N ω) s i r 0}) atTop (𝓝 0))
    {t : ℝ} (ht : 0 ≤ t) (hmeas : ∀ N, Measurable fun ω => I N ω t) :
    Tendsto (fun N => ∫ ω, (I N ω t : ℝ) / N ∂μ) atTop (𝓝 (i t)) := by
  refine tendsto_integral_of_tendsto_measure
    (fun N => (measurable_from_nat.comp (hmeas N)).div_const _) ?_ (fun ε hε => ?_)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    filter_upwards [hchain N] with ω hω
    obtain ⟨-, ⟨h1, h2⟩, -⟩ := hω.scaled_mem_Icc hN ht
    obtain ⟨-, h3, -⟩ := hode.nonneg hγ hs0 hi0 hr0 ht
    have := hode.total_eq ht
    obtain ⟨h4, -, h5⟩ := hode.nonneg hγ hs0 hi0 hr0 ht
    rw [abs_le]
    constructor <;> linarith
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_measure_deviation hβ hγ hY₁ hY₂ hchain hode hs0 hi0 hr0 hsum hinit t hε)
      (fun _ => bot_le) (fun N => measure_mono fun ω hω => ⟨t, ⟨ht, le_rfl⟩, ?_⟩)
    simp only [mem_ofPred_eq] at hω
    unfold deviation
    linarith [abs_nonneg ((S N ω t : ℝ) / N - s t), abs_nonneg ((R N ω t : ℝ) / N - r t)]

end Kurtz

end MathlibExt.Biology.Epidemiology.StochasticSIR
