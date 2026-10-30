/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.Prokhorov
public import MathlibExt.Probability.StochasticOrder.StochasticDomination

/-!
# Monotone limits of probability measures on configuration space

On `ConfigSpace E = E → Bool` (`E` countable) the cylinder events are clopen, so weak convergence
implies convergence of the probabilities of cylinder events (portmanteau), and a probability
measure is determined by its values on clopen sets. Combined with stochastic domination this
gives the monotone construction of infinite-volume limits: a chain `μ₀ ≼ μ₁ ≼ ⋯` has increasing
probabilities of increasing clopen events, these converge, and the limits define a weak limit.

## Main results

* `StatMech.isClopen_cylinderEvent`: cylinder events are clopen.
* `StatMech.WeakConvergesTo.tendsto_real_of_isClopen`: weak convergence gives convergence of the
  probabilities of clopen events.
* `StatMech.WeakConvergesTo.le_real_of_monotone_isIncreasing`,
  `StatMech.WeakConvergesTo.ge_real_of_antitone_isIncreasing`: the weak limit of a monotone chain
  bounds every term on increasing clopen events.
* `StatMech.dominated_weakLimit_of_forall_dominated`,
  `StatMech.weakLimit_dominated_of_forall_dominated`: domination passes to weak limits on
  increasing clopen events.
* `StatMech.ProbabilityMeasure.ext_of_forall_isClopen`: probability measures agreeing on clopen
  sets are equal.
* `StatMech.tendsto_weakly_of_forall_isClopen_tendsto`: if the probabilities of all clopen events
  converge, the sequence converges weakly.
-/

@[expose] public section

open MeasureTheory TopologicalSpace Filter Topology MeasurableSpace
open scoped ENNReal NNReal Topology

namespace StatMech

variable {E : Type*} [Countable E]

omit [Countable E] in
/-- A cylinder event of `ConfigSpace E`, determined by finitely many coordinates, is clopen. -/
theorem isClopen_cylinderEvent (s : Finset E) (S : Set (∀ _i : s, Bool)) :
    IsClopen (cylinder (α := fun _ : E => Bool) s S) := by
  apply IsClopen.preimage
  · exact isClopen_discrete S
  · exact continuous_pi (fun i => continuous_apply i.1)

/-- Under weak convergence on `ConfigSpace E`, the probability of every clopen event converges
(portmanteau theorem). -/
theorem WeakConvergesTo.tendsto_real_of_isClopen
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν) {A : Set (ConfigSpace E)} (hA : IsClopen A) :
    Tendsto (fun n => (μ n : Measure (ConfigSpace E)).real A) atTop
      (𝓝 ((ν : Measure (ConfigSpace E)).real A)) := by
  have hnn : Tendsto (fun n => ((μ n) A : NNReal)) atTop (𝓝 ((ν : ProbabilityMeasure _) A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto h hA
  have hcoe := (NNReal.continuous_coe.tendsto _).comp hnn
  simp only [Function.comp_def, ← MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn] at hcoe
  exact hcoe

omit [Countable E] in
/-- Along a chain `μ₀ ≼ μ₁ ≼ ⋯`, the probability of an increasing event is monotone. -/
theorem monotone_real_of_chain
    {μ : ℕ → Measure (ConfigSpace E)}
    (hchain : ∀ n, μ n ≼ μ (n + 1))
    (hfinite : ∀ n, IsFiniteMeasure (μ n))
    {A : Set (ConfigSpace E)} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    Monotone (fun n => (μ n).real A) := by
  apply monotone_nat_of_le_succ
  intro n
  let _ := hfinite (n + 1)
  exact (hchain n).real A hAmeas hAinc

omit [Countable E] in
/-- Along a chain `⋯ ≼ μ₁ ≼ μ₀`, the probability of an increasing event is antitone. -/
theorem antitone_real_of_chain
    {μ : ℕ → Measure (ConfigSpace E)}
    (hchain : ∀ n, μ (n + 1) ≼ μ n)
    (hfinite : ∀ n, IsFiniteMeasure (μ n))
    {A : Set (ConfigSpace E)} (hAmeas : MeasurableSet A) (hAinc : IsIncreasing A) :
    Antitone (fun n => (μ n).real A) := by
  apply antitone_nat_of_succ_le
  intro n
  let _ := hfinite n
  exact (hchain n).real A hAmeas hAinc

/-- The weak limit of an increasing chain gives each increasing clopen event at least the
probability any term of the chain gives it. -/
theorem WeakConvergesTo.le_real_of_monotone_isIncreasing
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) (n : ℕ) :
    (μ n : Measure (ConfigSpace E)).real A ≤ (ν : Measure (ConfigSpace E)).real A :=
  (monotone_real_of_chain hchain (fun _ => inferInstance)
      (hAclopen.isOpen.measurableSet) hAinc).ge_of_tendsto
    (h.tendsto_real_of_isClopen hAclopen) n

/-- The weak limit of a decreasing chain gives each increasing clopen event at most the
probability any term of the chain gives it. -/
theorem WeakConvergesTo.ge_real_of_antitone_isIncreasing
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    (hchain : ∀ n, (μ (n + 1) : Measure (ConfigSpace E)) ≼ (μ n : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) (n : ℕ) :
    (ν : Measure (ConfigSpace E)).real A ≤ (μ n : Measure (ConfigSpace E)).real A :=
  (antitone_real_of_chain hchain (fun _ => inferInstance)
      (hAclopen.isOpen.measurableSet) hAinc).le_of_tendsto
    (h.tendsto_real_of_isClopen hAclopen) n

/-- A lower bound on the probabilities of a clopen event along a weakly convergent sequence passes
to the limit. -/
theorem le_real_of_weakLimit
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (_hAinc : IsIncreasing A)
    (hbound : ∀ n, ρ.real A ≤ (μ n : Measure (ConfigSpace E)).real A) :
    ρ.real A ≤ (ν : Measure (ConfigSpace E)).real A :=
  ge_of_tendsto (h.tendsto_real_of_isClopen hAclopen)
    (Filter.Eventually.of_forall hbound)

/-- An upper bound on the probabilities of a clopen event along a weakly convergent sequence passes
to the limit. -/
theorem real_le_of_weakLimit
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A)
    (hbound : ∀ n, (μ n : Measure (ConfigSpace E)).real A ≤ ρ.real A) :
    (ν : Measure (ConfigSpace E)).real A ≤ ρ.real A :=
  le_of_tendsto (h.tendsto_real_of_isClopen hAclopen)
    (Filter.Eventually.of_forall hbound)

/-- If `ρ ≼ μₙ` for all `n` and `μₙ → ν` weakly, then `ρ(A) ≤ ν(A)` for every increasing clopen
event `A`. -/
theorem dominated_weakLimit_of_forall_dominated
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)}
    (h : WeakConvergesTo μ ν)
    (hdom : ∀ n, ρ ≼ (μ n : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    ρ.real A ≤ (ν : Measure (ConfigSpace E)).real A :=
  le_real_of_weakLimit h hAclopen hAinc
    (fun n => (hdom n).real A (hAclopen.isOpen.measurableSet) hAinc)

/-- If `μₙ ≼ ρ` for all `n` and `μₙ → ν` weakly, then `ν(A) ≤ ρ(A)` for every increasing clopen
event `A`. -/
theorem weakLimit_dominated_of_forall_dominated
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {ν : ProbabilityMeasure (ConfigSpace E)}
    {ρ : Measure (ConfigSpace E)} [IsFiniteMeasure ρ]
    (h : WeakConvergesTo μ ν)
    (hdom : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ ρ)
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    (ν : Measure (ConfigSpace E)).real A ≤ ρ.real A :=
  real_le_of_weakLimit h hAclopen
    (fun n => (hdom n).real A (hAclopen.isOpen.measurableSet) hAinc)

omit [Countable E] in
/-- Two probability measures on `ConfigSpace E` that agree on clopen sets are equal: the clopen
cylinder events form a generating π-system. -/
theorem ProbabilityMeasure.ext_of_forall_isClopen
    {μ ν : ProbabilityMeasure (ConfigSpace E)}
    (h : ∀ A : Set (ConfigSpace E), IsClopen A → μ A = ν A) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_generate_finite (measurableCylinders (fun _ : E => Bool))
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
  · intro s hs
    rw [mem_measurableCylinders] at hs
    obtain ⟨t, S, _hS, rfl⟩ := hs
    have hclopen := isClopen_cylinderEvent t S
    have hμν := h _ hclopen
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
        ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hμν]
  · rw [measure_univ, measure_univ]

/-- If the probabilities of clopen events converge to `L`, every subsequential weak limit `ξ`
satisfies `ξ(A) = L(A)` on clopen `A`. -/
theorem isClopen_apply_eq_of_subseq_tendsto
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {L : Set (ConfigSpace E) → NNReal}
    (hconv : ∀ A : Set (ConfigSpace E), IsClopen A → Tendsto (fun n => (μ n) A) atTop (𝓝 (L A)))
    {ξ : ProbabilityMeasure (ConfigSpace E)} {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (htends : Tendsto (μ ∘ ψ) atTop (𝓝 ξ))
    {A : Set (ConfigSpace E)} (hA : IsClopen A) :
    (ξ A : NNReal) = L A := by
  have hport : Tendsto (fun n => (μ ∘ ψ) n A) atTop (𝓝 (ξ A)) :=
    ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto htends hA
  have hsub : Tendsto (fun n => (μ ∘ ψ) n A) atTop (𝓝 (L A)) :=
    (hconv A hA).comp hψ.tendsto_atTop
  exact tendsto_nhds_unique hport hsub

/-- If the probability of every clopen event converges along a sequence of probability measures on
`ConfigSpace E`, the sequence converges weakly: all subsequential limits (which exist by
Prokhorov) agree on clopen sets, hence coincide. -/
theorem tendsto_weakly_of_forall_isClopen_tendsto
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)} {L : Set (ConfigSpace E) → NNReal}
    (hconv : ∀ A : Set (ConfigSpace E), IsClopen A → Tendsto (fun n => (μ n) A) atTop (𝓝 (L A))) :
    ∃ ν : ProbabilityMeasure (ConfigSpace E), WeakConvergesTo μ ν := by
  obtain ⟨ν, φ, hφ, hν⟩ := CompactSpace.tendsto_subseq μ
  refine ⟨ν, ?_⟩
  rw [WeakConvergesTo]
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ξ hξ
  obtain ⟨ψ, hψ, htends_ξ⟩ := hξ.tendsto_subseq
  apply ProbabilityMeasure.ext_of_forall_isClopen
  intro A hA
  have hξA : (ξ A : NNReal) = L A :=
    isClopen_apply_eq_of_subseq_tendsto hconv hψ htends_ξ hA
  have hνA : (ν A : NNReal) = L A :=
    isClopen_apply_eq_of_subseq_tendsto hconv hφ hν hA
  rw [hξA, hνA]

/-- Along a chain `μ₀ ≼ μ₁ ≼ ⋯`, the probability of an increasing clopen event converges to its
supremum. -/
theorem tendsto_NNReal_of_monotone_isIncreasing
    {μ : ℕ → ProbabilityMeasure (ConfigSpace E)}
    (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    Tendsto (fun n => (μ n) A) atTop (𝓝 (⨆ n, (μ n) A)) := by
  have hAmeas := hAclopen.isOpen.measurableSet
  have hmono : Monotone (fun n => (μ n) A) := by
    apply monotone_nat_of_le_succ
    intro n
    have hreal : (μ n : Measure (ConfigSpace E)).real A
        ≤ (μ (n + 1) : Measure (ConfigSpace E)).real A :=
      (hchain n).real A hAmeas hAinc
    rw [MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn,
      MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn] at hreal
    exact_mod_cast hreal
  have hbdd : BddAbove (Set.range (fun n => (μ n) A)) :=
    ⟨1, by rintro x ⟨n, rfl⟩; exact MeasureTheory.ProbabilityMeasure.apply_le_one _ _⟩
  exact tendsto_atTop_ciSup hmono hbdd

end StatMech
