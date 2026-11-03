/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Discrete pure differential privacy

A mechanism is a function `Database → PMF Output`, so its output distribution
has total mass one. `IsDP` bounds point masses by a factor of `exp ε`, with
`ε ≥ 0`. `IsDPEvent` gives the equivalent bound for every event (set of
outputs), using the discrete outer measure associated with the PMF.

Deterministic postprocessing uses `PMF.map` and preserves privacy for arbitrary
functions, including many-to-one maps. `ReplaceOne` is bounded adjacency:
fixed-size databases disagree in at most one row, including at size zero.

This is an analytic model of discrete distributions, not an executable sampler.
Continuous distributions, a Laplace mechanism, and a SampCert bridge are not
implemented here.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

/-- Bounded adjacency: the set of changed row indices has at most one element.
In particular, equal databases are adjacent even when `n = 0`. -/
def ReplaceOne {n : ℕ} {X : Type*} (d d' : Fin n → X) : Prop :=
  {i | d i ≠ d' i}.Subsingleton

/-- A database is adjacent to itself, including an empty database. -/
@[refl]
theorem ReplaceOne.refl {n : ℕ} {X : Type*} (d : Fin n → X) :
    ReplaceOne d d := by
  intro i hi
  exact (hi rfl).elim

/-- Bounded replace-one adjacency is symmetric. -/
@[symm]
theorem ReplaceOne.symm {n : ℕ} {X : Type*} {d d' : Fin n → X}
    (h : ReplaceOne d d') : ReplaceOne d' d := by
  intro i hi j hj
  exact h (Ne.symm hi) (Ne.symm hj)

/-- Pure `ε`-DP for normalized discrete distributions. The inequality is for
ordered adjacent pairs; symmetric adjacency therefore gives both directions. -/
def IsDP {Database Output : Type*} (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ d d', adj d d' → ∀ o,
    M d o ≤ ENNReal.ofReal (Real.exp ε) * M d' o

/-- Event-level pure `ε`-DP. All subsets are events in the discrete PMF model;
no ambient measurable-space structure is required. -/
def IsDPEvent {Database Output : Type*} (M : Database → PMF Output)
    (adj : Database → Database → Prop) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ d d', adj d d' → ∀ s : Set Output,
    (M d).toOuterMeasure s ≤
      ENNReal.ofReal (Real.exp ε) * (M d').toOuterMeasure s

/-- Pointwise and event-level pure DP are equivalent for PMFs. -/
theorem isDP_iff_isDPEvent {Database Output : Type*}
    {M : Database → PMF Output} {adj : Database → Database → Prop}
    {ε : ℝ} : IsDP M adj ε ↔ IsDPEvent M adj ε := by
  constructor
  · rintro ⟨hε, h⟩
    refine ⟨hε, fun d d' hadj s => ?_⟩
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
      ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro o
    by_cases ho : o ∈ s
    · simpa only [Set.indicator_of_mem ho] using h d d' hadj o
    · simp only [Set.indicator_of_notMem ho, mul_zero, le_refl]
  · rintro ⟨hε, h⟩
    refine ⟨hε, fun d d' hadj o => ?_⟩
    simpa only [PMF.toOuterMeasure_apply_singleton] using h d d' hadj {o}

/-- Deterministic postprocessing, with normalization supplied by `PMF.map`. -/
noncomputable def postProcess {Database Output Output' : Type*}
    (g : Output → Output') (M : Database → PMF Output) :
    Database → PMF Output' :=
  fun d => (M d).map g

/-- Every deterministic function of an `ε`-DP mechanism is `ε`-DP.
No injectivity or finiteness assumption is needed on the function. -/
theorem isDP_postProcess {Database Output Output' : Type*}
    {M : Database → PMF Output} {adj : Database → Database → Prop}
    {ε : ℝ} (h : IsDP M adj ε) (g : Output → Output') :
    IsDP (postProcess g M) adj ε := by
  apply isDP_iff_isDPEvent.mpr
  refine ⟨h.1, fun d d' hadj s => ?_⟩
  simpa only [postProcess, PMF.toOuterMeasure_map_apply] using
    (isDP_iff_isDPEvent.mp h).2 d d' hadj (g ⁻¹' s)

/-- A distribution independent of the database is private with zero budget. -/
theorem isDP_const {Database Output : Type*} (p : PMF Output)
    (adj : Database → Database → Prop) : IsDP (fun _ => p) adj 0 := by
  simp [IsDP]

end CSLibExt.Privacy.DifferentialPrivacy
