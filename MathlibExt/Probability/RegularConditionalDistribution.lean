/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Kernel.CondDistrib

/-!
# Measure-valued regular conditional distribution refinements

This module provides a strengthened, measure-valued refinement of the
Lecture 26 raw set-function definition in
`v1/Atlas/TheoryOfProbability/targets.yaml`. The archived developments are
`RegularConditionalDistribution.lean` and `ExistRegularCondProb.lean` in
`v1/Atlas/TheoryOfProbability/code/`.

The source permits `[0,1]`-valued set functions that form probability
measures only almost everywhere. Here `rcd ω : Measure S` imposes empty-set
mass zero and countable additivity at every sample point, including null
states. Thus not every source family has a pointwise representation in
this API. The retained family also records conditioning measurability,
ambient target measurability, and pointwise `[0,1]` bounds; probability
normalization remains an almost-everywhere condition.

The general-G measure-valued witness implies the source existence theorem:
evaluate each witness measure on measurable sets and take `toReal`. Its
evaluations have the source's range, measurability, per-set a.e. conditional
expectation, and a.e. probability-measure clauses. This does not identify
all raw source families with measure-valued families. Finite measures are
allowed, extending the source's probability-space setting.

## Scope and Mathlib reuse

* `RegularConditionalDistribution`: strengthened measure-valued family.
* `IsRegularConditionalDistribution`: measurable conditioning/target maps
  with a Markov kernel for `σ(X)`.
* `condDistrib_isRegularConditionalDistribution`: canonical kernel packaging.
* `exists_regularConditionalDistribution`: kernel-form existence.
* `exists_regularConditionalDistribution_family_of_le`: measure-valued
  family existence for any `𝒢 ≤ mα`.
* `exists_regularConditionalDistribution_family`: the `σ(X)` corollary.

The general-G witness uses `id : (α, mα) → (α, 𝒢)` as the conditioning map
in Mathlib's `condDistrib`. The outcome space is nonempty and standard
Borel; the measure is finite. No countability assumption on `𝒢` is added.
Conditional-expectation equality is per measurable target set and almost
everywhere, so its exceptional set may depend on that target set. The a.e.
probability condition uses a single full-measure set of sample points.
No pointwise kernel identity at null conditioning values is claimed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [MeasurableSpace Ω] {μ : Measure α}

/-- **Strengthened measure-valued refinement of a regular conditional
distribution.** Each sample-point value is a measure, enforcing countable
additivity and empty-set mass zero even at null states. The target is
ambient-measurable, `𝒢` is a sub-sigma-algebra, and every measurable-set
evaluation is `𝒢`-measurable with values in `[0,1]` pointwise. Conditional
expectation agrees a.e. for each measurable set, and probability
normalization is required a.e. This is stricter than the Lecture 26 raw
set-function definition at exceptional sample points. -/
structure RegularConditionalDistribution
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {S : Type*} [MeasurableSpace S]
    (rcd : Ω → Measure S) (X : Ω → S) (𝒢 : MeasurableSpace Ω)
    (P : @Measure Ω mΩ) : Prop where
  conditioning_le : 𝒢 ≤ mΩ
  measurable_target : @Measurable Ω S mΩ ‹MeasurableSpace S› X
  measurable_eval : ∀ {A : Set S}, MeasurableSet A →
    Measurable[𝒢] fun ω => rcd ω A
  mass_le_one : ∀ ω, rcd ω Set.univ ≤ 1
  ae_eq_condexp : ∀ {A : Set S}, MeasurableSet A →
    (fun ω => (rcd ω A).toReal) =ᵐ[P] P⟦X ⁻¹' A | 𝒢⟧
  ae_isProbabilityMeasure : ∀ᵐ ω ∂P, IsProbabilityMeasure (rcd ω)

/-- **Regular conditional distribution (kernel form).** A Markov kernel
`κ : Kernel β Ω` is a regular conditional distribution of measurable `Y : α → Ω` given
measurable `X : α → β` under `μ` if for every measurable `s ⊆ Ω`, the function
`a ↦ κ (X a) s` is a version of the conditional probability
`μ(Y ∈ s | σ(X))`. -/
structure IsRegularConditionalDistribution
    (κ : Kernel β Ω) (Y : α → Ω) (X : α → β) (μ : Measure α) : Prop where
  measurable_conditioning : @Measurable α β mα mβ X
  measurable_target : @Measurable α Ω mα ‹MeasurableSpace Ω› Y
  isMarkovKernel : IsMarkovKernel κ
  ae_eq_condExp : ∀ {s : Set Ω}, MeasurableSet s →
    (fun a => (κ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧

/-- When `Ω` is a standard Borel space, Mathlib's `condDistrib Y X μ` is a
regular conditional distribution of `Y` given `X` under `μ`. This packages
`condDistrib_ae_eq_condExp` together with the Markov-kernel property. -/
theorem condDistrib_isRegularConditionalDistribution
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    IsRegularConditionalDistribution (condDistrib Y X μ) Y X μ where
  measurable_conditioning := hX
  measurable_target := hY
  isMarkovKernel := inferInstance
  ae_eq_condExp hs := condDistrib_ae_eq_condExp hX hY hs

/-- **Existence of regular conditional distributions (kernel form).** When
`Ω` is a standard Borel space, for any finite measure `μ` and measurable
maps `X : α → β`, `Y : α → Ω`, there exists a Markov kernel
`κ : Kernel β Ω` that is a regular conditional distribution of `Y` given
`X`. -/
theorem exists_regularConditionalDistribution
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ κ : Kernel β Ω, IsRegularConditionalDistribution κ Y X μ :=
  ⟨condDistrib Y X μ, condDistrib_isRegularConditionalDistribution hX hY⟩

/-- **Measure-valued refinement existence for an arbitrary sub-sigma-algebra.** A measurable
map into a nonempty standard Borel space has a regular conditional
distribution given any `𝒢 ≤ mα`, under a finite measure. The witness is
Mathlib's `condDistrib` with conditioning map `id` into the space carrying `𝒢`. -/
theorem exists_regularConditionalDistribution_family_of_le
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {𝒢 : MeasurableSpace α} {Y : α → Ω}
    (h𝒢 : 𝒢 ≤ mα) (hY : @Measurable α Ω mα ‹MeasurableSpace Ω› Y) :
    ∃ rcd : α → Measure Ω, RegularConditionalDistribution rcd Y 𝒢 μ := by
  let κ : @Kernel α Ω 𝒢 ‹MeasurableSpace Ω› :=
    @condDistrib α α Ω ‹MeasurableSpace Ω› ‹StandardBorelSpace Ω› ‹Nonempty Ω›
      mα 𝒢 Y id μ ‹IsFiniteMeasure μ›
  have hid : @Measurable α α mα 𝒢 id := by
    intro s hs
    exact h𝒢 s hs
  refine ⟨fun a => κ a, ?_⟩
  exact {
    conditioning_le := h𝒢
    measurable_target := hY
    measurable_eval := fun hA => Kernel.measurable_coe κ hA
    mass_le_one := fun _ => prob_le_one
    ae_eq_condexp := fun hA => by
      simpa only [κ, measureReal_def, MeasurableSpace.comap_id, id_eq] using
        (condDistrib_ae_eq_condExp (mβ := 𝒢) (μ := μ) hid hY hA)
    ae_isProbabilityMeasure := Filter.Eventually.of_forall fun _ => inferInstance }

/-- **Measure-valued refinement existence for `σ(X)`.** This retains the original public
statement and follows from existence for arbitrary sub-sigma-algebras. -/
theorem exists_regularConditionalDistribution_family
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ rcd : α → Measure Ω,
      RegularConditionalDistribution rcd Y (mβ.comap X) μ :=
  exists_regularConditionalDistribution_family_of_le hX.comap_le hY

end ProbabilityTheory
