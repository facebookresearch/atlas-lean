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

/-- **Regular conditional distribution (measure-valued family).** Let $P$ be a measure on a
measurable space $(\Omega, \mathcal{F})$, let $S$ be a measurable space, $X : \Omega \to S$ a
map, $\mathcal{G}$ a σ-algebra on $\Omega$, and $\rho$ a family assigning a measure $\rho_\omega$
on $S$ to each $\omega \in \Omega$. Then $\rho$ is a regular conditional distribution of $X$
given $\mathcal{G}$ under $P$ if $\mathcal{G} \subseteq \mathcal{F}$; $X$ is
$\mathcal{F}$-measurable; for every measurable $A \subseteq S$ the map
$\omega \mapsto \rho_\omega(A)$ is $\mathcal{G}$-measurable; $\rho_\omega(S) \le 1$ for every
$\omega$; for every measurable $A \subseteq S$ the real number $\rho_\omega(A)$ agrees, for
$P$-almost every $\omega$, with the conditional expectation
$P[\mathbf{1}_{X^{-1}(A)} \mid \mathcal{G}](\omega)$; and $\rho_\omega$ is a probability measure
for $P$-almost every $\omega$.

Because each $\rho_\omega$ is a measure, countable additivity holds at every sample point,
including null ones; this is stricter than the raw set-function definition of Lecture 26, whose
set functions need to form probability measures only almost everywhere. -/
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

/-- **Regular conditional distribution (kernel form).** Let $\mu$ be a measure on $\alpha$ and let
$X : \alpha \to \beta$ and $Y : \alpha \to \Omega$ be maps. A kernel $\kappa$ from $\beta$ to
$\Omega$ is a regular conditional distribution of $Y$ given $X$ under $\mu$ if $X$ and $Y$ are
measurable, $\kappa$ is a Markov kernel, and for every measurable set $s \subseteq \Omega$ the
real-valued function $a \mapsto \kappa(X(a))(s)$ is $\mu$-almost everywhere equal to the
conditional expectation $\mu[\mathbf{1}_{Y^{-1}(s)} \mid \sigma(X)]$, where $\sigma(X)$ is the
σ-algebra on $\alpha$ generated by $X$. -/
structure IsRegularConditionalDistribution
    (κ : Kernel β Ω) (Y : α → Ω) (X : α → β) (μ : Measure α) : Prop where
  measurable_conditioning : @Measurable α β mα mβ X
  measurable_target : @Measurable α Ω mα ‹MeasurableSpace Ω› Y
  isMarkovKernel : IsMarkovKernel κ
  ae_eq_condExp : ∀ {s : Set Ω}, MeasurableSet s →
    (fun a => (κ (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | mβ.comap X⟧

/-- **The conditional distribution kernel is a regular conditional distribution.** Let $\Omega$
be a nonempty standard Borel space, $\mu$ a finite measure on $\alpha$, and $X : \alpha \to \beta$,
$Y : \alpha \to \Omega$ measurable maps. Then the conditional distribution of $Y$ given $X$ under
$\mu$, the kernel from $\beta$ to $\Omega$ obtained by disintegrating the joint law of $(X, Y)$
under $\mu$, is a regular conditional distribution of $Y$ given $X$ under $\mu$. -/
theorem condDistrib_isRegularConditionalDistribution
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    IsRegularConditionalDistribution (condDistrib Y X μ) Y X μ where
  measurable_conditioning := hX
  measurable_target := hY
  isMarkovKernel := inferInstance
  ae_eq_condExp hs := condDistrib_ae_eq_condExp hX hY hs

/-- **Existence of regular conditional distributions (kernel form).** Let $\Omega$ be a nonempty
standard Borel space, $\mu$ a finite measure on $\alpha$, and $X : \alpha \to \beta$,
$Y : \alpha \to \Omega$ measurable maps. Then there exists a kernel $\kappa$ from $\beta$ to
$\Omega$ that is a regular conditional distribution of $Y$ given $X$ under $\mu$; in particular
$\kappa$ is a Markov kernel. -/
theorem exists_regularConditionalDistribution
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ κ : Kernel β Ω, IsRegularConditionalDistribution κ Y X μ :=
  ⟨condDistrib Y X μ, condDistrib_isRegularConditionalDistribution hX hY⟩

/-- **Existence of measure-valued regular conditional distributions given a sub-σ-algebra.** Let
$\Omega$ be a nonempty standard Borel space, $\mu$ a finite measure on a measurable space
$(\alpha, \mathcal{F})$, $\mathcal{G} \subseteq \mathcal{F}$ a sub-σ-algebra, and
$Y : \alpha \to \Omega$ an $\mathcal{F}$-measurable map. Then some family of measures on $\Omega$
indexed by $\alpha$ is a measure-valued regular conditional distribution of $Y$ given
$\mathcal{G}$ under $\mu$.

The witness is the conditional distribution of $Y$ given the identity map from
$(\alpha, \mathcal{F})$ to $(\alpha, \mathcal{G})$. -/
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

/-- **Existence of measure-valued regular conditional distributions given a random variable.**
Let $\Omega$ be a nonempty standard Borel space, $\mu$ a finite measure on $\alpha$, and
$X : \alpha \to \beta$, $Y : \alpha \to \Omega$ measurable maps. Then some family of measures on
$\Omega$ indexed by $\alpha$ is a measure-valued regular conditional distribution of $Y$ given
the σ-algebra $\sigma(X)$ on $\alpha$ generated by $X$, under $\mu$. -/
theorem exists_regularConditionalDistribution_family
    [StandardBorelSpace Ω] [Nonempty Ω] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → Ω}
    (hX : Measurable X) (hY : Measurable Y) :
    ∃ rcd : α → Measure Ω,
      RegularConditionalDistribution rcd Y (mβ.comap X) μ :=
  exists_regularConditionalDistribution_family_of_le hX.comap_le hY

end ProbabilityTheory
