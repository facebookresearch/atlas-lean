/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

section

open MeasureTheory Filter
open scoped ENNReal

namespace MathlibExt.Probability.LargeDeviationPrinciple

/-!
# Large deviation principles

A sequence of measures `μₙ` satisfies a large deviation principle (LDP)
with rate function `I` and speed `n` if the logarithmic asymptotics of
`μₙ(Γ)` are controlled by the infimum of `I` over `Γ`: roughly,
`μₙ(Γ) ≈ exp (-n inf_{x ∈ Γ} I(x))`. This file ports the definitions
from `v1/Atlas/TheoryOfProbability/code/LargeDeviations.lean`, with
finite-level goodness and topological/measurable-space compatibility
made explicit (see below), and proves measurable-set bounds, the Dirac-mass
example, and a good rate function on `ℝ`.

## Source

This formalizes the target "Definition (rate function and large
deviation principle)" (Lecture 13) of
`v1/Atlas/TheoryOfProbability/targets.yaml`. The v1 formalization is
`v1/Atlas/TheoryOfProbability/code/LargeDeviations.lean`, which states
only the definitions. Cramér's theorem (the LDP for empirical means,
stated in v1's `CramerTheorem.lean`) is not claimed here: its v1 proof
is left unproved, and proving it is a separate, much larger project.

## Correction to the v1 definition of a good rate function

In v1, a good rate function was required to have compact sub-level
sets `{x | I x ≤ a}` for *every* `a : ℝ≥0∞`, including `a = ⊤`.
But `{x | I x ≤ ⊤}` is the whole space, so on any non-compact space
(such as `ℝ`) no good rate function exists under that definition.
The standard definition only requires compactness for finite levels,
and that is what is formalized here:
`∀ a : ℝ, IsCompact {x | I x ≤ ENNReal.ofReal a}`. Negative real
levels are clipped to `0`, so they repeat the zero-level condition.

The LDP structure explicitly requires `OpensMeasurableSpace X`, ensuring
that the open and closed sets in its bounds are measurable. The converse
accepts bounds only for measurable sets; on a `BorelSpace X` these are
the textbook Borel sets. The forward bounds also hold for arbitrary sets
through monotonicity of measures, and are retained as stronger corollaries.

## Main results

* `IsRateFunction`: `I` is lower semicontinuous.
* `IsGoodRateFunction`: a rate function with compact finite sub-level
  sets (corrected definition, see above).
* `IsConvexRateFunction`: a rate function that is convex.
* `SatisfiesLDP`: open/closed LDP bounds with explicit measurable-open-set compatibility.
* `SatisfiesLDP.borel_bounds`: bounds for any set `Γ`, including measurable
  sets, with `interior Γ` and `closure Γ` in place of open and closed sets.
* `satisfiesLDP_of_borel_bounds`: measurable-set bounds imply the open/closed LDP.
* `satisfiesLDP_dirac`: the Dirac mass at `x₀` satisfies the LDP with
  the rate function that is `0` at `x₀` and `∞` elsewhere.
* `isGoodRateFunction_abs`: `x ↦ ENNReal.ofReal |x|` is a good rate
  function on `ℝ`, showing the corrected definition is non-vacuous
  there (under v1's definition, no good rate function on `ℝ` exists).
-/

/-- **Rate function.** Let $X$ be a topological space. A rate function on $X$ is a lower
semicontinuous function $I : X \to [0, \infty]$.

This is the basic regularity hypothesis used in the formulation of a large deviation principle. -/
structure IsRateFunction {X : Type*} [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I

/-- **Good rate function.** Let $X$ be a topological space. A function $I : X \to [0, \infty]$ is a
good rate function if it is a rate function and, for every real number $a \ge 0$, the sub-level
set $\{x \in X : I(x) \le a\}$ is compact.

Compactness is required only at finite levels: the sub-level set at level $\infty$ is all of $X$,
so requiring it as well would force $X$ itself to be compact. -/
structure IsGoodRateFunction {X : Type*} [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop
    extends IsRateFunction I where
  isCompact_levelSet : ∀ a : ℝ, IsCompact {x | I x ≤ ENNReal.ofReal a}

/-- **Convex rate function.** Let $X$ be a real vector space carrying a topology (no compatibility
between the topology and the linear structure is assumed). A function $I : X \to [0, \infty]$ is a
convex rate function if it is a rate function and $I(ax + by) \le a I(x) + b I(y)$ for all
$x, y \in X$ and all real numbers $a, b \ge 0$ with $a + b = 1$. -/
structure IsConvexRateFunction {X : Type*} [TopologicalSpace X] [AddCommMonoid X]
    [Module ℝ X] (I : X → ℝ≥0∞) : Prop extends IsRateFunction I where
  convex : ∀ ⦃x y : X⦄, ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    I (a • x + b • y) ≤ ENNReal.ofReal a * I x + ENNReal.ofReal b * I y

/-- **Large deviation principle for a sequence of measures.** Let $X$ be a topological space with
a $\sigma$-algebra containing every open set, let $(\mu_n)_{n \in \mathbb{N}}$ be a sequence of
measures on $X$, and let $I : X \to [0, \infty]$. The sequence $(\mu_n)$ satisfies the large
deviation principle with rate function $I$ and speed $n$ if $I$ is a rate function, every open
set $U \subseteq X$ satisfies
$$\liminf_{n \to \infty} \frac{1}{n} \log \mu_n(U) \ge -\inf_{x \in U} I(x),$$
and every closed set $F \subseteq X$ satisfies
$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(F) \le -\inf_{x \in F} I(x).$$
Here $\log 0 = -\infty$, an infimum over the empty set is $\infty$, and the limits are taken in
the extended reals. -/
structure SatisfiesLDP {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop where
  isRateFunction : IsRateFunction I
  lower_bound : ∀ U : Set X, IsOpen U →
    - (⨅ x ∈ U, (I x : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n U)) atTop
  upper_bound : ∀ F : Set X, IsClosed F →
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n F)) atTop ≤
      - (⨅ x ∈ F, (I x : EReal))

/-- **Good rate functions are rate functions.** Every good rate function on a topological space
is a rate function. -/
theorem IsGoodRateFunction.isRateFunction {X : Type*} [TopologicalSpace X]
    {I : X → ℝ≥0∞} (h : IsGoodRateFunction I) : IsRateFunction I :=
  h.toIsRateFunction

/-- **Convex rate functions are rate functions.** Every convex rate function on a real vector space
with a topology is a rate function. -/
theorem IsConvexRateFunction.isRateFunction {X : Type*} [TopologicalSpace X]
    [AddCommMonoid X] [Module ℝ X] {I : X → ℝ≥0∞} (h : IsConvexRateFunction I) :
    IsRateFunction I :=
  h.toIsRateFunction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- **Large deviation lower bound for arbitrary sets.** Let $X$ be a topological space with a
$\sigma$-algebra in which every open set is measurable, and let $(\mu_n)_{n \in \mathbb{N}}$ be
measures on $X$ satisfying the large deviation principle with rate function
$I : X \to [0, \infty]$. Then for every set $\Gamma \subseteq X$, not necessarily measurable (for
non-measurable $\Gamma$, $\mu_n(\Gamma)$ is its outer measure), with interior $\Gamma^\circ$,

$$-\inf_{x \in \Gamma^\circ} I(x) \le \liminf_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma),$$

computed in the extended reals with $\log 0 = -\infty$. -/
theorem SatisfiesLDP.borel_lower_bound [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (h : SatisfiesLDP μ I) (Γ : Set X) :
    - (⨅ x ∈ interior Γ, (I x : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop := by
  refine le_trans (h.lower_bound (interior Γ) isOpen_interior) ?_
  refine liminf_le_liminf ?_ ⟨⊥, Filter.Eventually.of_forall fun _ => bot_le⟩
    ⟨⊤, fun _ _ => le_top⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply mul_le_mul_of_nonneg_left _ _
  · exact ENNReal.log_monotone (measure_mono interior_subset)
  · exact EReal.inv_nonneg_of_nonneg (by exact_mod_cast Nat.zero_le n)

/-- **Large deviation upper bound for arbitrary sets.** Let $X$ be a topological space with a
$\sigma$-algebra in which every open set is measurable, and let $(\mu_n)_{n \in \mathbb{N}}$ be
measures on $X$ satisfying the large deviation principle with rate function
$I : X \to [0, \infty]$. Then for every set $\Gamma \subseteq X$, not necessarily measurable (for
non-measurable $\Gamma$, $\mu_n(\Gamma)$ is its outer measure), with closure $\overline{\Gamma}$,

$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \le -\inf_{x \in \overline{\Gamma}} I(x),$$

computed in the extended reals with $\log 0 = -\infty$. -/
theorem SatisfiesLDP.borel_upper_bound [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (h : SatisfiesLDP μ I) (Γ : Set X) :
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ≤
      - (⨅ x ∈ closure Γ, (I x : EReal)) := by
  refine le_trans ?_ (h.upper_bound (closure Γ) isClosed_closure)
  refine limsup_le_limsup ?_ ⟨⊥, fun _ _ => bot_le⟩
    ⟨⊤, Filter.Eventually.of_forall fun _ => le_top⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  apply mul_le_mul_of_nonneg_left _ _
  · exact ENNReal.log_monotone (measure_mono subset_closure)
  · exact EReal.inv_nonneg_of_nonneg (by exact_mod_cast Nat.zero_le n)

/-- **Large deviation bounds for arbitrary sets.** Let $X$ be a topological space with a
$\sigma$-algebra in which every open set is measurable, and let $(\mu_n)_{n \in \mathbb{N}}$ be
measures on $X$ satisfying the large deviation principle with rate function
$I : X \to [0, \infty]$. Then for every set $\Gamma \subseteq X$, not necessarily measurable (for
non-measurable $\Gamma$, $\mu_n(\Gamma)$ is its outer measure), with interior $\Gamma^\circ$ and
closure $\overline{\Gamma}$, both

$$-\inf_{x \in \Gamma^\circ} I(x) \le \liminf_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma)$$

and

$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \le -\inf_{x \in \overline{\Gamma}} I(x)$$

hold, computed in the extended reals with $\log 0 = -\infty$. In particular the bounds hold for
every Borel set $\Gamma$. -/
theorem SatisfiesLDP.borel_bounds [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (h : SatisfiesLDP μ I) (Γ : Set X) :
    - (⨅ x ∈ interior Γ, (I x : EReal)) ≤
        liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ∧
      limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ≤
        - (⨅ x ∈ closure Γ, (I x : EReal)) :=
  ⟨h.borel_lower_bound Γ, h.borel_upper_bound Γ⟩

/-- **Large deviation principle from bounds on measurable sets.** Let $X$ be a topological space
with a $\sigma$-algebra containing every open set, let $(\mu_n)_{n \in \mathbb{N}}$ be a sequence
of measures on $X$, and let $I$ be a rate function on $X$. Suppose that every measurable set
$\Gamma \subseteq X$, with interior $\Gamma^\circ$ and closure $\overline{\Gamma}$, satisfies
$$\liminf_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \ge -\inf_{x \in \Gamma^\circ} I(x)$$
and
$$\limsup_{n \to \infty} \frac{1}{n} \log \mu_n(\Gamma) \le -\inf_{x \in \overline{\Gamma}} I(x),$$
where $\log 0 = -\infty$, an infimum over the empty set is $\infty$, and the limits are taken in
the extended reals. Then $(\mu_n)$ satisfies the large deviation principle with rate function $I$.

Open and closed sets are measurable and equal to their interior and closure respectively, so the
hypothesis contains the open-set and closed-set bounds. On a Borel space this is the textbook
Borel-set converse. -/
theorem satisfiesLDP_of_borel_bounds [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (hRate : IsRateFunction I)
    (h : ∀ Γ : Set X, MeasurableSet Γ →
      - (⨅ x ∈ interior Γ, (I x : EReal)) ≤
          liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ∧
        limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ≤
          - (⨅ x ∈ closure Γ, (I x : EReal))) :
    SatisfiesLDP μ I := by
  refine ⟨hRate, fun U hU => ?_, fun F hF => ?_⟩
  · have hU' := (h U hU.measurableSet).1
    rwa [hU.interior_eq] at hU'
  · have hF' := (h F hF.measurableSet).2
    rwa [hF.closure_eq] at hF'

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- **Rate function of a Dirac mass.** For a point $x_0$ of a set $X$, the Dirac rate function
at $x_0$ is the function $X \to [0, \infty]$ that equals $0$ at $x_0$ and $\infty$ at every other
point. -/
noncomputable def diracRate (x₀ : X) : X → ℝ≥0∞ :=
  Set.indicator {x₀}ᶜ (fun _ => (⊤ : ℝ≥0∞))

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- **The Dirac rate function vanishes at its center.** For every point $x_0$ of a set $X$, the
Dirac rate function at $x_0$ takes the value $0$ at $x_0$. -/
lemma diracRate_apply_self (x₀ : X) : diracRate x₀ x₀ = 0 := by
  simp [diracRate]

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- **The Dirac rate function is infinite away from its center.** For points $x \ne x_0$ of a set
$X$, the Dirac rate function at $x_0$ takes the value $\infty$ at $x$. -/
lemma diracRate_apply_of_ne {x₀ x : X} (h : x ≠ x₀) : diracRate x₀ x = ⊤ := by
  simp [diracRate, h]

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- **Infimum of the Dirac rate function over a set containing the center.** For a point $x_0$ of
a set $X$ and a subset $s \subseteq X$ with $x_0 \in s$, the infimum over $x \in s$ of the Dirac
rate function at $x_0$, evaluated at $x$, is $0$. -/
lemma iInf_diracRate_of_mem {x₀ : X} {s : Set X} (h : x₀ ∈ s) :
    (⨅ x ∈ s, ((diracRate x₀ x : ℝ≥0∞) : EReal)) = 0 := by
  apply le_antisymm _ _
  · have hle := iInf₂_le (f := fun x (_ : x ∈ s) => ((diracRate x₀ x : ℝ≥0∞) : EReal)) x₀ h
    rwa [diracRate_apply_self, EReal.coe_ennreal_zero] at hle
  · apply le_iInf₂
    intro x _
    exact EReal.coe_ennreal_nonneg _

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- **Infimum of the Dirac rate function over a set avoiding the center.** For a point $x_0$ of a
set $X$ and a subset $s \subseteq X$ with $x_0 \notin s$, the infimum over $x \in s$ of the Dirac
rate function at $x_0$, evaluated at $x$, is $\infty$. -/
lemma iInf_diracRate_of_notMem {x₀ : X} {s : Set X} (h : x₀ ∉ s) :
    (⨅ x ∈ s, ((diracRate x₀ x : ℝ≥0∞) : EReal)) = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf₂
  intro x hx
  have hne : x ≠ x₀ := fun he => h (he ▸ hx)
  rw [diracRate_apply_of_ne hne, EReal.coe_ennreal_top]

omit [TopologicalSpace X] in
/-- **Log-scaled Dirac mass of a set containing the center.** Let $X$ be a measurable space, let
$\delta_{x_0}$ be the Dirac measure at a point $x_0 \in X$, and let $s \subseteq X$ be a set with
$x_0 \in s$. Then $\frac{1}{n} \log \delta_{x_0}(s) = 0$ in the extended reals for every natural
number $n$, the factor $1/n$ being read as $0$ when $n = 0$. -/
lemma dirac_ldp_term_eq_zero_of_mem {x₀ : X} {s : Set X} (h : x₀ ∈ s) (n : ℕ) :
    ((n : ℕ) : EReal)⁻¹ * ENNReal.log (Measure.dirac x₀ s) = 0 := by
  rw [Measure.dirac_apply_of_mem h, ENNReal.log_one, mul_zero]

omit [TopologicalSpace X] in
/-- **Log-scaled Dirac mass of a set avoiding the center.** Let $X$ be a measurable space in which
every singleton is measurable, let $\delta_{x_0}$ be the Dirac measure at a point $x_0 \in X$, and
let $s \subseteq X$ be a set with $x_0 \notin s$. Then for every natural number $n \ge 1$,
$\frac{1}{n} \log \delta_{x_0}(s) = -\infty$ in the extended reals, with $\log 0 = -\infty$. -/
lemma dirac_ldp_term_eq_bot_of_notMem [MeasurableSingletonClass X] {x₀ : X} {s : Set X}
    (h : x₀ ∉ s) {n : ℕ}
    (hn : 1 ≤ n) : ((n : ℕ) : EReal)⁻¹ * ENNReal.log (Measure.dirac x₀ s) = ⊥ := by
  have hdirac : Measure.dirac x₀ s = 0 := by
    rw [Measure.dirac_apply]
    exact Set.indicator_of_notMem h _
  rw [hdirac, ENNReal.log_zero]
  apply EReal.mul_bot_of_pos
  apply EReal.inv_pos_of_pos_ne_top _ (EReal.natCast_ne_top n)
  exact_mod_cast Nat.cast_pos.mpr (Nat.lt_of_lt_of_le zero_lt_one hn)

/-- **Large deviation principle for a Dirac mass.** Let $X$ be a $T_1$ topological space equipped
with its Borel $\sigma$-algebra, and let $x_0 \in X$. The constant sequence of measures
$\mu_n = \delta_{x_0}$ satisfies the large deviation principle with the Dirac rate function of
$x_0$, which is $0$ at $x_0$ and $\infty$ elsewhere.

Indeed, the mass $1$ stays at $x_0$, so the exponential cost of a set is $0$ if it contains $x_0$
and $\infty$ otherwise. -/
theorem satisfiesLDP_dirac [BorelSpace X] [T1Space X] (x₀ : X) :
    SatisfiesLDP (fun _ => Measure.dirac x₀) (diracRate x₀) := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    by_cases ha : a = ⊤
    · subst ha
      have : diracRate x₀ ⁻¹' Set.Iic ⊤ = Set.univ := by
        ext x
        simp
      rw [this]
      exact isClosed_univ
    · have hpre : diracRate x₀ ⁻¹' Set.Iic a = {x₀} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_singleton_iff]
        constructor
        · intro h
          by_contra hne
          rw [diracRate_apply_of_ne hne] at h
          exact ha (top_le_iff.mp h)
        · intro h
          rw [h, diracRate_apply_self]
          exact zero_le
      rw [hpre]
      exact isClosed_singleton
  · intro U hU
    by_cases hx : x₀ ∈ U
    · have hlim : liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((fun _ => Measure.dirac x₀) n U)) atTop = 0 := by
        rw [liminf_congr (Filter.Eventually.of_forall
          (fun n => dirac_ldp_term_eq_zero_of_mem hx n))]
        exact liminf_const 0
      rw [iInf_diracRate_of_mem hx, neg_zero, hlim]
    · have hev : ∀ᶠ n in atTop, ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((fun _ => Measure.dirac x₀) n U) = ⊥ := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact dirac_ldp_term_eq_bot_of_notMem hx hn
      have hlim : liminf (fun n => ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((fun _ => Measure.dirac x₀) n U)) atTop = ⊥ := by
        rw [liminf_congr hev]
        exact liminf_const ⊥
      rw [iInf_diracRate_of_notMem hx, EReal.neg_top, hlim]
  · intro F hF
    by_cases hx : x₀ ∈ F
    · have hlim : limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((fun _ => Measure.dirac x₀) n F)) atTop = 0 := by
        rw [limsup_congr (Filter.Eventually.of_forall
          (fun n => dirac_ldp_term_eq_zero_of_mem hx n))]
        exact limsup_const 0
      rw [iInf_diracRate_of_mem hx, neg_zero, hlim]
    · have hev : ∀ᶠ n in atTop, ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((fun _ => Measure.dirac x₀) n F) = ⊥ := by
        filter_upwards [eventually_ge_atTop 1] with n hn
        exact dirac_ldp_term_eq_bot_of_notMem hx hn
      have hlim : limsup (fun n => ((n : ℕ) : EReal)⁻¹ *
          ENNReal.log ((fun _ => Measure.dirac x₀) n F)) atTop = ⊥ := by
        rw [limsup_congr hev]
        exact limsup_const ⊥
      rw [iInf_diracRate_of_notMem hx, EReal.neg_top, hlim]

/-- **The absolute value is a good rate function.** The function $x \mapsto |x|$, viewed as a map
$\mathbb{R} \to [0, \infty]$, is a good rate function on $\mathbb{R}$.

It is continuous, hence lower semicontinuous, and its sub-level sets at finite levels are closed
intervals (or the singleton $\{0\}$ for a negative level), hence compact. -/
theorem isGoodRateFunction_abs :
    IsGoodRateFunction (fun x : ℝ => ENNReal.ofReal |x|) := by
  refine ⟨⟨?_⟩, ?_⟩
  · exact (ENNReal.continuous_ofReal.comp continuous_abs).lowerSemicontinuous
  · intro a
    by_cases ha : 0 ≤ a
    · have hset : {x : ℝ | ENNReal.ofReal |x| ≤ ENNReal.ofReal a} = Set.Icc (-a) a := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_Icc]
        constructor
        · intro h
          exact abs_le.mp ((ENNReal.ofReal_le_ofReal_iff ha).mp h)
        · intro h
          exact (ENNReal.ofReal_le_ofReal_iff ha).mpr (abs_le.mpr h)
      rw [hset]
      exact isCompact_Icc
    · push Not at ha
      have hset : {x : ℝ | ENNReal.ofReal |x| ≤ ENNReal.ofReal a} = {0} := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
        constructor
        · intro h
          have h0 : ENNReal.ofReal |x| = 0 := by
            apply le_antisymm _ (by positivity)
            rwa [ENNReal.ofReal_eq_zero.mpr (le_of_lt ha)] at h
          rw [ENNReal.ofReal_eq_zero] at h0
          exact abs_nonpos_iff.mp h0
        · intro h
          rw [h]
          simp [ENNReal.ofReal_eq_zero.mpr (le_of_lt ha)]
      rw [hset]
      exact isCompact_singleton

end MathlibExt.Probability.LargeDeviationPrinciple

end
