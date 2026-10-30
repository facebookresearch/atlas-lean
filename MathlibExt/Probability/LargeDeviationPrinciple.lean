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

/-- A **rate function** `I : X → [0, ∞]` is, by definition, a
lower-semicontinuous function. This is the basic regularity hypothesis
used in the formulation of a large deviation principle. -/
structure IsRateFunction {X : Type*} [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop where
  lowerSemicontinuous : LowerSemicontinuous I

/-- A **good rate function** is a rate function whose finite sub-level
sets `{x | I x ≤ a}` are all compact. This is the
corrected form of v1's definition: v1 quantified over all
`a : ℝ≥0∞`, including `a = ⊤`, which forces the whole space to be
compact and makes the definition vacuous on non-compact spaces. -/
structure IsGoodRateFunction {X : Type*} [TopologicalSpace X] (I : X → ℝ≥0∞) : Prop
    extends IsRateFunction I where
  isCompact_levelSet : ∀ a : ℝ, IsCompact {x | I x ≤ ENNReal.ofReal a}

/-- A **convex rate function** on a real vector space is a rate
function `I` that is convex: `I(ax + by) ≤ a · I(x) + b · I(y)` for
all `x, y ∈ X` and all weights `a, b ≥ 0` with `a + b = 1`. -/
structure IsConvexRateFunction {X : Type*} [TopologicalSpace X] [AddCommMonoid X]
    [Module ℝ X] (I : X → ℝ≥0∞) : Prop extends IsRateFunction I where
  convex : ∀ ⦃x y : X⦄, ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    I (a • x + b • y) ≤ ENNReal.ofReal a * I x + ENNReal.ofReal b * I y

/-- A sequence of measures `μ : ℕ → Measure X` **satisfies the large
deviation principle** with rate function `I : X → [0, ∞]` and speed
`n` if `I` is a rate function and the following asymptotic bounds
hold: a `liminf` lower bound over open sets `U` and a `limsup` upper
bound over closed sets `F`. `OpensMeasurableSpace X` ensures that these sets
are measurable in the measure space used by `μ`. -/
structure SatisfiesLDP {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) (I : X → ℝ≥0∞) : Prop where
  isRateFunction : IsRateFunction I
  lower_bound : ∀ U : Set X, IsOpen U →
    - (⨅ x ∈ U, (I x : EReal)) ≤
      liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n U)) atTop
  upper_bound : ∀ F : Set X, IsClosed F →
    limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n F)) atTop ≤
      - (⨅ x ∈ F, (I x : EReal))

/-- A good rate function is a rate function. -/
theorem IsGoodRateFunction.isRateFunction {X : Type*} [TopologicalSpace X]
    {I : X → ℝ≥0∞} (h : IsGoodRateFunction I) : IsRateFunction I :=
  h.toIsRateFunction

/-- A convex rate function is a rate function. -/
theorem IsConvexRateFunction.isRateFunction {X : Type*} [TopologicalSpace X]
    [AddCommMonoid X] [Module ℝ X] {I : X → ℝ≥0∞} (h : IsConvexRateFunction I) :
    IsRateFunction I :=
  h.toIsRateFunction

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]

/-- The LDP lower bound for an arbitrary set `Γ`, with its interior in
place of the open set: `-inf_{interior Γ} I ≤ liminf (1/n) log μₙ(Γ)`. -/
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

/-- The LDP upper bound for an arbitrary set `Γ`, with its closure in
place of the closed set: `limsup (1/n) log μₙ(Γ) ≤ -inf_{closure Γ} I`. -/
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

/-- The LDP bounds hold for an arbitrary set `Γ` by monotonicity.
This stronger all-set corollary includes the textbook measurable/Borel-set form. -/
theorem SatisfiesLDP.borel_bounds [OpensMeasurableSpace X]
    {μ : ℕ → Measure X} {I : X → ℝ≥0∞}
    (h : SatisfiesLDP μ I) (Γ : Set X) :
    - (⨅ x ∈ interior Γ, (I x : EReal)) ≤
        liminf (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ∧
      limsup (fun n => ((n : ℕ) : EReal)⁻¹ * ENNReal.log (μ n Γ)) atTop ≤
        - (⨅ x ∈ closure Γ, (I x : EReal)) :=
  ⟨h.borel_lower_bound Γ, h.borel_upper_bound Γ⟩

/-- Conversely, bounds for measurable sets imply the open/closed form.
Open and closed sets are measurable by `OpensMeasurableSpace X`, and their
interior/closure equals the set itself. On a Borel space this is the
textbook Borel-set converse. -/
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
/-- The rate function of a Dirac mass at `x₀`: `0` at `x₀` and `∞`
elsewhere. -/
noncomputable def diracRate (x₀ : X) : X → ℝ≥0∞ :=
  Set.indicator {x₀}ᶜ (fun _ => (⊤ : ℝ≥0∞))

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- The Dirac rate function vanishes at its center. -/
lemma diracRate_apply_self (x₀ : X) : diracRate x₀ x₀ = 0 := by
  simp [diracRate]

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- The Dirac rate function is infinite away from its center. -/
lemma diracRate_apply_of_ne {x₀ x : X} (h : x ≠ x₀) : diracRate x₀ x = ⊤ := by
  simp [diracRate, h]

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- The infimum of the Dirac rate function over a set containing the
center is `0`. -/
lemma iInf_diracRate_of_mem {x₀ : X} {s : Set X} (h : x₀ ∈ s) :
    (⨅ x ∈ s, ((diracRate x₀ x : ℝ≥0∞) : EReal)) = 0 := by
  apply le_antisymm _ _
  · have hle := iInf₂_le (f := fun x (_ : x ∈ s) => ((diracRate x₀ x : ℝ≥0∞) : EReal)) x₀ h
    rwa [diracRate_apply_self, EReal.coe_ennreal_zero] at hle
  · apply le_iInf₂
    intro x _
    exact EReal.coe_ennreal_nonneg _

omit [TopologicalSpace X] [MeasurableSpace X] in
/-- The infimum of the Dirac rate function over a set not containing
the center is `∞`. -/
lemma iInf_diracRate_of_notMem {x₀ : X} {s : Set X} (h : x₀ ∉ s) :
    (⨅ x ∈ s, ((diracRate x₀ x : ℝ≥0∞) : EReal)) = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf₂
  intro x hx
  have hne : x ≠ x₀ := fun he => h (he ▸ hx)
  rw [diracRate_apply_of_ne hne, EReal.coe_ennreal_top]

omit [TopologicalSpace X] in
/-- The LDP term for a Dirac mass vanishes on a set containing the
center. -/
lemma dirac_ldp_term_eq_zero_of_mem {x₀ : X} {s : Set X} (h : x₀ ∈ s) (n : ℕ) :
    ((n : ℕ) : EReal)⁻¹ * ENNReal.log (Measure.dirac x₀ s) = 0 := by
  rw [Measure.dirac_apply_of_mem h, ENNReal.log_one, mul_zero]

omit [TopologicalSpace X] in
/-- The LDP term for a Dirac mass is `⊥` away from the center, for
`n ≥ 1`. -/
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

/-- A Dirac mass satisfies the large deviation principle with its
Dirac rate function: the mass `1` stays at `x₀`, so the exponential
cost of a set is `0` if it contains `x₀` and `∞` otherwise. -/
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

/-- `x ↦ ENNReal.ofReal |x|` is a good rate function on `ℝ`: it is
continuous, hence lower semicontinuous, and its finite sub-level sets
are closed intervals (or the singleton `{0}` for a negative level),
hence compact. -/
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
