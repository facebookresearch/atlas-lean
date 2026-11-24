/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Tightness of families of probability measures

An indexed family is tight when the complements of compact sets have
uniformly small mass. The general definition uses Mathlib's
`MeasureTheory.IsTightMeasureSet` on the range of the family. On `ℝ`, this
is equivalent to uniformly concentrating mass on one bounded interval.
The real-line equivalence is adapted from
`v1/Atlas/TheoryOfProbability/code/Tightness.lean`.

The extracted Lecture 12 target "Definition (tightness)" prints
`μ_n[-M,M] < ε`. Its archived report explicitly treats the missing
complement as a notation error. This file follows the standard
complementary-mass reading, as the archived real-line definition does:
`μ_n [-M,M] ≥ 1 - ε`. The unrestricted compact-mass definition from the
archive is corrected to canonical tightness.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.TightnessFamily

/-- **Tight family of probability measures.** Let $\alpha$ be a space carrying a σ-algebra and a
topology. A family $(\mu_i)_{i \in \iota}$ of probability measures on $\alpha$ is tight if its
range $\{\mu_i : i \in \iota\}$ is a tight set of measures: for every $\varepsilon \in (0, \infty]$
there is a compact set $K \subseteq \alpha$ such that $\mu_i(\alpha \setminus K) \le \varepsilon$
for every index $i$. -/
def IsTightFamily {α : Type*} [MeasurableSpace α] [TopologicalSpace α]
    {ι : Type*} (μ : ι → Measure α) [∀ i, IsProbabilityMeasure (μ i)] : Prop :=
  IsTightMeasureSet (Set.range μ)

/-- **Tightness on the real line.** A family $(\mu_i)_{i \in \iota}$ of probability measures on
$\mathbb{R}$ is tight in the real-line sense if for every $\varepsilon \in (0, \infty]$ there is
$M \in \mathbb{R}$ such that $\mu_i([-M, M]) \ge 1 - \varepsilon$ for every index $i$. -/
def IsTightFamilyReal {ι : Type*} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ M : ℝ, ∀ i, μ i (Set.Icc (-M) M) ≥ 1 - ε

/-- On the real line, compact sets are measurable, so complementary mass
and mass at least `1 - ε` give equivalent tightness conditions. -/
private theorem compact_mass_iff_isTightMeasureSet {ι : Type*} {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)] :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set ℝ, IsCompact K ∧ ∀ i, μ i K ≥ 1 - ε) ↔
      IsTightMeasureSet (Set.range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  constructor
  · intro h ε hε
    obtain ⟨K, hK_compact, hK⟩ := h ε hε
    refine ⟨K, hK_compact, fun ν hν => ?_⟩
    obtain ⟨i, rfl⟩ := hν
    have hKmeas : MeasurableSet K := hK_compact.isClosed.measurableSet
    rw [measure_compl hKmeas (measure_ne_top _ _), measure_univ,
      tsub_le_iff_right]
    rcases le_total ε 1 with hε1 | hε1
    · calc (1 : ℝ≥0∞) = ε + (1 - ε) := (add_tsub_cancel_of_le hε1).symm
        _ ≤ ε + μ i K := add_le_add (le_refl ε) (hK i)
    · exact hε1.trans (le_add_of_nonneg_right (by positivity))
  · intro h ε hε
    obtain ⟨K, hK_compact, hK⟩ := h ε hε
    refine ⟨K, hK_compact, fun i => ?_⟩
    have hKmeas : MeasurableSet K := hK_compact.isClosed.measurableSet
    have hcompl : μ i Kᶜ ≤ ε := hK (μ i) ⟨i, rfl⟩
    have hKeq : μ i K = 1 - μ i Kᶜ := by
      rw [measure_compl hKmeas (measure_ne_top _ _), measure_univ]
      exact (ENNReal.sub_sub_cancel ENNReal.one_ne_top (prob_le_one (μ := μ i))).symm
    rw [hKeq]
    show (1 : ℝ≥0∞) - ε ≤ 1 - μ i Kᶜ
    rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = (1 - μ i Kᶜ) + μ i Kᶜ :=
          (tsub_add_cancel_of_le (prob_le_one (μ := μ i))).symm
      _ ≤ (1 - μ i Kᶜ) + ε := add_le_add (le_refl (1 - μ i Kᶜ)) hcompl

/-- **Real-line tightness implies tightness.** Let $(\mu_i)_{i \in \iota}$ be a family of
probability measures on $\mathbb{R}$. If the family is tight in the real-line sense, that is,
for every $\varepsilon \in (0, \infty]$ there is $M \in \mathbb{R}$ with
$\mu_i([-M, M]) \ge 1 - \varepsilon$ for every $i$, then the family is tight, that is, for every
$\varepsilon \in (0, \infty]$ there is a compact set $K \subseteq \mathbb{R}$ with
$\mu_i(\mathbb{R} \setminus K) \le \varepsilon$ for every $i$.

The interval $[-M, M]$ is compact. -/
theorem IsTightFamilyReal.isTightFamily {ι : Type*} {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)]
    (h : IsTightFamilyReal μ) : IsTightFamily μ := by
  apply (compact_mass_iff_isTightMeasureSet (μ := μ)).mp
  intro ε hε
  obtain ⟨M, hM⟩ := h ε hε
  exact ⟨Set.Icc (-M) M, isCompact_Icc, hM⟩

/-- **Tight families on the real line concentrate on bounded intervals.** Let
$(\mu_i)_{i \in \iota}$ be a family of probability measures on $\mathbb{R}$. If the family is
tight, that is, for every $\varepsilon \in (0, \infty]$ there is a compact set
$K \subseteq \mathbb{R}$ with $\mu_i(\mathbb{R} \setminus K) \le \varepsilon$ for every $i$, then
it is tight in the real-line sense: for every $\varepsilon \in (0, \infty]$ there is
$M \in \mathbb{R}$ with $\mu_i([-M, M]) \ge 1 - \varepsilon$ for every $i$.

The proof encloses the compact set in a closed ball. -/
theorem IsTightFamily.isTightFamilyReal {ι : Type*} {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)]
    (h : IsTightFamily μ) : IsTightFamilyReal μ := by
  have hMass := (compact_mass_iff_isTightMeasureSet (μ := μ)).mpr h
  intro ε hε
  obtain ⟨K, hK_compact, hK_meas⟩ := hMass ε hε
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK_compact.isBounded
  refine ⟨r, fun i => ?_⟩
  calc (1 : ℝ≥0∞) - ε ≤ μ i K := hK_meas i
    _ ≤ μ i (Set.Icc (-r) r) := by
        rw [← Real.closedBall_zero_eq_Icc]
        exact measure_mono hr

/-- **Tightness of a family is tightness of its range.** Let $\alpha$ be a space carrying a
σ-algebra and a topology. A family $(\mu_i)_{i \in \iota}$ of probability measures on $\alpha$ is
tight exactly when its range $\{\mu_i : i \in \iota\}$ is a tight set of measures. -/
theorem isTightFamily_iff_isTightMeasureSet {α : Type*}
    [MeasurableSpace α] [TopologicalSpace α] {ι : Type*} {μ : ι → Measure α}
    [∀ i, IsProbabilityMeasure (μ i)] :
    IsTightFamily μ ↔ IsTightMeasureSet (Set.range μ) :=
  Iff.rfl

/-- **Constant families on the real line are tight.** For every index type $\iota$ and every
probability measure $\mu$ on $\mathbb{R}$, the constant family $(\mu)_{i \in \iota}$ is tight. -/
theorem isTightFamily_of_singleton {ι : Type*} {μ : Measure ℝ}
    [IsProbabilityMeasure μ] :
    IsTightFamily (fun _ : ι => μ) := by
  have : ∀ i : ι, IsProbabilityMeasure μ := fun _ => inferInstance
  rw [isTightFamily_iff_isTightMeasureSet]
  apply IsTightMeasureSet.subset (isTightMeasureSet_singleton (μ := μ))
  rintro ν ⟨i, rfl⟩
  exact rfl

end MathlibExt.Probability.TightnessFamily
