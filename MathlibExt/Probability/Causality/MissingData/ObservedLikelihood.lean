/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Likelihood
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.SetNotation
public import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Basic.ENNReal.Operations
import Mathlib.Basic.ENNReal.Inv

/-! # Ignorability of the missingness mechanism for likelihood inference

This module formalizes the discrete factorization and proportionality
conclusions of Theorem 1 of Seaman, Galati, Jackson and Carlin (2013):
under realized missing at random (Definition 1) and variation independence of
the joint parameter space, the observed-data likelihood factorizes. Ignoring
the missingness mechanism additionally requires a nonzero coefficient.
The profile results use a supremum, not the source's attained maximum, and
do not assert that the profile is one of the fixed-parameter likelihoods.

The full data `Y` are discrete (counting measure). `F.dens θ y` is the
full-data density `f_θ(y)`, `g ψ y m` is the response-pattern law
`g_ψ(m | y)`, and `o y m` is the observed part of the full data `y` under
pattern `m`. The set `{y | o y m₀ = o y₀ m₀}` collects full-data values
consistent with the realized observed data. Realized MAR is an explicit
hypothesis on the realized pattern `m₀` and realized observed values only;
it says `g ψ y m₀` is constant over consistent `y` for each admissible
`ψ ∈ Prod.snd '' S`. Response laws outside this projection are unrestricted.

Likelihood ignorability is NOT complete-case unbiasedness: under realized MAR
the complete-case mean can still be biased (see the tests).

Not covered: frequentist (repeated-sampling) validity, everywhere MAR,
Bayesian inference, continuous full data (needs disintegration), estimation.

## References

* S. R. Seaman, J. Galati, D. Jackson, J. Carlin, What Is Meant by
  Missing at Random?, Statistical Science 28(2) (2013), 257-268,
  Definition 1 and Theorem 1.
* D. B. Rubin, Inference and missing data, Biometrika 63(3) (1976), 581-592.
-/

@[expose] public section

open scoped ENNReal Topology

namespace MathlibExt.Probability.Causality.MissingData

/-- Theorem 1 (i) of Seaman et al. (2013): under realized MAR and variation
independence, the joint observed-data likelihood `L1` factorizes into a
missingness factor depending only on `ψ` and a full-data factor depending
only on `θ`. -/
theorem likelihood_factorization
  {Y Θ Ψ M O : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
  (F : ProbabilityTheory.NormalizedDensityFamily Y Θ
    MeasureTheory.Measure.count)
  (g : Ψ → Y → PMF M) (o : Y → M → O)
  (y₀ : Y) (m₀ : M) (S : Set (Θ × Ψ))
  (hMAR : ∀ ψ ∈ Prod.snd '' S, ∀ y y',
    o y m₀ = o y₀ m₀ → o y' m₀ = o y₀ m₀ →
    g ψ y m₀ = g ψ y' m₀)
  (hS : S = (Prod.fst '' S) ×ˢ (Prod.snd '' S))
  (θ : Θ) (ψ : Ψ) :
  S.indicator
    (fun p : Θ × Ψ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
      (fun y => F.dens p.1 y * g p.2 y m₀) y) (θ, ψ) =
    (Prod.snd '' S).indicator (fun ψ => g ψ y₀ m₀) ψ *
      (Prod.fst '' S).indicator
        (fun θ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
          (fun y => F.dens θ y) y) θ := by
  have hmem : (θ, ψ) ∈ S ↔ θ ∈ Prod.fst '' S ∧ ψ ∈ Prod.snd '' S :=
    (Set.ext_iff.mp hS (θ, ψ)).trans Set.mem_prod
  have htsum : ∀ (θ : Θ) (ψ : Ψ), ψ ∈ Prod.snd '' S →
      (∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens θ y * g ψ y m₀) y) =
      g ψ y₀ m₀ * ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens θ y) y := by
    intro θ ψ hψ
    have hpoint : ∀ y,
        {y | o y m₀ = o y₀ m₀}.indicator
          (fun y => F.dens θ y * g ψ y m₀) y =
        g ψ y₀ m₀ *
          ({y | o y m₀ = o y₀ m₀}.indicator
            (fun y => F.dens θ y) y) := by
      intro y
      by_cases hy : y ∈ {y | o y m₀ = o y₀ m₀}
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        have hoy : o y m₀ = o y₀ m₀ := hy
        have hg : g ψ y m₀ = g ψ y₀ m₀ := hMAR ψ hψ y y₀ hoy rfl
        rw [hg, mul_comm]
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy,
          mul_zero]
    simp only [hpoint, ENNReal.tsum_mul_left]
  by_cases hmem' : (θ, ψ) ∈ S
  · rw [Set.indicator_of_mem hmem']
    have hθ : θ ∈ Prod.fst '' S := (hmem.mp hmem').1
    have hψ : ψ ∈ Prod.snd '' S := (hmem.mp hmem').2
    rw [Set.indicator_of_mem hψ, Set.indicator_of_mem hθ]
    change (∑' y, {y | o y m₀ = o y₀ m₀}.indicator
      (fun y => F.dens θ y * g ψ y m₀) y) =
      g ψ y₀ m₀ * ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens θ y) y
    exact htsum θ ψ hψ
  · rw [Set.indicator_of_notMem hmem']
    have hcon : ¬(θ ∈ Prod.fst '' S ∧ ψ ∈ Prod.snd '' S) :=
      fun h => hmem' (hmem.mpr h)
    have hnot : θ ∉ Prod.fst '' S ∨ ψ ∉ Prod.snd '' S := by
      by_cases hθ : θ ∈ Prod.fst '' S
      · right
        intro hψ
        exact hcon ⟨hθ, hψ⟩
      · left
        exact hθ
    cases hnot with
    | inl hθ =>
      rw [Set.indicator_of_notMem hθ, mul_zero]
    | inr hψ =>
      rw [Set.indicator_of_notMem hψ, zero_mul]

/-- Theorem 1 (ii) of Seaman et al. (2013): for fixed admissible `ψ`,
`L1` is exactly `g ψ y₀ m₀` times `L2`, uniformly in `θ`. The coefficient
is positive and at most one, so the proportionality is nondegenerate.
The indicators extend both likelihoods by zero outside the parameter space. -/
theorem likelihood_proportional_of_realizedMAR
  {Y Θ Ψ M O : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
  (F : ProbabilityTheory.NormalizedDensityFamily Y Θ
    MeasureTheory.Measure.count)
  (g : Ψ → Y → PMF M) (o : Y → M → O)
  (y₀ : Y) (m₀ : M) (S : Set (Θ × Ψ))
  (hMAR : ∀ ψ ∈ Prod.snd '' S, ∀ y y',
    o y m₀ = o y₀ m₀ → o y' m₀ = o y₀ m₀ →
    g ψ y m₀ = g ψ y' m₀)
  (hS : S = (Prod.fst '' S) ×ˢ (Prod.snd '' S))
  (ψ : Ψ) (hψ : ψ ∈ Prod.snd '' S) (hg : g ψ y₀ m₀ ≠ 0) :
  let c := g ψ y₀ m₀
  0 < c ∧ c ≤ 1 ∧ ∀ θ,
    S.indicator
      (fun p : Θ × Ψ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens p.1 y * g p.2 y m₀) y) (θ, ψ) =
      c * (Prod.fst '' S).indicator
        (fun θ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
          (fun y => F.dens θ y) y) θ := by
  refine ⟨pos_iff_ne_zero.mpr hg, (g ψ y₀).coe_le_one m₀, ?_⟩
  intro θ
  simpa only [Set.indicator_of_mem hψ] using
    likelihood_factorization F g o y₀ m₀ S hMAR hS θ ψ

/-- Pairwise ordering is a corollary of exact nonzero proportionality for
fixed `ψ`; it is not itself the relative-likelihood assertion. -/
theorem likelihood_le_iff_of_realizedMAR
  {Y Θ Ψ M O : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
  (F : ProbabilityTheory.NormalizedDensityFamily Y Θ
    MeasureTheory.Measure.count)
  (g : Ψ → Y → PMF M) (o : Y → M → O)
  (y₀ : Y) (m₀ : M) (S : Set (Θ × Ψ))
  (hMAR : ∀ ψ ∈ Prod.snd '' S, ∀ y y',
    o y m₀ = o y₀ m₀ → o y' m₀ = o y₀ m₀ →
    g ψ y m₀ = g ψ y' m₀)
  (hS : S = (Prod.fst '' S) ×ˢ (Prod.snd '' S))
  (ψ : Ψ) (hψ : ψ ∈ Prod.snd '' S) (hg : g ψ y₀ m₀ ≠ 0)
  (θ₁ θ₂ : Θ) (hθ₁ : θ₁ ∈ Prod.fst '' S)
  (hθ₂ : θ₂ ∈ Prod.fst '' S) :
  S.indicator
    (fun p : Θ × Ψ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
      (fun y => F.dens p.1 y * g p.2 y m₀) y) (θ₁, ψ) ≤
    S.indicator
    (fun p : Θ × Ψ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
      (fun y => F.dens p.1 y * g p.2 y m₀) y) (θ₂, ψ) ↔
    (∑' y, {y | o y m₀ = o y₀ m₀}.indicator
      (fun y => F.dens θ₁ y) y) ≤
    ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
      (fun y => F.dens θ₂ y) y := by
  have hfact :=
    (likelihood_proportional_of_realizedMAR F g o y₀ m₀ S hMAR hS ψ hψ hg).2.2
  rw [hfact θ₁, hfact θ₂, Set.indicator_of_mem hθ₁,
    Set.indicator_of_mem hθ₂]
  exact ENNReal.mul_le_mul_iff_right hg
    (PMF.apply_ne_top (g ψ y₀) m₀)

/-- Zero-allowed profile factorization, using `⨆` rather than an attained
maximum. The coefficient may vanish; nondegenerate proportionality is stated
separately in `iSup_likelihood_proportional_of_realizedMAR`. -/
theorem iSup_likelihood_eq_mul
  {Y Θ Ψ M O : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
  (F : ProbabilityTheory.NormalizedDensityFamily Y Θ
    MeasureTheory.Measure.count)
  (g : Ψ → Y → PMF M) (o : Y → M → O)
  (y₀ : Y) (m₀ : M) (S : Set (Θ × Ψ))
  (hMAR : ∀ ψ ∈ Prod.snd '' S, ∀ y y',
    o y m₀ = o y₀ m₀ → o y' m₀ = o y₀ m₀ →
    g ψ y m₀ = g ψ y' m₀)
  (hS : S = (Prod.fst '' S) ×ˢ (Prod.snd '' S))
  (θ : Θ) (hθ : θ ∈ Prod.fst '' S) :
  (⨆ ψ, S.indicator
    (fun p : Θ × Ψ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
      (fun y => F.dens p.1 y * g p.2 y m₀) y) (θ, ψ)) =
    (⨆ ψ ∈ Prod.snd '' S, g ψ y₀ m₀) *
      (∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens θ y) y) := by
  have hs_eq : (⨆ ψ, (Prod.snd '' S).indicator
      (fun ψ => g ψ y₀ m₀) ψ) =
      ⨆ ψ ∈ Prod.snd '' S, g ψ y₀ m₀ := by
    apply le_antisymm
    · apply iSup_le
      intro ψ
      by_cases hψ : ψ ∈ Prod.snd '' S
      · rw [Set.indicator_of_mem hψ]
        have h1 : g ψ y₀ m₀ ≤ ⨆ _ : ψ ∈ Prod.snd '' S, g ψ y₀ m₀ :=
          le_iSup (fun _ : ψ ∈ Prod.snd '' S => g ψ y₀ m₀) hψ
        have h2 : (⨆ _ : ψ ∈ Prod.snd '' S, g ψ y₀ m₀) ≤
            ⨆ ψ ∈ Prod.snd '' S, g ψ y₀ m₀ :=
          le_iSup (fun ψ => ⨆ _ : ψ ∈ Prod.snd '' S, g ψ y₀ m₀) ψ
        exact le_trans h1 h2
      · rw [Set.indicator_of_notMem hψ]
        exact bot_le
    · apply iSup_le
      intro ψ
      apply iSup_le
      intro hψ
      have hle : (Prod.snd '' S).indicator (fun ψ => g ψ y₀ m₀) ψ ≤
          ⨆ ψ, (Prod.snd '' S).indicator (fun ψ => g ψ y₀ m₀) ψ :=
        le_iSup _ ψ
      rw [Set.indicator_of_mem hψ] at hle
      exact hle
  have hfact : ∀ ψ, S.indicator
      (fun p : Θ × Ψ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens p.1 y * g p.2 y m₀) y) (θ, ψ) =
      (Prod.snd '' S).indicator (fun ψ => g ψ y₀ m₀) ψ *
        (∑' y, {y | o y m₀ = o y₀ m₀}.indicator
          (fun y => F.dens θ y) y) := by
    intro ψ
    have h := likelihood_factorization F g o y₀ m₀ S hMAR hS θ ψ
    rw [Set.indicator_of_mem hθ] at h
    exact h
  simp only [hfact, ← ENNReal.iSup_mul, hs_eq]

/-- The nondegenerate proportionality conclusion of Theorem 1 (iii) of
Seaman et al. (2013), for the supremum profile. An admissible response
parameter with positive realized-pattern mass makes the exact profile
coefficient positive and at most one. No maximizing parameter is asserted. -/
theorem iSup_likelihood_proportional_of_realizedMAR
  {Y Θ Ψ M O : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
  (F : ProbabilityTheory.NormalizedDensityFamily Y Θ
    MeasureTheory.Measure.count)
  (g : Ψ → Y → PMF M) (o : Y → M → O)
  (y₀ : Y) (m₀ : M) (S : Set (Θ × Ψ))
  (hMAR : ∀ ψ ∈ Prod.snd '' S, ∀ y y',
    o y m₀ = o y₀ m₀ → o y' m₀ = o y₀ m₀ →
    g ψ y m₀ = g ψ y' m₀)
  (hS : S = (Prod.fst '' S) ×ˢ (Prod.snd '' S))
  (hpos : ∃ ψ ∈ Prod.snd '' S, 0 < g ψ y₀ m₀) :
  let c := ⨆ ψ ∈ Prod.snd '' S, g ψ y₀ m₀
  0 < c ∧ c ≤ 1 ∧ ∀ θ ∈ Prod.fst '' S,
    (⨆ ψ, S.indicator
      (fun p : Θ × Ψ => ∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens p.1 y * g p.2 y m₀) y) (θ, ψ)) =
      c * (∑' y, {y | o y m₀ = o y₀ m₀}.indicator
        (fun y => F.dens θ y) y) := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨ψ, hψ, hg⟩ := hpos
    exact hg.trans_le (le_iSup₂
      (f := fun ψ (_ : ψ ∈ Prod.snd '' S) => g ψ y₀ m₀) ψ hψ)
  · exact iSup_le fun ψ => iSup_le fun _ => (g ψ y₀).coe_le_one m₀
  · intro θ hθ
    exact iSup_likelihood_eq_mul F g o y₀ m₀ S hMAR hS θ hθ

end MathlibExt.Probability.Causality.MissingData
