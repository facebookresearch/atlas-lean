/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Distributions.NegativeBinomial
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Data.ENat.Basic

/-!
# Coalescence in critical Galton–Watson processes with immigration
-/

@[expose] public section

namespace WantedExt.Biology.GaltonWatsonImmigrationCoalescenceWanted

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- An immigrant founder, identified by its arrival generation and index, and a descendant's
path of child indices. Different immigrants, including simultaneous arrivals, have distinct
roots. -/
structure Individual where
  arrival : ℕ
  immigrant : ℕ
  lineage : List ℕ
  deriving DecidableEq

/-- The generation in which an individual is born. -/
def birthGeneration (a : Individual) : ℕ := a.arrival + a.lineage.length

/-- The immigrants arriving in generation `n`. -/
def immigrants (n count : ℕ) : Finset Individual :=
  (Finset.range count).image (fun i => ⟨n, i, []⟩)

/-- The children of one individual, with distinct child indices. -/
def children (a : Individual) (count : ℕ) : Finset Individual :=
  (Finset.range count).image (fun i => ⟨a.arrival, a.immigrant, a.lineage ++ [i]⟩)

/-- The genealogical GWPI: generation zero consists of its immigrants; each subsequent
population consists of the previous generation's children and the new immigrants. Its size
satisfies `Z₀ = I₀` and `Zₙ₊₁ = ∑ a ∈ population n, ξ n a + Iₙ₊₁`. -/
def population {Ω : Type*} (ξ : ℕ → Individual → Ω → ℕ) (I : ℕ → Ω → ℕ) :
    ℕ → Ω → Finset Individual
  | 0, η => immigrants 0 (I 0 η)
  | n + 1, η =>
      (population ξ I n η).biUnion (fun a => children a (ξ n a η)) ∪
        immigrants (n + 1) (I (n + 1) η)

/-- All ancestors of an individual, including itself and its immigrant founder. -/
def ancestors (a : Individual) : Finset Individual :=
  (Finset.range (a.lineage.length + 1)).image
    (fun j => ⟨a.arrival, a.immigrant, a.lineage.take j⟩)

/-- The generation of the most recent common ancestor of a finite population, with infinity
when no common ancestor exists (also for the empty population). -/
noncomputable def coalescenceGeneration (G : Finset Individual) : ℕ∞ := by
  classical
  let common := (G.biUnion ancestors).filter (fun a => ∀ b ∈ G, a ∈ ancestors b)
  exact if common.Nonempty then ((common.sup birthGeneration : ℕ) : ℕ∞) else ⊤

/-- The arrival generation of the oldest immigrant family surviving in `G`, with infinity
if no family survives. -/
noncomputable def oldestImmigration (G : Finset Individual) : ℕ∞ :=
  G.inf (fun a => (a.arrival : ℕ∞))

/-- The fraction of ordered distinct pairs whose MRCA generation satisfies `event`.
The denominator is `|G| (|G| - 1)`, so sampling is uniform without replacement. The fraction
is zero when there are fewer than two individuals. -/
noncomputable def pairFraction (G : Finset Individual) (event : ℕ∞ → Prop) : ℝ := by
  classical
  let pairs := (G.product G).filter (fun ab => ab.1 ≠ ab.2)
  exact ((pairs.filter (fun ab => event (coalescenceGeneration {ab.1, ab.2}))).card : ℝ) /
    (pairs.card : ℝ)

/-- Conditional pairwise coalescence probability, conditioning on population size greater
than one and then choosing a uniform ordered distinct pair in that population. -/
noncomputable def pairProbability {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ξ : ℕ → Individual → Ω → ℕ) (I : ℕ → Ω → ℕ) (n : ℕ) (event : ℕ∞ → Prop) : ℝ :=
  (∫ η, pairFraction (population ξ I n η) event ∂P) /
    P.real {η | 1 < (population ξ I n η).card}

/-- The offspring variance under the criticality assumption. -/
noncomputable def offspringVariance (p : Measure ℕ) : ℝ :=
  (∫ j : ℕ, (j : ℝ) ^ 2 ∂p) - 1

/-- The mean number of immigrants. -/
noncomputable def immigrationMean (b : Measure ℕ) : ℝ := ∫ j : ℕ, (j : ℝ) ∂b

/-- The immigration parameter `γ = 2β/σ²`. -/
noncomputable def immigrationRatio (p b : Measure ℕ) : ℝ :=
  2 * immigrationMean b / offspringVariance p

/-- The intensity `γ exp(-2r/σ²)/r dr` on the positive half-line. -/
noncomputable def familyIntensity (sigmaSq γ : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity
    (fun r => ENNReal.ofReal (γ / r * Real.exp (-(2 * r / sigmaSq))))

/-- A Poisson random measure on the positive half-line: finite-intensity measurable sets
have Poisson counts and disjoint such sets have independent counts. The total intensity and
total number of atoms need not be finite. -/
def IsFamilyPoissonMeasure {Θ : Type*} [MeasurableSpace Θ] (Q : Measure Θ)
    (W : Θ → Measure ℝ) (ν : Measure ℝ) : Prop :=
  AEMeasurable W Q ∧
  (∀ᵐ θ ∂Q, W θ (Set.Ioi (0 : ℝ)).compl = 0) ∧
  (∀ s : Set ℝ, MeasurableSet s → s ⊆ Set.Ioi 0 → ν s < ⊤ →
    HasLaw (fun θ => W θ s)
      (Measure.map (fun j : ℕ => (j : ℝ≥0∞))
        (poissonMeasure ⟨(ν s).toReal, ENNReal.toReal_nonneg⟩)) Q) ∧
  (∀ m : ℕ, ∀ s : Fin m → Set ℝ,
    (∀ i, MeasurableSet (s i) ∧ s i ⊆ Set.Ioi 0 ∧ ν (s i) < ⊤) →
    Pairwise (fun i j => Disjoint (s i) (s j)) →
    iIndepFun (fun i θ => W θ (s i)) Q)

/-- Greenwood–Yule at the parameters of the surviving immigration-family count:
Gamma shape `γ`, rate `(1-u)/u`, gives the negative binomial mass with success parameter `1-u`. -/
theorem poissonMixture_familyCount (γ u : ℝ) (hγ : 0 < γ) (hu₀ : 0 < u) (hu₁ : u < 1)
    (k : ℕ) :
    poissonMixtureReal (gammaMeasure γ ((1 - u) / u)) k = negBinomialPMF γ (1 - u) k := by
  have hr : 0 < (1 - u) / u := div_pos (sub_pos.mpr hu₁) hu₀
  rw [poissonMixtureReal_gammaMeasure hγ hr,
    negBinomialReal_eq_negBinomialPMF hγ (div_pos hγ hr).le]
  have hp : γ / (γ + γ / ((1 - u) / u)) = 1 - u := by
    field_simp
    ring
  rw [hp]

/-- The squared-mass ratio of the Poisson families. -/
noncomputable def poissonFamilyRatio (μ : Measure ℝ) : ℝ :=
  (∫ r : ℝ, r ^ 2 ∂μ) / (∫ r : ℝ, r ∂μ) ^ 2

/-- `φ(j, μ)`: average over the independent exponential family sizes while holding the count
`j` and Poisson measure `μ` fixed. Index zero denotes the source's first exponential variable. -/
noncomputable def phi {Θ : Type*} [MeasurableSpace Θ] (Q : Measure Θ)
    (ω : ℕ → Θ → ℝ) (j : ℕ) (μ : Measure ℝ) : ℝ :=
  ∫ θ, ((∑ i ∈ Finset.range j, (ω i θ) ^ 2) + ∫ r : ℝ, r ^ 2 ∂μ) /
    ((∑ i ∈ Finset.range j, ω i θ) + ∫ r : ℝ, r ∂μ) ^ 2 ∂Q

/-- **Coalescence limits for a critical Galton–Watson process with immigration.**
Under Assumption 1, the probability of a pair's MRCA lying in `[k,n)`, conditional on `Zₙ > 1`,
tends to `E φ(Nᵤᴵ,W)` whenever `k/n → u ∈ (0,1)`. The conditional probability of a finite
pairwise MRCA tends to the expected Poisson squared-mass ratio; the conditional probability
of a finite common ancestor of the whole nonempty population tends to zero. The unconditional
probability that the oldest surviving immigrant family arrived after `k` tends to `(1-u)^γ`.
MRCA times are absolute generations, and distinct immigrant founders never coalesce.

The auxiliary variables are independent: exponential sizes have rate `2/σ²`, `W` has intensity
`γ exp(-2r/σ²)/r dr`, and `Nᵤᴵ` has negative binomial mass `negBinomialPMF γ (1-u) k` for all
`k : ℕ`, including zero. `poissonMixture_familyCount` identifies this law using Greenwood–Yule.
No independence between counts at different values of `u` is required.

Source: R.-L. Liu, Y.-X. Ren and Y. Wang, "Coalescence times for critical Galton–Watson processes
with immigration", Statistics and Probability Letters 210 (2024), 110121,
https://doi.org/10.1016/j.spl.2024.110121. Numbering from https://arxiv.org/abs/2307.07384v1:
Section 1, Assumption 1 and Theorems 1.1–1.2; Section 2, Corollary 2.6. -/
theorem_wanted tendsto_coalescence_immigration
    {Ω Θ : Type*} [MeasurableSpace Ω] [MeasurableSpace Θ]
    (P : Measure Ω) (Q : Measure Θ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (p b : Measure ℕ) [IsProbabilityMeasure p] [IsProbabilityMeasure b]
    (ξ : ℕ → Individual → Ω → ℕ) (I : ℕ → Ω → ℕ)
    (hξ : ∀ n a, HasLaw (ξ n a) p P) (hI : ∀ n, HasLaw (I n) b P)
    (hind : iIndepFun (β := fun _ : ℕ ⊕ (ℕ × Individual) => ℕ)
      (fun j => match j with
      | .inl n => I n
      | .inr (n, a) => ξ n a) P)
    (hp₀₁ : 0 < p.real {0} + p.real {1} ∧ p.real {0} + p.real {1} < 1)
    (hcritical : (∫ j : ℕ, (j : ℝ) ∂p) = 1)
    (hsecond : Integrable (fun j : ℕ => (j : ℝ) ^ 2) p)
    (hb₀ : b.real {0} < 1)
    (hmean : Integrable (fun j : ℕ => (j : ℝ)) b)
    (ω : ℕ → Θ → ℝ) (W : Θ → Measure ℝ) (N : ℝ → Θ → ℕ)
    (hω : ∀ i, HasLaw (ω i) (expMeasure (2 / offspringVariance p)) Q)
    (hωind : iIndepFun ω Q)
    (hW : IsFamilyPoissonMeasure Q W
      (familyIntensity (offspringVariance p) (immigrationRatio p b)))
    (hN : ∀ u : ℝ, 0 < u → u < 1 → AEMeasurable (N u) Q ∧
      ∀ k : ℕ, Q.real {θ | N u θ = k} = negBinomialPMF (immigrationRatio p b) (1 - u) k)
    (hNW : ∀ u : ℝ, 0 < u → u < 1 → IndepFun (N u) W Q)
    (hωNW : ∀ u : ℝ, 0 < u → u < 1 →
      IndepFun (fun θ i => ω i θ) (fun θ => (N u θ, W θ)) Q) :
    (∀ u : ℝ, 0 < u → u < 1 → ∀ k : ℕ → ℕ,
      Tendsto (fun n => (k n : ℝ) / (n : ℝ)) atTop (𝓝 u) →
      Tendsto (fun n => pairProbability P ξ I n (fun x => (k n : ℕ∞) ≤ x ∧ x < (n : ℕ∞)))
        atTop (𝓝 (∫ θ, phi Q ω (N u θ) (W θ) ∂Q))) ∧
    Tendsto (fun n => pairProbability P ξ I n (fun x => x < ⊤))
      atTop (𝓝 (∫ θ, poissonFamilyRatio (W θ) ∂Q)) ∧
    Tendsto (fun n =>
      P.real {η | 0 < (population ξ I n η).card ∧
        coalescenceGeneration (population ξ I n η) < ⊤} /
      P.real {η | 0 < (population ξ I n η).card}) atTop (𝓝 0) ∧
    (∀ u : ℝ, 0 < u → u < 1 → ∀ k : ℕ → ℕ,
      Tendsto (fun n => (k n : ℝ) / (n : ℝ)) atTop (𝓝 u) →
      Tendsto (fun n => P.real {η | (k n : ℕ∞) < oldestImmigration (population ξ I n η)})
        atTop (𝓝 ((1 - u) ^ immigrationRatio p b)))

end WantedExt.Biology.GaltonWatsonImmigrationCoalescenceWanted
