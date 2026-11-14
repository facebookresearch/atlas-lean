/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Sampling.HorvitzThompson
public import MathlibExt.Probability.Sampling.HorvitzThompsonVariance
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Inclusion-weighted graph totals under a known sampling design

Order-`k` graph totals from a known probability design on vertices,
estimated with the shared Horvitz-Thompson total. The vertex sample
`s1` comes from a known design `p`; a `k`-subset is observed exactly
when it lies inside `s1` (induced observation). The inclusion
probability `π(M) = Pr(M ⊆ s1)` is the inclusion probability of the
pushed-forward design, and the estimator is the Horvitz-Thompson total
over the observed `k`-subsets, unbiased as a corollary of
`integral_horvitzThompsonTotal`.

Declared estimands: order 1 counts vertex quantities (first-order
`π_i`); order 2 counts dyad and edge quantities (joint `π_ij`, which
is `pairInclusionProbability`); order 3 counts motif quantities such
as triangles and stars (third-order `π_ijh`). Snowball designs are out
of scope unless their inclusion probabilities are supplied by the
design: never infer population network structure from an unspecified
snowball sample.

## References

- L.-C. Zhang and M. Patone, "Graph sampling", METRON 75 (2017),
  277-299. Graph total (1) and HT-estimator (2); induced observation
  when both endpoints lie in the vertex sample.
- O. Frank, "Estimation of graph totals", Scand. J. Statist. 4 (1977),
  81-89.
- D. G. Horvitz and D. J. Thompson, "A generalization of sampling
  without replacement from a finite universe", JASA 47(260) (1952),
  663-685.
-/

@[expose] public section

namespace MathlibExt.Probability.Networks

open MeasureTheory
open MathlibExt.Probability.Sampling

/-- Order-`k` graph total (Zhang-Patone (1)): `θ = ∑ M ∈ C_k, y M`. -/
noncomputable def graphTotal {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ) (y : Finset V → ℝ) : ℝ :=
  ∑ M ∈ Finset.powersetCard k Finset.univ, y M

/-- Induced observation design: push `p` forward along
`s ↦ {M ∈ C_k | M ⊆ s}` on `Finset (Finset V)`. -/
noncomputable def inducedDesign {V : Type*} [Fintype V] [DecidableEq V]
    (p : PMF (Finset V)) (k : ℕ) : PMF (Finset (Finset V)) :=
  PMF.map (fun s => (Finset.powersetCard k Finset.univ).filter (· ⊆ s)) p

/-- Inclusion probability `π(M) = Pr(M ⊆ s₁)`, as a vertex-level sum. -/
noncomputable def graphInclusionProbability {V : Type*} [Fintype V]
    [DecidableEq V] (p : PMF (Finset V)) (M : Finset V) : ℝ :=
  ∑ s, if M ⊆ s then (p s).toReal else 0

/-- Subtype-valued induced design on the `k`-subsets themselves. -/
noncomputable def inducedSubDesign {V : Type*} [Fintype V] [DecidableEq V]
    (p : PMF (Finset V)) (k : ℕ) :
    PMF (Finset ↥(Finset.powersetCard k (Finset.univ : Finset V))) :=
  PMF.map
    (fun s => Finset.univ.filter
      (fun m : ↥(Finset.powersetCard k (Finset.univ : Finset V)) =>
        m.val ⊆ s))
    p

/-- Dyad indicator of `G`: one exactly on two-vertex adjacent sets. -/
noncomputable def edgeIndicator {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset V) : ℝ :=
  if ∃ i j, M = {i, j} ∧ i ≠ j ∧ G.Adj i j then 1 else 0

/-- Horvitz-Thompson graph-total estimator (Zhang-Patone (2)): the shared
HT total over the observed `k`-subsets. -/
noncomputable def graphHT {V : Type*} [Fintype V] [DecidableEq V]
    (p : PMF (Finset V)) (k : ℕ) (y : Finset V → ℝ)
    (u : Finset ↥(Finset.powersetCard k (Finset.univ : Finset V))) : ℝ :=
  horvitzThompsonTotal (inducedSubDesign p k) (fun m => y m.val) u

/-- Inclusion probability of a pushforward design, as a sum over preimages. -/
theorem inclusionProbability_map {α : Type*} {γ : Type*} [Fintype α]
    [Fintype γ] [DecidableEq γ]
    (p : PMF α) (f : α → Finset γ) (M : γ) :
    inclusionProbability (PMF.map f p) M
      = ∑ a, if M ∈ f a then (p a).toReal else 0 := by
  classical
  have hmap : ∀ t : Finset γ, ((PMF.map f p) t).toReal
      = ∑ a, (if t = f a then (p a).toReal else 0) := by
    intro t
    rw [PMF.map_apply, tsum_fintype]
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro a _
      by_cases h : t = f a <;> simp [h]
    · intro a _
      by_cases h : t = f a <;> simp [h, p.apply_ne_top a]
  have hdist : ∀ t : Finset γ,
      (if M ∈ t then ∑ a, (if t = f a then (p a).toReal else 0)
        else (0 : ℝ))
        = ∑ a, (if M ∈ t then (if t = f a then (p a).toReal else 0)
          else 0) := by
    intro t
    split_ifs with h
    · rfl
    · simp
  unfold inclusionProbability
  simp only [hmap, hdist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : M ∈ f a
  · have hsingle : (∑ t, (if M ∈ t then
        (if t = f a then (p a).toReal else 0) else (0 : ℝ)))
        = (if M ∈ f a then (if f a = f a then (p a).toReal else 0)
          else (0 : ℝ)) := by
      apply Finset.sum_eq_single_of_mem (f a) (Finset.mem_univ _)
      intro t _ ht
      by_cases hMt : M ∈ t
      · simp [hMt, ht]
      · simp [hMt]
    rw [hsingle]
    simp [h]
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro t _
    by_cases htf : t = f a
    · subst htf
      simp [h]
    · by_cases hMt : M ∈ t
      · simp [hMt, htf]
      · simp [hMt]

/-- `π(M)`, as the inclusion probability of the pushed-forward design. -/
theorem graphInclusion_eq_induced {V : Type*} [Fintype V] [DecidableEq V]
    (p : PMF (Finset V)) (k : ℕ) (M : Finset V)
    (hM : M ∈ Finset.powersetCard k Finset.univ) :
    inclusionProbability (inducedDesign p k) M = graphInclusionProbability p M := by
  unfold inducedDesign graphInclusionProbability
  rw [inclusionProbability_map]
  apply Finset.sum_congr rfl
  intro s _
  have hiff : (M ∈ (Finset.powersetCard k Finset.univ).filter (· ⊆ s))
      ↔ M ⊆ s := by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hM, h⟩⟩
  simp only [hiff]

/-- Inclusion in the subtype design as a vertex-level subset sum. -/
theorem inclusionProbability_subDesign {V : Type*} [Fintype V]
    [DecidableEq V] (p : PMF (Finset V)) (k : ℕ)
    (m : ↥(Finset.powersetCard k Finset.univ)) :
    inclusionProbability (inducedSubDesign p k) m
      = ∑ s, if m.val ⊆ s then (p s).toReal else 0 := by
  unfold inducedSubDesign
  rw [inclusionProbability_map]
  apply Finset.sum_congr rfl
  intro s _
  have hiff : (m ∈ Finset.univ.filter
      (fun m_ : ↥(Finset.powersetCard k Finset.univ) => m_.val ⊆ s))
      ↔ m.val ⊆ s := by
    rw [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ m, h⟩⟩
  simp only [hiff]

/-- Order-1 inclusion is first-order: `π({i}) = πᵢ`. -/
theorem graphInclusion_singleton {V : Type*} [Fintype V] [DecidableEq V]
    (p : PMF (Finset V)) (i : V) :
    graphInclusionProbability p {i} = inclusionProbability p i := by
  unfold graphInclusionProbability inclusionProbability
  apply Finset.sum_congr rfl
  intro s _
  have hiff : ({i} ⊆ s) ↔ i ∈ s := Finset.singleton_subset_iff
  simp only [hiff]

/-- Order-2 inclusion is joint: `π({i,j}) = πᵢⱼ` (reuses the S02.4 notion). -/
theorem graphInclusion_pair {V : Type*} [Fintype V] [DecidableEq V]
    (p : PMF (Finset V)) (i j : V) :
    graphInclusionProbability p {i, j} = pairInclusionProbability p i j := by
  unfold graphInclusionProbability pairInclusionProbability
  apply Finset.sum_congr rfl
  intro s _
  have hiff : ({i, j} ⊆ s) ↔ (i ∈ s ∧ j ∈ s) := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  simp only [hiff]

/-- Unbiasedness of the HT graph-total estimator (Zhang-Patone (2)):
a corollary of `integral_horvitzThompsonTotal` for the pushed-forward
design. Covers order `k` (vertices at `k = 1`, dyads and edges at
`k = 2`, motifs at `k = 3`) whenever every `π(M)` is positive. -/
theorem integral_graphHT {V : Type*} [Fintype V] [DecidableEq V]
    (k : ℕ)
    [MeasurableSpace
      (Finset ↥(Finset.powersetCard k (Finset.univ : Finset V)))]
    [MeasurableSingletonClass
      (Finset ↥(Finset.powersetCard k (Finset.univ : Finset V)))]
    (p : PMF (Finset V)) (y : Finset V → ℝ)
    (hpos : ∀ m : ↥(Finset.powersetCard k (Finset.univ : Finset V)),
      0 < inclusionProbability (inducedSubDesign p k) m) :
    ∫ u, graphHT p k y u ∂(inducedSubDesign p k).toMeasure
      = graphTotal k y := by
  unfold graphHT
  rw [integral_horvitzThompsonTotal _ _ hpos]
  unfold graphTotal
  exact Finset.sum_coe_sort _ _

/-- Order-1 unbiasedness: this counts vertex quantities, with first-order
inclusion `πᵢ` (`graphInclusion_singleton`). -/
theorem integral_graphHT_order1 {V : Type*} [Fintype V] [DecidableEq V]
    [MeasurableSpace
      (Finset ↥(Finset.powersetCard 1 (Finset.univ : Finset V)))]
    [MeasurableSingletonClass
      (Finset ↥(Finset.powersetCard 1 (Finset.univ : Finset V)))]
    (p : PMF (Finset V)) (y : Finset V → ℝ)
    (hpos : ∀ m : ↥(Finset.powersetCard 1 (Finset.univ : Finset V)),
      0 < inclusionProbability (inducedSubDesign p 1) m) :
    ∫ u, graphHT p 1 y u ∂(inducedSubDesign p 1).toMeasure
      = graphTotal 1 y :=
  integral_graphHT 1 p y hpos

/-- Order-2 unbiasedness: this counts dyad and edge quantities, with joint
inclusion `πᵢⱼ` (`graphInclusion_pair`, `pairInclusionProbability`). -/
theorem integral_graphHT_order2 {V : Type*} [Fintype V] [DecidableEq V]
    [MeasurableSpace
      (Finset ↥(Finset.powersetCard 2 (Finset.univ : Finset V)))]
    [MeasurableSingletonClass
      (Finset ↥(Finset.powersetCard 2 (Finset.univ : Finset V)))]
    (p : PMF (Finset V)) (y : Finset V → ℝ)
    (hpos : ∀ m : ↥(Finset.powersetCard 2 (Finset.univ : Finset V)),
      0 < inclusionProbability (inducedSubDesign p 2) m) :
    ∫ u, graphHT p 2 y u ∂(inducedSubDesign p 2).toMeasure
      = graphTotal 2 y :=
  integral_graphHT 2 p y hpos

/-- Order-3 unbiasedness: this counts motif quantities (triangles, stars),
with third-order inclusion `πᵢⱼₕ`. -/
theorem integral_graphHT_order3 {V : Type*} [Fintype V] [DecidableEq V]
    [MeasurableSpace
      (Finset ↥(Finset.powersetCard 3 (Finset.univ : Finset V)))]
    [MeasurableSingletonClass
      (Finset ↥(Finset.powersetCard 3 (Finset.univ : Finset V)))]
    (p : PMF (Finset V)) (y : Finset V → ℝ)
    (hpos : ∀ m : ↥(Finset.powersetCard 3 (Finset.univ : Finset V)),
      0 < inclusionProbability (inducedSubDesign p 3) m) :
    ∫ u, graphHT p 3 y u ∂(inducedSubDesign p 3).toMeasure
      = graphTotal 3 y :=
  integral_graphHT 3 p y hpos

end MathlibExt.Probability.Networks
