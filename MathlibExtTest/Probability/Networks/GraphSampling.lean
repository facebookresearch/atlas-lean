/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Networks.GraphSampling
public import MathlibExt.Probability.Sampling.HorvitzThompson
public import MathlibExt.Probability.Sampling.HorvitzThompsonVariance
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.ENNReal.Real
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Finset.Card

/-!
# Boundary tests for inclusion-weighted graph totals

Exact-fraction checks on the 4-vertex graph with edges 01, 12, 23, 13:
the vertex total (number of degree-2 vertices is 2) under simple random
sampling of 2 vertices, the edge total (size 4) under induced simple
random sampling of 3 vertices, and the fixed-size design on `{0, 2}` and
`{1, 3}` with positive first-order but zero joint inclusion, whose
observable-dyad HT sum has expectation `1 ≠ 4`.
-/

open MathlibExt.Probability.Networks
open MathlibExt.Probability.Sampling

@[expose] public section

namespace MathlibExt.Probability.Networks.GraphSamplingTest

/-- Adjacency of the 4-vertex test graph (edges 01, 12, 23, 13). -/
@[reducible] def testEdge : Fin 4 → Fin 4 → Prop :=
  fun i j => (i, j) ∈ ([(0, 1), (1, 0), (1, 2), (2, 1), (2, 3), (3, 2),
    (1, 3), (3, 1)] : List (Fin 4 × Fin 4))

/-- The 4-vertex test graph with edges 01, 12, 23, 13. -/
def testGraph : SimpleGraph (Fin 4) where
  Adj := testEdge
  symm := Std.Symm.mk (by decide)
  loopless := Std.Irrefl.mk (by decide)

instance : DecidableRel testGraph.Adj := fun i j => by
  show Decidable (testEdge i j)
  infer_instance

/-- Every listed pair is adjacent. -/
theorem adj01 : testGraph.Adj 0 1 := by decide

/-- Every listed pair is adjacent. -/
theorem adj12 : testGraph.Adj 1 2 := by decide

/-- Every listed pair is adjacent. -/
theorem adj23 : testGraph.Adj 2 3 := by decide

/-- Every listed pair is adjacent. -/
theorem adj13 : testGraph.Adj 1 3 := by decide

/-- The degree-2 vertices are exactly `2` and `3`. -/
theorem deg2_iff : ∀ v : Fin 4,
    testGraph.degree v = 2 ↔ (v = 2 ∨ v = 3) := by
  intro v
  fin_cases v <;> decide

/-- Vertex outcome: one on singletons of degree-2 vertices `{2}`, `{3}`. -/
def yVertex : Finset (Fin 4) → ℝ :=
  fun M => if M = {2} ∨ M = {3} then 1 else 0

/-- The order-1 subsets of the vertex set. -/
theorem powersetCard_one_fin4 :
    Finset.powersetCard 1 (Finset.univ : Finset (Fin 4))
      = {{0}, {1}, {2}, {3}} := by decide

/-- Vertex total: the number of degree-2 vertices is 2. -/
theorem vertex_total : graphTotal 1 yVertex = 2 := by
  have e02 : ({0} : Finset (Fin 4)) ≠ {2} := by decide
  have e03 : ({0} : Finset (Fin 4)) ≠ {3} := by decide
  have e12 : ({1} : Finset (Fin 4)) ≠ {2} := by decide
  have e13 : ({1} : Finset (Fin 4)) ≠ {3} := by decide
  have h0 : yVertex {0} = 0 := by simp [yVertex, e02, e03]
  have h1 : yVertex {1} = 0 := by simp [yVertex, e12, e13]
  have h2 : yVertex {2} = 1 := by simp [yVertex]
  have h3 : yVertex {3} = 1 := by simp [yVertex]
  unfold graphTotal
  rw [powersetCard_one_fin4, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, h0, h1, h2, h3]
  norm_num

/-- The order-2 subsets of the vertex set. -/
theorem powersetCard_two_fin4 :
    Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))
      = {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}} := by decide

/-- Edge indicators on the six dyads. -/
theorem edge_values :
    edgeIndicator testGraph {0, 1} = 1
      ∧ edgeIndicator testGraph {0, 2} = 0
      ∧ edgeIndicator testGraph {0, 3} = 0
      ∧ edgeIndicator testGraph {1, 2} = 1
      ∧ edgeIndicator testGraph {1, 3} = 1
      ∧ edgeIndicator testGraph {2, 3} = 1 := by
  have w01 : ∃ i j : Fin 4, ({0, 1} : Finset (Fin 4)) = {i, j}
      ∧ i ≠ j ∧ testGraph.Adj i j := ⟨0, 1, rfl, by decide, adj01⟩
  have w12 : ∃ i j : Fin 4, ({1, 2} : Finset (Fin 4)) = {i, j}
      ∧ i ≠ j ∧ testGraph.Adj i j := ⟨1, 2, rfl, by decide, adj12⟩
  have w13 : ∃ i j : Fin 4, ({1, 3} : Finset (Fin 4)) = {i, j}
      ∧ i ≠ j ∧ testGraph.Adj i j := ⟨1, 3, rfl, by decide, adj13⟩
  have w23 : ∃ i j : Fin 4, ({2, 3} : Finset (Fin 4)) = {i, j}
      ∧ i ≠ j ∧ testGraph.Adj i j := ⟨2, 3, rfl, by decide, adj23⟩
  have n02 : ¬ ∃ i j : Fin 4, ({0, 2} : Finset (Fin 4)) = {i, j}
      ∧ i ≠ j ∧ testGraph.Adj i j := by decide
  have n03 : ¬ ∃ i j : Fin 4, ({0, 3} : Finset (Fin 4)) = {i, j}
      ∧ i ≠ j ∧ testGraph.Adj i j := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [edgeIndicator, w01, w12, w13, w23, n02, n03]

/-- Edge total: the graph has size 4. -/
theorem edge_total : graphTotal 2 (edgeIndicator testGraph) = 4 := by
  have h := edge_values
  unfold graphTotal
  rw [powersetCard_two_fin4, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2]
  norm_num

/-- Constant-mass sum over a supporting family. -/
private theorem uniform_mass_sum (C : Finset (Finset (Fin 4))) (c : ℝ)
    (mass : Finset (Fin 4) → ENNReal)
    (hmass : ∀ s, mass s = if s ∈ C then ENNReal.ofReal c else 0) :
    (∑ s, mass s) = C.card • ENNReal.ofReal c := by
  have hsub : (∑ s : Finset (Fin 4), mass s) = ∑ s ∈ C, mass s := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro s _ hs
    show mass s = 0
    simp only [hmass]
    simp [hs]
  have hval : ∀ s ∈ C, mass s = ENNReal.ofReal c := by
    intro s hs
    show mass s = ENNReal.ofReal c
    simp only [hmass]
    simp [hs]
  calc (∑ s : Finset (Fin 4), mass s) = ∑ s ∈ C, mass s := hsub
    _ = ∑ s ∈ C, ENNReal.ofReal c :=
        Finset.sum_congr rfl (fun s hs => hval s hs)
    _ = C.card • ENNReal.ofReal c := Finset.sum_const _

/-- Inclusion sum for a constant-mass-on-`C` design. -/
private theorem uniform_inclusion_sum (C : Finset (Finset (Fin 4)))
    (c : ℝ) (mass : Finset (Fin 4) → ENNReal)
    (hmass : ∀ s, mass s = if s ∈ C then ENNReal.ofReal c else 0)
    (p : PMF (Finset (Fin 4))) (hp : ∀ s, (p s).toReal = (mass s).toReal)
    (Q : Finset (Fin 4) → Prop) [DecidablePred Q] (hc : 0 ≤ c) :
    (∑ s, if Q s then (p s).toReal else 0)
      = (C.filter Q).card * c := by
  have hterm : ∀ s : Finset (Fin 4), (if Q s then (p s).toReal else 0)
      = (if s ∈ C.filter Q then c else 0) := by
    intro s
    simp only [Finset.mem_filter]
    by_cases hQ : Q s <;> by_cases hC : s ∈ C
    · simp [hQ, hC, hp s, hmass s, ENNReal.toReal_ofReal hc]
    · simp [hQ, hC, hp s, hmass s]
    · simp [hQ]
    · simp [hQ]
  calc (∑ s, if Q s then (p s).toReal else 0)
        = ∑ s, (if s ∈ C.filter Q then c else 0) :=
        Finset.sum_congr rfl (fun s _ => hterm s)
      _ = ∑ s ∈ C.filter Q, c := by
          have hsame : (∑ s, (if s ∈ C.filter Q then c else 0))
              = ∑ s ∈ C.filter Q, (if s ∈ C.filter Q then c else 0) := by
            refine (Finset.sum_subset
              (Finset.subset_univ (C.filter Q)) ?_).symm
            intro s _ hs
            show (if s ∈ C.filter Q then c else 0) = 0
            simp [hs]
          rw [hsame]
          apply Finset.sum_congr rfl
          intro s hs
          show (if s ∈ C.filter Q then c else 0) = c
          simp [hs]
      _ = (C.filter Q).card * c := by
          rw [Finset.sum_const, nsmul_eq_mul]

/-- SRS of 2 vertices: mass `1/6` on each 2-subset. -/
noncomputable def srs2Mass : Finset (Fin 4) → ENNReal :=
  fun s => if s ∈ Finset.powersetCard 2 Finset.univ
    then ENNReal.ofReal (1/6) else 0

/-- The SRS-2 masses sum to one. -/
theorem srs2Mass_sum : ∑ s, srs2Mass s = 1 := by
  have hcard : (Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))).card
      = 6 := by decide
  have h := uniform_mass_sum
    (Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))) (1/6)
    srs2Mass (fun s => rfl)
  rw [h, hcard]
  show (6 : ℕ) • ENNReal.ofReal (1/6 : ℝ) = 1
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (6 : ℕ),
    ← ENNReal.ofReal_mul (by norm_num)]
  have h6 : ((6 : ℕ) : ℝ) * (1/6 : ℝ) = 1 := by norm_num
  rw [h6, ENNReal.ofReal_one]

/-- SRS of 2 vertices as a normalized `PMF`. -/
noncomputable def srs2 : PMF (Finset (Fin 4)) :=
  PMF.ofFintype srs2Mass srs2Mass_sum

/-- SRS of 3 vertices: mass `1/4` on each 3-subset. -/
noncomputable def srs3Mass : Finset (Fin 4) → ENNReal :=
  fun s => if s ∈ Finset.powersetCard 3 Finset.univ
    then ENNReal.ofReal (1/4) else 0

/-- The SRS-3 masses sum to one. -/
theorem srs3Mass_sum : ∑ s, srs3Mass s = 1 := by
  have hcard : (Finset.powersetCard 3 (Finset.univ : Finset (Fin 4))).card
      = 4 := by decide
  have h := uniform_mass_sum
    (Finset.powersetCard 3 (Finset.univ : Finset (Fin 4))) (1/4)
    srs3Mass (fun s => rfl)
  rw [h, hcard]
  show (4 : ℕ) • ENNReal.ofReal (1/4 : ℝ) = 1
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (4 : ℕ),
    ← ENNReal.ofReal_mul (by norm_num)]
  have h4 : ((4 : ℕ) : ℝ) * (1/4 : ℝ) = 1 := by norm_num
  rw [h4, ENNReal.ofReal_one]

/-- SRS of 3 vertices as a normalized `PMF`. -/
noncomputable def srs3 : PMF (Finset (Fin 4)) :=
  PMF.ofFintype srs3Mass srs3Mass_sum

/-- First-order inclusion under SRS-2 is `1/2`. -/
theorem srs2_pi : ∀ i : Fin 4, inclusionProbability srs2 i = 1/2 := by
  intro i
  have hnn : (0 : ℝ) ≤ 1/6 := by norm_num
  have h := uniform_inclusion_sum
    (Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))) (1/6)
    srs2Mass (fun s => rfl) srs2 (fun s => rfl)
    (fun s => i ∈ s) hnn
  have hcard : ((Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))).filter
      (fun s => i ∈ s)).card = 3 := by
    fin_cases i <;> decide
  rw [hcard] at h
  unfold inclusionProbability
  norm_num at h
  exact h

/-- Joint inclusion under SRS-3 is `1/2`. -/
theorem srs3_pair : ∀ i j : Fin 4, i ≠ j →
    pairInclusionProbability srs3 i j = 1/2 := by
  intro i j hij
  have hnn : (0 : ℝ) ≤ 1/4 := by norm_num
  have h := uniform_inclusion_sum
    (Finset.powersetCard 3 (Finset.univ : Finset (Fin 4))) (1/4)
    srs3Mass (fun s => rfl) srs3 (fun s => rfl)
    (fun s => i ∈ s ∧ j ∈ s) hnn
  have hcard : ((Finset.powersetCard 3 (Finset.univ : Finset (Fin 4))).filter
      (fun s => i ∈ s ∧ j ∈ s)).card = 2 := by
    fin_cases i <;> fin_cases j <;> revert hij <;> decide
  rw [hcard] at h
  unfold pairInclusionProbability
  norm_num at h
  exact h

/-- Positivity for the order-1 induced design under SRS-2. -/
theorem hpos1 : ∀ m : ↥(Finset.powersetCard 1 (Finset.univ : Finset (Fin 4))),
    0 < inclusionProbability (inducedSubDesign srs2 1) m := by
  intro m
  rw [inclusionProbability_subDesign]
  obtain ⟨a, hM⟩ := Finset.card_eq_one.mp
    (Finset.mem_powersetCard.mp m.property).2
  rw [hM]
  have heq : (∑ s, if ({a} : Finset (Fin 4)) ⊆ s then (srs2 s).toReal
      else 0) = graphInclusionProbability srs2 {a} := rfl
  rw [heq, graphInclusion_singleton, srs2_pi a]
  norm_num

/-- Positivity for the order-2 induced design under SRS-3. -/
theorem hpos2 : ∀ m : ↥(Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))),
    0 < inclusionProbability (inducedSubDesign srs3 2) m := by
  intro m
  rw [inclusionProbability_subDesign]
  obtain ⟨i, j, hij, hM⟩ := Finset.card_eq_two.mp
    (Finset.mem_powersetCard.mp m.property).2
  rw [hM]
  have heq : (∑ s, if ({i, j} : Finset (Fin 4)) ⊆ s then (srs3 s).toReal
      else 0) = graphInclusionProbability srs3 {i, j} := rfl
  rw [heq, graphInclusion_pair, srs3_pair i j hij]
  norm_num

/-- Vertex expectation under SRS-2: `E[θ̂] = 2`. -/
theorem srs2_vertex_expectation :
    ∫ u, graphHT srs2 1 yVertex u ∂(inducedSubDesign srs2 1).toMeasure
      = 2 := by
  rw [integral_graphHT_order1 _ _ hpos1, vertex_total]

/-- Edge expectation under induced SRS-3: `E[θ̂] = 4`. -/
theorem srs3_edge_expectation :
    ∫ u, graphHT srs3 2 (edgeIndicator testGraph) u
      ∂(inducedSubDesign srs3 2).toMeasure = 4 := by
  rw [integral_graphHT_order2 _ _ hpos2, edge_total]

/-- Two-point support: `{0, 2}` and `{1, 3}`. -/
def twoPointSupport : Finset (Finset (Fin 4)) :=
  {{0, 2}, {1, 3}}

/-- Two-point design: mass `1/2` on `{0, 2}` and `{1, 3}`. -/
noncomputable def twoPointMass : Finset (Fin 4) → ENNReal :=
  fun s => if s ∈ twoPointSupport then ENNReal.ofReal (1/2) else 0

/-- The two-point masses sum to one. -/
theorem twoPointMass_sum : ∑ s, twoPointMass s = 1 := by
  have hcard : twoPointSupport.card = 2 := by decide
  have h := uniform_mass_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl)
  rw [h, hcard]
  show (2 : ℕ) • ENNReal.ofReal (1/2 : ℝ) = 1
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast (2 : ℕ),
    ← ENNReal.ofReal_mul (by norm_num)]
  have h2 : ((2 : ℕ) : ℝ) * (1/2 : ℝ) = 1 := by norm_num
  rw [h2, ENNReal.ofReal_one]

/-- Two-point design as a normalized `PMF`. -/
noncomputable def twoPoint : PMF (Finset (Fin 4)) :=
  PMF.ofFintype twoPointMass twoPointMass_sum

/-- First-order inclusion under the two-point design is `1/2`. -/
theorem twoPoint_pi : ∀ i : Fin 4, inclusionProbability twoPoint i = 1/2 := by
  intro i
  have hnn : (0 : ℝ) ≤ 1/2 := by norm_num
  have h := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl) (fun s => i ∈ s) hnn
  have hcard : (twoPointSupport.filter (fun s => i ∈ s)).card = 1 := by
    fin_cases i <;> decide
  rw [hcard] at h
  unfold inclusionProbability
  norm_num at h
  exact h

/-- Observable joint inclusions under the two-point design are `1/2`. -/
theorem twoPoint_pair_obs :
    pairInclusionProbability twoPoint 0 2 = 1/2
      ∧ pairInclusionProbability twoPoint 1 3 = 1/2 := by
  have hnn : (0 : ℝ) ≤ 1/2 := by norm_num
  have h02 := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl)
    (fun s => (0 : Fin 4) ∈ s ∧ (2 : Fin 4) ∈ s) hnn
  have h13 := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl)
    (fun s => (1 : Fin 4) ∈ s ∧ (3 : Fin 4) ∈ s) hnn
  have c02 : (twoPointSupport.filter
      (fun s => (0 : Fin 4) ∈ s ∧ (2 : Fin 4) ∈ s)).card = 1 := by decide
  have c13 : (twoPointSupport.filter
      (fun s => (1 : Fin 4) ∈ s ∧ (3 : Fin 4) ∈ s)).card = 1 := by decide
  rw [c02] at h02
  rw [c13] at h13
  unfold pairInclusionProbability
  norm_num at h02
  norm_num at h13
  exact ⟨h02, h13⟩

/-- Edge dyads never observed together have zero joint inclusion. -/
theorem twoPoint_pair_zero :
    pairInclusionProbability twoPoint 0 1 = 0
      ∧ pairInclusionProbability twoPoint 1 2 = 0
      ∧ pairInclusionProbability twoPoint 2 3 = 0 := by
  have hnn : (0 : ℝ) ≤ 1/2 := by norm_num
  have h01 := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl)
    (fun s => (0 : Fin 4) ∈ s ∧ (1 : Fin 4) ∈ s) hnn
  have h12 := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl)
    (fun s => (1 : Fin 4) ∈ s ∧ (2 : Fin 4) ∈ s) hnn
  have h23 := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl)
    (fun s => (2 : Fin 4) ∈ s ∧ (3 : Fin 4) ∈ s) hnn
  have c01 : (twoPointSupport.filter
      (fun s => (0 : Fin 4) ∈ s ∧ (1 : Fin 4) ∈ s)).card = 0 := by decide
  have c12 : (twoPointSupport.filter
      (fun s => (1 : Fin 4) ∈ s ∧ (2 : Fin 4) ∈ s)).card = 0 := by decide
  have c23 : (twoPointSupport.filter
      (fun s => (2 : Fin 4) ∈ s ∧ (3 : Fin 4) ∈ s)).card = 0 := by decide
  rw [c01] at h01
  rw [c12] at h12
  rw [c23] at h23
  unfold pairInclusionProbability
  norm_num at h01
  norm_num at h12
  norm_num at h23
  exact ⟨h01, h12, h23⟩

/-- Observable-dyad HT sum for the two-point design. -/
noncomputable def twoPointEst (s : Finset (Fin 4)) : ℝ :=
  ∑ M ∈ (Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))).filter
    (· ⊆ s),
    edgeIndicator testGraph M / graphInclusionProbability twoPoint M

/-- The observable-dyad sum is `0` on `{0, 2}` and `2` on `{1, 3}`. -/
theorem twoPointEst_values :
    twoPointEst {0, 2} = 0 ∧ twoPointEst {1, 3} = 2 := by
  have f02 : (Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))).filter
      (fun M : Finset (Fin 4) => M ⊆ ({0, 2} : Finset (Fin 4)))
      = {({0, 2} : Finset (Fin 4))} := by decide
  have f13 : (Finset.powersetCard 2 (Finset.univ : Finset (Fin 4))).filter
      (fun M : Finset (Fin 4) => M ⊆ ({1, 3} : Finset (Fin 4)))
      = {({1, 3} : Finset (Fin 4))} := by decide
  have e02 : edgeIndicator testGraph {0, 2} = 0 := edge_values.2.1
  have e13 : edgeIndicator testGraph {1, 3} = 1 := edge_values.2.2.2.2.1
  have hnn : (0 : ℝ) ≤ 1/2 := by norm_num
  have g02 := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl)
    (fun s => ({0, 2} : Finset (Fin 4)) ⊆ s) hnn
  have g13 := uniform_inclusion_sum twoPointSupport (1/2) twoPointMass
    (fun s => rfl) twoPoint (fun s => rfl)
    (fun s => ({1, 3} : Finset (Fin 4)) ⊆ s) hnn
  have cg02 : (twoPointSupport.filter
      (fun s => ({0, 2} : Finset (Fin 4)) ⊆ s)).card = 1 := by decide
  have cg13 : (twoPointSupport.filter
      (fun s => ({1, 3} : Finset (Fin 4)) ⊆ s)).card = 1 := by decide
  rw [cg02] at g02
  rw [cg13] at g13
  have p02 : graphInclusionProbability twoPoint {0, 2} = 1/2 := by
    unfold graphInclusionProbability
    norm_num at g02
    exact g02
  have p13 : graphInclusionProbability twoPoint {1, 3} = 1/2 := by
    unfold graphInclusionProbability
    norm_num at g13
    exact g13
  refine ⟨?_, ?_⟩
  · unfold twoPointEst
    rw [f02, Finset.sum_singleton, e02, p02]
    norm_num
  · unfold twoPointEst
    rw [f13, Finset.sum_singleton, e13, p13]
    norm_num

/-- The observable-dyad HT sum has expectation `1 ≠ 4`: edge totals need
joint inclusion probabilities. -/
theorem twoPoint_observable_expectation :
    ∫ s, twoPointEst s ∂twoPoint.toMeasure = 1 := by
  have hval02 : (twoPoint {0, 2}).toReal = 1/2 := by
    show (twoPointMass {0, 2}).toReal = 1/2
    have hm : ({0, 2} : Finset (Fin 4)) ∈ twoPointSupport := by decide
    simp only [twoPointMass, hm, ite_true]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hval13 : (twoPoint {1, 3}).toReal = 1/2 := by
    show (twoPointMass {1, 3}).toReal = 1/2
    have hm : ({1, 3} : Finset (Fin 4)) ∈ twoPointSupport := by decide
    simp only [twoPointMass, hm, ite_true]
    exact ENNReal.toReal_ofReal (by norm_num)
  have hest := twoPointEst_values
  rw [PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  have hsup : twoPointSupport = ({{0, 2}, {1, 3}} : Finset (Finset (Fin 4))) :=
    rfl
  have hsub : (∑ s : Finset (Fin 4), (twoPoint s).toReal * twoPointEst s)
      = ∑ s ∈ twoPointSupport, (twoPoint s).toReal * twoPointEst s := by
    refine (Finset.sum_subset (Finset.subset_univ twoPointSupport) ?_).symm
    intro s _ hs
    show (twoPoint s).toReal * twoPointEst s = 0
    have hz : (twoPoint s).toReal = 0 := by
      show (twoPointMass s).toReal = 0
      simp only [twoPointMass]
      simp [hs]
    rw [hz, zero_mul]
  rw [hsub, hsup, Finset.sum_insert (by decide), Finset.sum_singleton,
    hval02, hval13, hest.1, hest.2]
  norm_num

/-- The observable-dyad expectation misses the edge total. -/
theorem twoPoint_observable_expectation_ne :
    ∫ s, twoPointEst s ∂twoPoint.toMeasure
      ≠ graphTotal 2 (edgeIndicator testGraph) := by
  rw [twoPoint_observable_expectation, edge_total]
  norm_num

end MathlibExt.Probability.Networks.GraphSamplingTest
