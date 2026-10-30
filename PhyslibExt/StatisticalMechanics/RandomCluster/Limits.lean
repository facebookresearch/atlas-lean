/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.StochasticOrder.StochasticDomination
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKG
public import PhyslibExt.StatisticalMechanics.RandomCluster.InfiniteVolume
/-!
# Free–wired comparison for finite FK measures

For `q ≥ 1` the free random-cluster measure on a finite graph is dominated by the wired one.

## i. Overview

Write `k(ω)` for the number of open clusters and `k¹(ω)` for the number after wiring the
boundary. The two counts satisfy the mixed supermodularity
`k(a) + k¹(b) ≤ k(a ⊓ b) + k¹(a ⊔ b)`. Together with the log-modularity of the Bernoulli edge
product this gives, for `q ≥ 1`, Holley's condition
`φ⁰(a) φ¹(b) ≤ φ⁰(a ⊓ b) φ¹(a ⊔ b)`, and Holley's inequality yields `φ⁰(A) ≤ φ¹(A)` for every
increasing event `A`. Since `extendEdge` is monotone, the domination carries over to the box
measures on `ℤ^d`.

## ii. Key results

- `mixed_supermodular` : the mixed supermodularity of free and wired cluster counts.
- `freeWiredProb_cross` : Holley's condition for the pair (free, wired).
- `fkProb_le_wiredFkProb_increasing` : free ≤ wired on increasing events of a finite graph.
- `freeFiniteMeasure_dominated` : `φ⁰_n ≼ φ¹_n` for the box measures on `ℤ^d`.

## iii. Table of contents

- A. Open subgraphs and cluster counts
- B. Mixed supermodularity and Holley's condition
- C. Domination on a finite graph
- D. Domination of the box measures

## iv. References

- R. Holley, *Remarks on the FKG inequalities*, Comm. Math. Phys. 36 (1974).
- G. R. Grimmett, *The Random-Cluster Model*, Springer, 2006.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory
open StatMech.Lattice SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-!
## A. Open subgraphs and cluster counts
-/

lemma openSub_eq_openGraph (ω : ConfigSpace (Sym2 V)) :
    openSub G ω = StatMech.Lattice.openGraph G ω := by
  ext x y; simp [openSub_adj, StatMech.Lattice.openGraph_adj]

lemma numClusters_eq_numClustersFree (ω : ConfigSpace (Sym2 V)) :
    numClusters G ω = numClustersFree G ω := by
  rw [numClusters, numClustersFree, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (by rw [openSub_eq_openGraph])

lemma openGraph_inf (a b : ConfigSpace (Sym2 V)) :
    StatMech.Lattice.openGraph G (a ⊓ b)
      = StatMech.Lattice.openGraph G a ⊓ StatMech.Lattice.openGraph G b := by
  ext x y
  simp only [StatMech.Lattice.openGraph_adj, SimpleGraph.inf_adj]
  change (G.Adj x y ∧ (a s(x, y) && b s(x, y)) = true) ↔ _
  rw [Bool.and_eq_true]; tauto

lemma openGraph_sup (a b : ConfigSpace (Sym2 V)) :
    StatMech.Lattice.openGraph G (a ⊔ b)
      = StatMech.Lattice.openGraph G a ⊔ StatMech.Lattice.openGraph G b := by
  ext x y
  simp only [StatMech.Lattice.openGraph_adj, SimpleGraph.sup_adj]
  change (G.Adj x y ∧ (a s(x, y) || b s(x, y)) = true) ↔ _
  rw [Bool.or_eq_true]; tauto

/-!
## B. Mixed supermodularity and Holley's condition
-/

/-- Mixed supermodularity of cluster counts: `k(a) + k¹(b) ≤ k(a ⊓ b) + k¹(a ⊔ b)`, where `k¹`
counts clusters with the boundary wired. -/
lemma mixed_supermodular (a b : ConfigSpace (Sym2 V)) :
    numClusters G a + numClustersWired G bdry b
      ≤ numClusters G (a ⊓ b) + numClustersWired G bdry (a ⊔ b) := by
  classical
  set A := StatMech.Lattice.openGraph G a with hA
  set B := StatMech.Lattice.openGraph G b with hB
  set C := boundaryCliqueGraph (V := V) bdry with hC
  have hka : numClusters G a = Nat.card A.ConnectedComponent := by
    rw [numClusters_eq_numClustersFree, numClustersFree]
  have hk1b : numClustersWired G bdry b = Nat.card (B ⊔ C).ConnectedComponent := by
    rw [numClustersWired, wiredGraph]
  have hkab : numClusters G (a ⊓ b) = Nat.card (A ⊓ B).ConnectedComponent := by
    rw [numClusters_eq_numClustersFree, numClustersFree, openGraph_inf]
  have hk1ab : numClustersWired G bdry (a ⊔ b)
      = Nat.card (A ⊔ B ⊔ C).ConnectedComponent := by
    rw [numClustersWired, wiredGraph, openGraph_sup]
  rw [hka, hk1b, hkab, hk1ab]
  have hmarg := card_connectedComponent_marginal (A := A ⊓ B) (B := A) inf_le_left (B ⊔ C)
  have e1 : (A ⊓ B) ⊔ (B ⊔ C) = B ⊔ C := by
    rw [← sup_assoc, sup_comm (A ⊓ B) B, inf_comm A B, sup_inf_self]
  have e2 : A ⊔ (B ⊔ C) = A ⊔ B ⊔ C := by rw [sup_assoc]
  rw [e1, e2] at hmarg
  omega

/-- Holley's condition for the free and wired weights when `q ≥ 1`. See also `bcWeight_cross`, which
contains this as the case of boundary wirings `⊥ ≤ clique`. -/
lemma freeWiredWeight_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkWeight G p q a * wiredFkWeight G bdry p q b
      ≤ fkWeight G p q (a ⊓ b) * wiredFkWeight G bdry p q (a ⊔ b) := by
  have hcluster :
      q ^ numClusters G a * q ^ numClustersWired G bdry b
        ≤ q ^ numClusters G (a ⊓ b) * q ^ numClustersWired G bdry (a ⊔ b) := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hq (mixed_supermodular G bdry a b)
  have hedge := edgeProduct_logModular G p a b
  have hpow_nonneg : (0 : ℝ) ≤ edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) :=
    mul_nonneg (edgeProduct_pos G hp hp1 _).le (edgeProduct_pos G hp hp1 _).le
  have hLHS : fkWeight G p q a * wiredFkWeight G bdry p q b
      = (edgeProduct G p a * edgeProduct G p b)
          * (q ^ numClusters G a * q ^ numClustersWired G bdry b) := by
    unfold fkWeight wiredFkWeight; ring
  have hRHS : fkWeight G p q (a ⊓ b) * wiredFkWeight G bdry p q (a ⊔ b)
      = (edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b))
          * (q ^ numClusters G (a ⊓ b) * q ^ numClustersWired G bdry (a ⊔ b)) := by
    unfold fkWeight wiredFkWeight; ring
  rw [hLHS, hRHS, hedge]
  have hcomm : edgeProduct G p (a ⊔ b) * edgeProduct G p (a ⊓ b)
      = edgeProduct G p (a ⊓ b) * edgeProduct G p (a ⊔ b) := by ring
  rw [hcomm]
  exact mul_le_mul_of_nonneg_left hcluster hpow_nonneg

/-- Holley's condition for the free and wired probabilities when `q ≥ 1`. -/
lemma freeWiredProb_cross {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (a b : ConfigSpace (Sym2 V)) :
    fkProb G p q a * wiredFkProb G bdry p q b
      ≤ fkProb G p q (a ⊓ b) * wiredFkProb G bdry p q (a ⊔ b) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hZ1 : 0 < fkZ G p q := fkZ_pos G hp hp1 hq0
  have hZ2 : 0 < wiredFkZ G bdry p q := wiredFkZ_pos G bdry hp hp1 hq0
  unfold fkProb wiredFkProb
  rw [div_mul_div_comm, div_mul_div_comm,
    div_le_div_iff_of_pos_right (mul_pos hZ1 hZ2)]
  exact freeWiredWeight_cross G bdry hp hp1 hq a b

/-!
## C. Domination on a finite graph
-/

/-- For `q ≥ 1` the free random-cluster measure gives every increasing event at most the probability
the wired measure gives it. -/
lemma fkProb_le_wiredFkProb_increasing {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb G p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * wiredFkProb G bdry p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  refine holley_dominates ?_ ?_ ?_ ?_ hA
  · exact fun ω => fkProb_nonneg G hp hp1 hq0 ω
  · exact fun ω => wiredFkProb_nonneg G bdry hp hp1 hq0 ω
  · rw [fkProb_sum_eq_one G hp hp1 hq0, wiredFkProb_sum_eq_one G bdry hp hp1 hq0]
  · exact fun a b => freeWiredProb_cross G bdry hp hp1 hq a b

/-!
## D. Domination of the box measures
-/

lemma monotone_extendEdge (d n : ℕ) : Monotone (extendEdge d n) := by
  intro x y hxy e
  unfold extendEdge
  split
  · next h => exact hxy h.choose
  · exact le_refl _

lemma isIncreasing_preimage_extendEdge (d n : ℕ)
    {A : Set (ConfigSpace (Sym2 (Site d)))} (hA : IsIncreasing A) :
    IsIncreasing (extendEdge d n ⁻¹' A) :=
  fun _ _ hxy hx => hA (monotone_extendEdge d n hxy) hx

lemma fkPMF_toMeasure_toReal (d n : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n)))) :
    ((fkPMF (boxGraph d n) hp hp1 hq).toMeasure S).toReal
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          S.indicator (fun _ => (1 : ℝ)) ω * fkProb (boxGraph d n) p q ω := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, fkPMF_apply,
        ENNReal.toReal_ofReal (fkProb_nonneg (boxGraph d n) hp hp1 hq ω), one_mul]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]; simp
  · by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, fkPMF_apply]; exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]; simp

lemma wiredFkPMF_toMeasure_toReal (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (S : Set (ConfigSpace (Sym2 (boxVerts d n)))) :
    ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure S).toReal
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          S.indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  classical
  rw [PMF.toMeasure_apply_fintype, ENNReal.toReal_sum (fun a _ => ?_)]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem hω, wiredFkPMF,
        PMF.ofFintype_apply,
        ENNReal.toReal_ofReal (wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n) hp hp1 hq ω),
        one_mul]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem hω]; simp
  · by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha, wiredFkPMF, PMF.ofFintype_apply]
      exact ENNReal.ofReal_ne_top
    · rw [Set.indicator_of_notMem ha]; simp

/-- For `q ≥ 1` the free box measure is stochastically dominated by the wired box measure on `ℤ^d`:
`φ⁰_n ≼ φ¹_n`. -/
lemma freeFiniteMeasure_dominated (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (freeFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq)
        : Measure (ConfigSpace (Sym2 (Site d))))
      ≼ (wiredFiniteMeasure d n hp hp1 (zero_lt_one.trans_le hq)
        : Measure (ConfigSpace (Sym2 (Site d)))) := by
  set hq0 : 0 < q := zero_lt_one.trans_le hq with hhq0
  intro A hA _
  rename_i hAinc
  have hfree : (freeFiniteMeasure d n hp hp1 hq0 : Measure _).real A
      = ((fkPMF (boxGraph d n) hp hp1 hq0).toMeasure (extendEdge d n ⁻¹' A)).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  have hwired : (wiredFiniteMeasure d n hp hp1 hq0 : Measure _).real A
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq0).toMeasure
          (extendEdge d n ⁻¹' A)).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hfree, hwired, fkPMF_toMeasure_toReal, wiredFkPMF_toMeasure_toReal]
  exact fkProb_le_wiredFkProb_increasing (boxGraph d n) (boxBoundary d n) hp hp1 hq
    (isIncreasing_preimage_extendEdge d n hAinc)

end FK

end StatMech
