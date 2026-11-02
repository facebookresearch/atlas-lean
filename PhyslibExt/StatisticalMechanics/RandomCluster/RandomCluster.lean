/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Configuration.ConfigSpace
/-!
# The random-cluster measure on a finite graph

The Fortuin–Kasteleyn random-cluster measure `φ_{G,p,q}` on edge configurations of a finite
graph `G`.

## i. Overview

An edge configuration `ω : ConfigSpace (Sym2 V)` declares each edge of `G` open (`true`) or
closed (`false`). Its open subgraph `openSub G ω` keeps exactly the open edges of `G`, and
`numClusters G ω` counts its connected components, isolated vertices included. For
`p ∈ (0, 1)` and `q > 0` the random-cluster weight of `ω` is
`p ^ o(ω) (1 - p) ^ c(ω) q ^ k(ω)`, where `o(ω)` and `c(ω)` count the open and closed edges of
`G` and `k(ω)` the clusters. Normalizing by the partition function `fkZ G p q` gives the
random-cluster probability `fkProb G p q`, packaged as a `PMF` by `fkPMF`. At `q = 1` the
measure is Bernoulli bond percolation with parameter `p`.

Coordinates of `ω` on non-edges of `G` do not enter the weight; the measure is uniform in them.

## ii. Key results

- `StatMech.FK.openSub` : the subgraph of open edges, with `openSub_eq_inf_fromEdgeSet`
  relating it to Mathlib's `SimpleGraph.fromEdgeSet`.
- `StatMech.FK.numClusters` : the number of open clusters.
- `StatMech.FK.fkWeight`, `StatMech.FK.fkZ`, `StatMech.FK.fkProb` : weight, partition
  function and probability, with positivity and `fkProb_sum_eq_one`.
- `StatMech.FK.fkPMF` : the random-cluster measure as a `PMF`.
- `StatMech.FK.fkWeight_one`, `StatMech.FK.fkZ_one` : at `q = 1` the weight is the
  Bernoulli product measure.

## iii. Table of contents

- A. Open subgraph and clusters
- B. The random-cluster weight and partition function
- C. The random-cluster probability
- D. The case `q = 1`

## iv. References

- C. M. Fortuin, P. W. Kasteleyn, *On the random-cluster model I. Introduction and relation to
  other models*, Physica 57 (1972).
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Chapter 1.

-/

@[expose] public section

open scoped BigOperators

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-!

## A. Open subgraph and clusters

-/

/-- The open subgraph of `G` under the edge configuration `ω`: the edges of `G` that `ω`
declares open. -/
def openSub (ω : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ω s(x, y) = true
  symm := by
    refine ⟨fun x y h => ?_⟩
    refine ⟨h.1.symm, ?_⟩
    rw [Sym2.eq_swap]; exact h.2
  loopless := ⟨fun x h => h.1.ne rfl⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
lemma openSub_adj (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (openSub G ω).Adj x y ↔ G.Adj x y ∧ ω s(x, y) = true :=
  Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
lemma openSub_le (ω : ConfigSpace (Sym2 V)) : openSub G ω ≤ G := fun _ _ h => h.1

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The open subgraph is `G ⊓ fromEdgeSet {e | ω e = true}` in Mathlib's terms. -/
lemma openSub_eq_inf_fromEdgeSet (ω : ConfigSpace (Sym2 V)) :
    openSub G ω = G ⊓ SimpleGraph.fromEdgeSet {e | ω e = true} := by
  ext x y
  simp only [openSub_adj, SimpleGraph.inf_adj, SimpleGraph.fromEdgeSet_adj, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h.1, h.2, h.1.ne⟩, fun h => ⟨h.1, h.2.1⟩⟩

/-- Adjacency in the open subgraph is decidable. -/
instance instDecidableRelOpenSubAdj (ω : ConfigSpace (Sym2 V)) :
    DecidableRel (openSub G ω).Adj := by
  intro x y
  change Decidable (G.Adj x y ∧ ω s(x, y) = true)
  infer_instance

/-- The number `k(ω)` of open clusters: connected components of the open subgraph, isolated
vertices included. -/
def numClusters (ω : ConfigSpace (Sym2 V)) : ℕ :=
  Fintype.card (openSub G ω).ConnectedComponent

/-!

## B. The random-cluster weight and partition function

-/

/-- The Bernoulli edge product `∏_{e ∈ E(G)} (p if e open, 1 - p if e closed)`. -/
def edgeProduct (p : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  ∏ e ∈ G.edgeFinset, (if ω e then p else 1 - p)

omit [DecidableEq V] in
lemma edgeProduct_pos {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (ω : ConfigSpace (Sym2 V)) :
    0 < edgeProduct G p ω := by
  unfold edgeProduct
  apply Finset.prod_pos
  intro e _
  split
  · exact hp
  · linarith

/-- The unnormalized random-cluster weight `p ^ o(ω) (1 - p) ^ c(ω) q ^ k(ω)`. -/
def fkWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  edgeProduct G p ω * q ^ numClusters G ω

lemma fkWeight_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < fkWeight G p q ω :=
  mul_pos (edgeProduct_pos G hp hp1 ω) (pow_pos hq _)

lemma fkWeight_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ fkWeight G p q ω :=
  (fkWeight_pos G hp hp1 hq ω).le

/-- The random-cluster partition function `Z_{G,p,q} = ∑_ω p ^ o(ω) (1 - p) ^ c(ω) q ^ k(ω)`. -/
def fkZ (p q : ℝ) : ℝ :=
  ∑ ω : ConfigSpace (Sym2 V), fkWeight G p q ω

lemma fkZ_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : 0 < fkZ G p q :=
  Finset.sum_pos (fun ω _ => fkWeight_pos G hp hp1 hq ω) Finset.univ_nonempty

lemma fkZ_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : fkZ G p q ≠ 0 :=
  (fkZ_pos G hp hp1 hq).ne'

/-!

## C. The random-cluster probability

-/

/-- The random-cluster probability `φ_{G,p,q}(ω) = fkWeight G p q ω / fkZ G p q`. -/
noncomputable def fkProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) : ℝ :=
  fkWeight G p q ω / fkZ G p q

lemma fkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ fkProb G p q ω :=
  div_nonneg (fkWeight_nonneg G hp hp1 hq ω) (fkZ_pos G hp hp1 hq).le

lemma fkProb_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < fkProb G p q ω :=
  div_pos (fkWeight_pos G hp hp1 hq ω) (fkZ_pos G hp hp1 hq)

lemma fkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), fkProb G p q ω = 1 := by
  unfold fkProb
  rw [← Finset.sum_div]
  exact div_self (fkZ_ne_zero G hp hp1 hq)

/-- The random-cluster measure `φ_{G,p,q}` as a probability mass function on edge
configurations. -/
noncomputable def fkPMF {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    PMF (ConfigSpace (Sym2 V)) :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (fkProb G p q ω)) <| by
    rw [← ENNReal.ofReal_sum_of_nonneg fun ω _ => fkProb_nonneg G hp hp1 hq ω,
      fkProb_sum_eq_one G hp hp1 hq]
    simp

@[simp]
lemma fkPMF_apply {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) :
    fkPMF G hp hp1 hq ω = ENNReal.ofReal (fkProb G p q ω) :=
  PMF.ofFintype_apply _ _

/-!

## D. The case `q = 1`

-/

/-- At `q = 1` the random-cluster weight is the Bernoulli product weight. -/
lemma fkWeight_one (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p 1 ω = edgeProduct G p ω := by
  unfold fkWeight
  rw [one_pow, mul_one]

lemma fkZ_one (p : ℝ) : fkZ G p 1 = ∑ ω : ConfigSpace (Sym2 V), edgeProduct G p ω := by
  unfold fkZ
  exact Finset.sum_congr rfl fun ω _ => fkWeight_one G p ω

end FK

end StatMech
