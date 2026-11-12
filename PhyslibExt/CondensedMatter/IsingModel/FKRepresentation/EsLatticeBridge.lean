/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.MonoBC

/-!
# Wired FK measures as random-cluster measures with a boundary clique

The wired random-cluster measure of `FK` coincides with the boundary-condition random-cluster
measure in which the boundary vertices are joined by a clique.

## i. Overview

Wiring the boundary of a finite graph identifies all boundary vertices into one cluster; adding a
clique on the boundary has the same effect on cluster counts. Hence the wired cluster count,
weight, partition function and probability agree with their boundary-clique counterparts, and
the wired FK probability mass function is the boundary-clique probability.

## ii. Key results

- `numClustersWired_eq_numClustersBC` : wired and boundary-clique cluster counts agree.
- `wiredFkProb_eq_bcProb` : the wired FK probability is the boundary-clique probability.
- `wiredFkPMF_apply_eq_bcProb` : the same for the probability mass function.

## iii. Table of contents

- A. Wired and boundary-clique random-cluster measures

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 4.2.
-/

@[expose] public section

open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.FK
open StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]

/-! ## A. Wired and boundary-clique random-cluster measures -/

lemma numClustersWired_eq_numClustersBC (ω : ConfigSpace (Sym2 V)) :
    numClustersWired G bdry ω
      = numClustersBC G (boundaryCliqueGraph bdry) ω :=
  (numClustersBC_boundaryClique G bdry ω).symm

lemma wiredFkWeight_eq_bcWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q ω
      = bcWeight G (boundaryCliqueGraph bdry) p q ω := by
  rw [wiredFkWeight, bcWeight, numClustersWired_eq_numClustersBC]

lemma wiredFkZ_eq_bcZ (p q : ℝ) :
    wiredFkZ G bdry p q = bcZ G (boundaryCliqueGraph bdry) p q := by
  rw [wiredFkZ, bcZ]
  exact Finset.sum_congr rfl fun ω _ => wiredFkWeight_eq_bcWeight G bdry p q ω

lemma wiredFkProb_eq_bcProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q ω
      = bcProb G (boundaryCliqueGraph bdry) p q ω := by
  rw [wiredFkProb, bcProb, wiredFkWeight_eq_bcWeight G bdry p q ω,
    wiredFkZ_eq_bcZ G bdry p q]

lemma wiredFkPMF_apply_eq_bcProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    (wiredFkPMF G bdry hp hp1 hq) ω
      = ENNReal.ofReal (bcProb G (boundaryCliqueGraph bdry) p q ω) := by
  rw [wiredFkPMF, PMF.ofFintype_apply, wiredFkProb_eq_bcProb]

end IsingFK

end StatMech
