/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































import Mathlib
import Code.FK.RandomCluster
import Code.FK.MonoBC
import Code.FK.InfiniteVolume
import Code.Lattice.BoundaryConditions

open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.FK
open StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable (bdry : V → Prop) [DecidablePred bdry]













theorem numClustersWired_eq_numClustersBC (ω : ConfigSpace (Sym2 V)) :
    numClustersWired G bdry ω
      = numClustersBC G (boundaryCliqueGraph bdry) ω :=
  (numClustersBC_boundaryClique G bdry ω).symm






theorem wiredFkWeight_eq_bcWeight (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkWeight G bdry p q ω
      = bcWeight G (boundaryCliqueGraph bdry) p q ω := by
  rw [wiredFkWeight, bcWeight, numClustersWired_eq_numClustersBC]




theorem wiredFkZ_eq_bcZ (p q : ℝ) :
    wiredFkZ G bdry p q = bcZ G (boundaryCliqueGraph bdry) p q := by
  rw [wiredFkZ, bcZ]
  exact Finset.sum_congr rfl fun ω _ => wiredFkWeight_eq_bcWeight G bdry p q ω











theorem wiredFkProb_eq_bcProb (p q : ℝ) (ω : ConfigSpace (Sym2 V)) :
    wiredFkProb G bdry p q ω
      = bcProb G (boundaryCliqueGraph bdry) p q ω := by
  rw [wiredFkProb, bcProb, wiredFkWeight_eq_bcWeight G bdry p q ω,
    wiredFkZ_eq_bcZ G bdry p q]





theorem wiredFkPMF_apply_eq_bcProb {p q : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    (wiredFkPMF G bdry hp hp1 hq) ω
      = ENNReal.ofReal (bcProb G (boundaryCliqueGraph bdry) p q ω) := by
  rw [wiredFkPMF, PMF.ofFintype_apply, wiredFkProb_eq_bcProb]

end IsingFK

end StatMech
