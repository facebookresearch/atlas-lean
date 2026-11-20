/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.ClusterExplorationFreeBoundary
import Code.FrontierD.FKFreeConnectionBoxEmbedding










open MeasureTheory SimpleGraph StatMech.Lattice

namespace StatMech.FrontierD

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]




theorem fkClusterExploration_condConnectionMass_le_boxConn
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V)
    (N : Nat)
    (iota : FK.ClusterUnexploredVertex G rho roots -> FK.boxVerts 2 N)
    (hiota : Function.Injective iota)
    (hadj : FK.ocd_AdjMatch
      (FK.clusterUnexploredGraph G rho roots) (FK.boxGraph 2 N) iota)
    (source target : FK.ClusterUnexploredVertex G rho roots)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q) :
    (∑ sigma : ConfigSpace (Sym2 V),
        (FK.ocd_innerRestrict
          (Subtype.val : FK.ClusterUnexploredVertex G rho roots -> V) ⁻¹'
          FKFiniteConnectionEvent
            (FK.clusterUnexploredGraph G rho roots) source target).indicator
          (fun _ => (1 : Real)) sigma *
        FK.condBcProb G
          (StatMech.Lattice.boundaryCliqueGraph
            (FK.clusterNoBoundary : V -> Prop)) p q
          (FK.clusterUnexploredPairEdges G rho roots) rho sigma) <=
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
          (FK.boxConnEvent 2 N (iota source) (iota target)) := by
  calc
    _ = ∑ omega,
          (FKFiniteConnectionEvent
            (FK.clusterUnexploredGraph G rho roots) source target).indicator
              (fun _ => (1 : Real)) omega *
            FK.fkProb (FK.clusterUnexploredGraph G rho roots) p q omega :=
      FK.clusterExploration_condBcProb_innerEvent_eq_free
        G rho roots hp hp1 (zero_lt_one.trans_le hq)
        (FKFiniteConnectionEvent
          (FK.clusterUnexploredGraph G rho roots) source target)
    _ <= _ := fkFiniteConnection_freeMass_le_boxConn
      (FK.clusterUnexploredGraph G rho roots) N iota hiota hadj
      source target hp hp1 hq

end

end StatMech.FrontierD
