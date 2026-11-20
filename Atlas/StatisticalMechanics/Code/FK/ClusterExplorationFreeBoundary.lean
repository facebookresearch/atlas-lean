/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.OffCentreFreeDomination
import Code.FK.OffCentreEventLaw











open SimpleGraph

namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


def ClusterExploredVertex (rho : ConfigSpace (Sym2 V))
    (roots : Finset V) (v : V) : Prop :=
  ∃ r ∈ roots, (openSub G rho).Reachable r v


def ClusterUnexploredVertex (rho : ConfigSpace (Sym2 V))
    (roots : Finset V) :=
  {v : V // ¬ ClusterExploredVertex G rho roots v}

noncomputable instance instFintypeClusterUnexploredVertex
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    Fintype (ClusterUnexploredVertex G rho roots) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instDecidableEqClusterUnexploredVertex
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    DecidableEq (ClusterUnexploredVertex G rho roots) :=
  Classical.decEq _


noncomputable def clusterUnexploredGraph
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    SimpleGraph (ClusterUnexploredVertex G rho roots) :=
  G.comap Subtype.val

noncomputable instance instDecidableRelClusterUnexploredGraph
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    DecidableRel (clusterUnexploredGraph G rho roots).Adj :=
  fun _ _ => Classical.dec _



noncomputable def clusterUnexploredPairEdges
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) : Finset (Sym2 V) :=
  ocd_innerEdgeFinset
    (Vin := ClusterUnexploredVertex G rho roots)
    (Subtype.val : ClusterUnexploredVertex G rho roots -> V)

def clusterNoBoundary (_ : V) : Prop := False

private instance instDecidablePredNoClusterBoundary :
    DecidablePred (clusterNoBoundary : V -> Prop) :=
  fun _ => isFalse id

theorem clusterExploredVertex_of_openAdj_right
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) {x y : V}
    (hxy : (openSub G rho).Adj x y)
    (hy : ClusterExploredVertex G rho roots y) :
    ClusterExploredVertex G rho roots x := by
  rcases hy with ⟨r, hr, hry⟩
  exact ⟨r, hr, hry.trans hxy.symm.reachable⟩


theorem not_clusterOutsideGraph_adj_from_unexplored
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V)
    (x : ClusterUnexploredVertex G rho roots) (y : V) :
    ¬ (ocd_outsideGraph G
      (Subtype.val : ClusterUnexploredVertex G rho roots -> V)
      (clusterNoBoundary : V -> Prop) rho).Adj x.1 y := by
  classical
  letI : Fintype (ClusterUnexploredVertex G rho roots) :=
    instFintypeClusterUnexploredVertex G rho roots
  intro hadj
  rw [ocd_outsideGraph_adj] at hadj
  rcases hadj with hout | hboundary
  · rcases hout with ⟨hG, hopen, hrange⟩
    have hOpen : (openSub G rho).Adj x.1 y := ⟨hG, hopen⟩
    by_cases hy : ClusterExploredVertex G rho roots y
    · exact x.2 (clusterExploredVertex_of_openAdj_right G rho roots hOpen hy)
    · apply hrange
      let y' : ClusterUnexploredVertex G rho roots := ⟨y, hy⟩
      exact ⟨s(x, y'), rfl⟩
  · exact hboundary.2.1.elim

theorem eq_of_clusterOutsideGraph_reachable_from_unexplored
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) {x y : V}
    (hx : ¬ ClusterExploredVertex G rho roots x)
    (hreach : (ocd_outsideGraph G
      (Subtype.val : ClusterUnexploredVertex G rho roots -> V)
      (clusterNoBoundary : V -> Prop) rho).Reachable x y) :
    x = y := by
  exact hreach.elim fun p => by
    cases p with
    | nil => rfl
    | cons hstep rest =>
        exact False.elim
          (not_clusterOutsideGraph_adj_from_unexplored
            G rho roots ⟨x, hx⟩ _ hstep)



theorem clusterExploration_inducedWiring_eq_bot
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) :
    ocd_inducedWiring G
        (Subtype.val : ClusterUnexploredVertex G rho roots -> V)
        (clusterNoBoundary : V -> Prop) rho =
      (⊥ : SimpleGraph (ClusterUnexploredVertex G rho roots)) := by
  apply le_antisymm
  · intro x y hadj
    exfalso
    apply hadj.1
    exact Subtype.ext
      (eq_of_clusterOutsideGraph_reachable_from_unexplored
        G rho roots x.2 hadj.2)
  · exact bot_le




theorem clusterExploration_condBcProb_eq_free
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace
      (Sym2 (ClusterUnexploredVertex G rho roots))) :
    condBcProb G
        (StatMech.Lattice.boundaryCliqueGraph
          (clusterNoBoundary : V -> Prop)) p q
        (clusterUnexploredPairEdges G rho roots) rho
        (@ocd_psiExt
          (ClusterUnexploredVertex G rho roots) V
          (instFintypeClusterUnexploredVertex G rho roots)
          (by infer_instance)
          (Subtype.val : ClusterUnexploredVertex G rho roots -> V)
          rho omega) =
      fkProb (clusterUnexploredGraph G rho roots) p q omega := by
  classical
  letI : Fintype (ClusterUnexploredVertex G rho roots) :=
    instFintypeClusterUnexploredVertex G rho roots
  letI : DecidableEq (ClusterUnexploredVertex G rho roots) :=
    instDecidableEqClusterUnexploredVertex G rho roots
  have hdm := ocd_condBcProb_psiExt_eq_bcProb
    (Gin := clusterUnexploredGraph G rho roots)
    (Gout := G)
    (ιV := (Subtype.val : ClusterUnexploredVertex G rho roots -> V))
    (bdryOut := clusterNoBoundary)
    Subtype.val_injective (fun _ _ => Iff.rfl)
    hp hp1 hq rho omega
  have hfree := @bcProb_congr_boundary
    (ClusterUnexploredVertex G rho roots)
    (instFintypeClusterUnexploredVertex G rho roots)
    (instDecidableEqClusterUnexploredVertex G rho roots)
    (clusterUnexploredGraph G rho roots)
    (ocd_inducedWiring G
      (Subtype.val : ClusterUnexploredVertex G rho roots -> V)
      (clusterNoBoundary : V -> Prop) rho)
    (⊥ : SimpleGraph (ClusterUnexploredVertex G rho roots))
    (instDecidableRelClusterUnexploredGraph G rho roots)
    (instDecidableRelAdjOcd_inducedWiring _ _ _) (by infer_instance)
    (clusterExploration_inducedWiring_eq_bot G rho roots) p q omega
  rw [bcProb_bot_eq_fkProb] at hfree
  simpa only [clusterUnexploredPairEdges] using hdm.trans hfree




theorem clusterExploration_condBcProb_innerEvent_eq_free
    (rho : ConfigSpace (Sym2 V)) (roots : Finset V) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (A : Set (ConfigSpace
      (Sym2 (ClusterUnexploredVertex G rho roots)))) :
    (∑ sigma : ConfigSpace (Sym2 V),
        (ocd_innerRestrict
          (Subtype.val : ClusterUnexploredVertex G rho roots -> V) ⁻¹' A).indicator
            (fun _ => (1 : Real)) sigma *
          condBcProb G
            (StatMech.Lattice.boundaryCliqueGraph
              (clusterNoBoundary : V -> Prop)) p q
            (clusterUnexploredPairEdges G rho roots) rho sigma) =
      ∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          fkProb (clusterUnexploredGraph G rho roots) p q omega := by
  simpa only [clusterUnexploredPairEdges] using
    ocd_condBcProb_innerEvent_eq_of_pointwise
    (Gin := clusterUnexploredGraph G rho roots)
    (Gout := G)
    (iota := (Subtype.val : ClusterUnexploredVertex G rho roots -> V))
    (bdryOut := clusterNoBoundary)
    Subtype.val_injective (fun _ _ => Iff.rfl)
    hp hp1 hq rho
    (fun omega =>
      fkProb (clusterUnexploredGraph G rho roots) p q omega)
    (fun omega => clusterExploration_condBcProb_eq_free
      G rho roots hp hp1 hq omega) A

end

end StatMech.FK
