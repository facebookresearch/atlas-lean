/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.BeffaraDC.TorusFKDuality
import Code.FK.TranslationInvariance

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusHalfTurn (L : ℕ) : (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) :=
  (torusQuarterTurn L).trans (torusQuarterTurn L)

@[simp] theorem torusHalfTurn_apply (L : ℕ) (v : ZMod L × ZMod L) :
    torusHalfTurn L v = (-v.1, -v.2) := by
  rfl


theorem torusHalfTurn_adj_iff (L : ℕ) [Fact (2 < L)]
    (u v : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusHalfTurn L u) (torusHalfTurn L v) ↔
      (onsTorusGraph L).Adj u v := by
  exact (torusQuarterTurn_adj_iff L (torusQuarterTurn L u)
    (torusQuarterTurn L v)).trans (torusQuarterTurn_adj_iff L u v)



theorem torusDualConfig_dualConfig (L : ℕ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusDualConfig L (torusDualConfig L ω) =
      FK.reCfg (torusHalfTurn L) ω := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp [torusDualConfig, FK.reCfg, torusHalfTurn, Sym2.map_map]


theorem torus_numClusters_dualConfig_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.numClusters (onsTorusGraph L) (torusDualConfig L (torusDualConfig L ω)) =
      FK.numClusters (onsTorusGraph L) ω := by
  rw [torusDualConfig_dualConfig]
  exact FK.fkTI_numClusters_reCfg (onsTorusGraph L) (torusHalfTurn L)
    (torusHalfTurn_adj_iff L) ω


theorem torusGeometricDefect_add_dual (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) +
      torusGeometricDefect L
        (FK.openSub (onsTorusGraph L) (torusDualConfig L ω)) = 2 := by
  have hopen := torus_dual_openCount L ω
  have hfaces := torus_numClusters_dualConfig L ω
  have hfacesDual := torus_numClusters_dualConfig L (torusDualConfig L ω)
  have hclusters2 := torus_numClusters_dualConfig_dualConfig L ω
  have hedge : (onsTorusGraph L).edgeFinset.card = 2 * L ^ 2 :=
    onsTorus_card_edges L
  have hvert : Nat.card (ZMod L × ZMod L) = L ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]
    ring
  have hclusters :
      Nat.card (FK.openSub (onsTorusGraph L) ω).ConnectedComponent =
        FK.numClusters (onsTorusGraph L) ω := by
    unfold FK.numClusters
    rw [Nat.card_eq_fintype_card]
  have hclustersDual :
      Nat.card (FK.openSub (onsTorusGraph L)
        (torusDualConfig L ω)).ConnectedComponent =
        FK.numClusters (onsTorusGraph L) (torusDualConfig L ω) := by
    unfold FK.numClusters
    rw [Nat.card_eq_fintype_card]
  unfold torusGeometricDefect
  rw [torus_openSub_edge_ncard, torus_openSub_edge_ncard]
  rw [hclusters, hclustersDual]
  rw [← hfaces, ← hfacesDual, hclusters2]
  have hopen_le : FK.openCount (onsTorusGraph L) ω ≤
      (onsTorusGraph L).edgeFinset.card := by
    unfold FK.openCount
    exact Finset.card_filter_le _ _
  have hopenAdd :
      FK.openCount (onsTorusGraph L) (torusDualConfig L ω) +
        FK.openCount (onsTorusGraph L) ω =
          (onsTorusGraph L).edgeFinset.card := by
    omega
  have htorus : (onsTorusGraph L).edgeFinset.card =
      2 * Nat.card (ZMod L × ZMod L) := by
    omega
  have hopenAddZ :
      (FK.openCount (onsTorusGraph L) (torusDualConfig L ω) : ℤ) +
        FK.openCount (onsTorusGraph L) ω =
          (onsTorusGraph L).edgeFinset.card := by
    exact_mod_cast hopenAdd
  have htorusZ : ((onsTorusGraph L).edgeFinset.card : ℤ) =
      2 * Nat.card (ZMod L × ZMod L) := by
    exact_mod_cast htorus
  linarith



theorem torusGeometricDefect_le_two_of_dual_nonneg (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    (hdual : 0 ≤ torusGeometricDefect L
      (FK.openSub (onsTorusGraph L) (torusDualConfig L ω))) :
    torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) ≤ 2 := by
  have hsum := torusGeometricDefect_add_dual L ω
  linarith


noncomputable def torusConfigOfGraph (L : ℕ)
    (K : SimpleGraph (ZMod L × ZMod L)) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) := by
  classical
  exact fun e => decide (e ∈ K.edgeSet)



theorem torus_openSub_configOfGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    FK.openSub (onsTorusGraph L) (torusConfigOfGraph L K) = K := by
  classical
  ext x y
  simp only [FK.openSub_adj, torusConfigOfGraph, decide_eq_true_eq,
    SimpleGraph.mem_edgeSet]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hK h, h⟩


theorem torusGeometricDefect_add_dualCutGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    torusGeometricDefect L K +
      torusGeometricDefect L (torusDualCutGraph L K) = 2 := by
  let ω := torusConfigOfGraph L K
  have hopen : FK.openSub (onsTorusGraph L) ω = K :=
    torus_openSub_configOfGraph L K hK
  have hdual := torus_openSub_dualConfig L ω
  rw [hopen] at hdual
  simpa only [hopen, hdual] using torusGeometricDefect_add_dual L ω




theorem torusDefectClassified_of_nonnegative (L : ℕ) [Fact (2 < L)]
    (hnonneg : ∀ K : SimpleGraph (ZMod L × ZMod L), K ≤ onsTorusGraph L →
      0 ≤ torusGeometricDefect L K) :
    TorusDefectClassified L := by
  intro K hK
  have h0 := hnonneg K hK
  have hdual0 := hnonneg (torusDualCutGraph L K) (torusDualCutGraph_le L K)
  have hsum := torusGeometricDefect_add_dualCutGraph L K hK
  omega

end StatMech.BeffaraDC
