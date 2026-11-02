/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusFKDuality
public import PhyslibExt.StatisticalMechanics.RandomCluster.TranslationInvariance

/-!
# Double duality for the quarter-turn torus dual

For the quarter-turn torus duality, the double dual is the half turn, and the geometric defect of a
configuration plus that of its dual is `2`.

## i. Overview

`torusDualConfig` (from `TorusFKDuality`) applied twice is the half turn `torusHalfTurn`, which
preserves cluster counts. Hence `torusGeometricDefect_add_dual`: defect of `ω` plus defect of its
dual equals `2`. `torusDefectClassified_of_nonnegative` derives `TorusDefectClassified L` from the
hypothesis that every geometric defect is nonnegative, so it is conditional. For the cell version
the hypothesis is proved, see `TorusCellDefectClassify`.

## ii. Key results

- `torusGeometricDefect_add_dual`: defects of `ω` and its dual sum to `2` (unconditional).
- `torusDefectClassified_of_nonnegative`: classification, conditional on nonnegativity of the
  geometric defect.

## iii. Table of contents

- A. Half turn and double duality
- B. Defect relations

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager

/-! ## A. Half turn and double duality -/

/-- The half turn `(x, y) ↦ (-x, -y)` of the torus, as the square of the quarter turn. -/
def torusHalfTurn (L : ℕ) : (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) :=
  (torusQuarterTurn L).trans (torusQuarterTurn L)

@[simp] lemma torusHalfTurn_apply (L : ℕ) (v : ZMod L × ZMod L) :
    torusHalfTurn L v = (-v.1, -v.2) := by
  rfl

lemma torusHalfTurn_adj_iff (L : ℕ) [Fact (2 < L)]
    (u v : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusHalfTurn L u) (torusHalfTurn L v) ↔
      (onsTorusGraph L).Adj u v := by
  exact (torusQuarterTurn_adj_iff L (torusQuarterTurn L u)
    (torusQuarterTurn L v)).trans (torusQuarterTurn_adj_iff L u v)

lemma torusDualConfig_dualConfig (L : ℕ)
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusDualConfig L (torusDualConfig L ω) =
      FK.reCfg (torusHalfTurn L) ω := by
  funext e
  induction e using Sym2.inductionOn with
  | _ x y =>
      simp [torusDualConfig, FK.reCfg, torusHalfTurn]

lemma torus_numClusters_dualConfig_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.numClusters (onsTorusGraph L) (torusDualConfig L (torusDualConfig L ω)) =
      FK.numClusters (onsTorusGraph L) ω := by
  rw [torusDualConfig_dualConfig]
  exact FK.fkTI_numClusters_reCfg (onsTorusGraph L) (torusHalfTurn L)
    (torusHalfTurn_adj_iff L) ω

/-! ## B. Defect relations -/

lemma torusGeometricDefect_add_dual (L : ℕ) [Fact (2 < L)]
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

lemma torusGeometricDefect_le_two_of_dual_nonneg (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    (hdual : 0 ≤ torusGeometricDefect L
      (FK.openSub (onsTorusGraph L) (torusDualConfig L ω))) :
    torusGeometricDefect L (FK.openSub (onsTorusGraph L) ω) ≤ 2 := by
  have hsum := torusGeometricDefect_add_dual L ω
  linarith

/-- The configuration whose open edges are the edges of `K`. -/
noncomputable def torusConfigOfGraph (L : ℕ)
    (K : SimpleGraph (ZMod L × ZMod L)) :
    ConfigSpace (Sym2 (ZMod L × ZMod L)) := by
  classical
  exact fun e => decide (e ∈ K.edgeSet)

lemma torus_openSub_configOfGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    FK.openSub (onsTorusGraph L) (torusConfigOfGraph L K) = K := by
  classical
  ext x y
  simp only [FK.openSub_adj, torusConfigOfGraph, decide_eq_true_eq,
    SimpleGraph.mem_edgeSet]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hK h, h⟩

lemma torusGeometricDefect_add_dualCutGraph (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    torusGeometricDefect L K +
      torusGeometricDefect L (torusDualCutGraph L K) = 2 := by
  let ω := torusConfigOfGraph L K
  have hopen : FK.openSub (onsTorusGraph L) ω = K :=
    torus_openSub_configOfGraph L K hK
  have hdual := torus_openSub_dualConfig L ω
  rw [hopen] at hdual
  simpa only [hopen, hdual] using torusGeometricDefect_add_dual L ω

lemma torusDefectClassified_of_nonnegative (L : ℕ) [Fact (2 < L)]
    (hnonneg : ∀ K : SimpleGraph (ZMod L × ZMod L), K ≤ onsTorusGraph L →
      0 ≤ torusGeometricDefect L K) :
    TorusDefectClassified L := by
  intro K hK
  have h0 := hnonneg K hK
  have hdual0 := hnonneg (torusDualCutGraph L K) (torusDualCutGraph_le L K)
  have hsum := torusGeometricDefect_add_dualCutGraph L K hK
  omega

end StatMech.BeffaraDC
