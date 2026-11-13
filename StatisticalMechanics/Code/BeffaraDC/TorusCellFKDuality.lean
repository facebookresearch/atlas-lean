/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.BeffaraDC.TorusCellDual

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager


noncomputable def torusCellPrimalWeight (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (K : SimpleGraph (ZMod L × ZMod L)) : ℝ :=
  edgeProductCount p (onsTorusGraph L).edgeFinset.card K.edgeSet.ncard *
    q ^ Nat.card K.ConnectedComponent


noncomputable def torusCellDualWeight (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (K : SimpleGraph (ZMod L × ZMod L)) : ℝ :=
  edgeProductCount p (onsTorusGraph L).edgeFinset.card
      ((onsTorusGraph L).edgeFinset.card - K.edgeSet.ncard) *
    q ^ torusCellFaceCount L K


theorem torusCell_primalWeight_openSub (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusCellPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q ω := by
  unfold torusCellPrimalWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, dlt_edgeProduct_eq_count]
  unfold FK.numClusters
  rw [Nat.card_eq_fintype_card]



theorem torusCell_dualWeight_openSub (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusCellDualWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q (torusCellDualConfig L ω) := by
  unfold torusCellDualWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, ← torusCell_dual_openCount,
    ← dlt_edgeProduct_eq_count, torusCell_numClusters_dualConfig]


theorem torusCell_subgraph_edgeCount_le (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L) :
    K.edgeSet.ncard ≤ (onsTorusGraph L).edgeFinset.card := by
  have hset : K.edgeSet ⊆ (onsTorusGraph L).edgeSet :=
    SimpleGraph.edgeSet_mono hK
  have hn := Set.ncard_le_ncard hset
    (Set.toFinite (onsTorusGraph L).edgeSet)
  simpa only [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card'] using hn



theorem torusCell_clusterEuler_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) :
    ((K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 : ℕ) : ℤ) =
      ((Nat.card (ZMod L × ZMod L) + torusCellFaceCount L K : ℕ) : ℤ) +
        torusCellDefect L K := by
  have h := torusCell_euler L K
  push_cast at h ⊢
  linarith


theorem torusCell_weight_duality_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    torusCellPrimalWeight L p q K *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        torusCellDualWeight L (dualParam p q) q K *
        q ^ torusCellDefect L K := by
  let m := (onsTorusGraph L).edgeFinset.card
  let o := K.edgeSet.ncard
  let k := Nat.card K.ConnectedComponent
  let f := torusCellFaceCount L K
  let v := Nat.card (ZMod L × ZMod L)
  let d := torusCellDefect L K
  have hom : o ≤ m := torusCell_subgraph_edgeCount_le L K hK
  have hedge := dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : ((o + k + 1 : ℕ) : ℤ) = ((v + f : ℕ) : ℤ) + d := by
    simpa only [o, k, v, f, d] using torusCell_clusterEuler_signed L K
  have hqne : q ≠ 0 := ne_of_gt hq
  have hpow : q ^ (o + k + 1) = q ^ (v + f) * q ^ d := by
    rw [← zpow_natCast, ← zpow_natCast]
    rw [heuler, zpow_add₀ hqne]
  unfold torusCellPrimalWeight torusCellDualWeight
  change edgeProductCount p m o * q ^ k * q ^ (m + 1) =
    (p / (1 - dualParam p q)) ^ m * q ^ v *
      (edgeProductCount (dualParam p q) m (m - o) * q ^ f) * q ^ d
  calc
    edgeProductCount p m o * q ^ k * q ^ (m + 1) =
        (edgeProductCount p m o * q ^ m) * (q ^ k * q) := by
      rw [pow_succ]
      ring
    _ = ((p / (1 - dualParam p q)) ^ m * q ^ o *
          edgeProductCount (dualParam p q) m (m - o)) *
          (q ^ k * q) := by
      rw [hedge]
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) *
          q ^ (o + k + 1) := by
      rw [pow_add, pow_succ]
      ring
    _ = (p / (1 - dualParam p q)) ^ m *
          edgeProductCount (dualParam p q) m (m - o) *
          (q ^ (v + f) * q ^ d) := by
      rw [hpow]
    _ = (p / (1 - dualParam p q)) ^ m * q ^ v *
          (edgeProductCount (dualParam p q) m (m - o) * q ^ f) *
          q ^ d := by
      rw [pow_add]
      ring


theorem torusCell_fkWeight_duality_signed (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.fkWeight (onsTorusGraph L) p q ω *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        FK.fkWeight (onsTorusGraph L) (dualParam p q) q
          (torusCellDualConfig L ω) *
        q ^ torusCellDefect L (FK.openSub (onsTorusGraph L) ω) := by
  rw [← torusCell_primalWeight_openSub L p q ω,
    ← torusCell_dualWeight_openSub L (dualParam p q) q ω]
  exact torusCell_weight_duality_signed L
    (FK.openSub (onsTorusGraph L) ω)
    (FK.openSub_le (onsTorusGraph L) ω) hp hp1 hq

end StatMech.BeffaraDC
