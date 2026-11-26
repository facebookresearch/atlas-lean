/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.TorusCellDual

/-!
# Random-cluster weight duality on the torus

On the torus, the random-cluster weight of a configuration equals the dual weight of its dual
configuration up to a factor `q ^ defect`.

## i. Overview

With the signed Euler relation `E + c = V + F + defect` the primal weight at `p` equals the dual
weight at the dual parameter times `q` raised to the defect. All results are unconditional; the
defect is not assumed zero.

## ii. Key results

- `torusCell_weight_duality_signed`: weight duality with the defect factor.
- `torusCell_fkWeight_duality_signed`: the same for random-cluster weights of configurations.

## iii. Table of contents

- A. Signed weight duality

## iv. References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model is
  critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012).
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech.BeffaraDC

open StatMech.Onsager

/-! ## A. Signed weight duality -/

/-- The dual random-cluster weight of a subgraph `K` of the torus at the dual parameter. -/
noncomputable def torusCellDualWeight (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (K : SimpleGraph (ZMod L × ZMod L)) : ℝ :=
  edgeProductCount p (onsTorusGraph L).edgeFinset.card
      ((onsTorusGraph L).edgeFinset.card - K.edgeSet.ncard) *
    q ^ torusCellFaceCount L K

lemma torusCell_primalWeight_openSub (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    StatMech.BeffaraDC.torusPrimalWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q ω := by
  unfold StatMech.BeffaraDC.torusPrimalWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, dlt_edgeProduct_eq_count]
  unfold FK.numClusters
  rw [Nat.card_eq_fintype_card]

lemma torusCell_dualWeight_openSub (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    torusCellDualWeight L p q (FK.openSub (onsTorusGraph L) ω) =
      FK.fkWeight (onsTorusGraph L) p q (torusCellDualConfig L ω) := by
  unfold torusCellDualWeight FK.fkWeight
  rw [torus_openSub_edge_ncard, ← torusCell_dual_openCount,
    ← dlt_edgeProduct_eq_count, torusCell_numClusters_dualConfig]

lemma torusCell_clusterEuler_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) :
    ((K.edgeSet.ncard + Nat.card K.ConnectedComponent + 1 : ℕ) : ℤ) =
      ((Nat.card (ZMod L × ZMod L) + torusCellFaceCount L K : ℕ) : ℤ) +
        torusCellDefect L K := by
  have h := torusCell_euler L K
  push_cast at h ⊢
  linarith

lemma torusCell_weight_duality_signed (L : ℕ) [Fact (2 < L)]
    (K : SimpleGraph (ZMod L × ZMod L)) (hK : K ≤ onsTorusGraph L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    StatMech.BeffaraDC.torusPrimalWeight L p q K *
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
  have hom : o ≤ m := StatMech.BeffaraDC.torus_subgraph_edgeCount_le L K hK
  have hedge := dlt_edgeProduct_duality hp hp1 hq m o hom
  have heuler : ((o + k + 1 : ℕ) : ℤ) = ((v + f : ℕ) : ℤ) + d := by
    simpa only [o, k, v, f, d] using torusCell_clusterEuler_signed L K
  have hqne : q ≠ 0 := ne_of_gt hq
  have hpow : q ^ (o + k + 1) = q ^ (v + f) * q ^ d := by
    rw [← zpow_natCast, ← zpow_natCast]
    rw [heuler, zpow_add₀ hqne]
  unfold StatMech.BeffaraDC.torusPrimalWeight torusCellDualWeight
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

/-- The same for random-cluster weights of configurations. -/
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
