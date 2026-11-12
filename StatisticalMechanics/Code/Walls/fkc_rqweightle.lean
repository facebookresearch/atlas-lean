/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































import Mathlib
import Code.FK.RandomCluster
import Code.Walls.fkc_rqnumclustersle

open scoped BigOperators
open SimpleGraph

namespace StatMech.Walls

namespace FK

open StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]



omit [DecidableEq V] in



theorem fkc_edgeProduct_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ edgeProduct G p ω := by
  unfold edgeProduct
  apply Finset.prod_nonneg
  intro e _
  split <;> linarith

omit [DecidableEq V] in



theorem fkc_edgeProduct_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : ConfigSpace (Sym2 V)) : edgeProduct G p ω ≤ 1 := by
  unfold edgeProduct
  apply Finset.prod_le_one
  · intro e _; split <;> linarith
  · intro e _; split <;> linarith







theorem fkc_qpow_numClusters_le {q : ℝ} (hq : 1 ≤ q) (ω : ConfigSpace (Sym2 V)) :
    q ^ numClusters G ω ≤ q ^ Fintype.card V :=
  pow_le_pow_right₀ hq (fkc_numClusters_le_card G ω)












theorem fkc_fkWeight_le_qpow_card {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 1 ≤ q)
    (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q ω ≤ q ^ Fintype.card V := by
  unfold fkWeight
  have hep_le : edgeProduct G p ω ≤ 1 := fkc_edgeProduct_le_one G hp hp1 ω
  have hpow_le : q ^ numClusters G ω ≤ q ^ Fintype.card V :=
    fkc_qpow_numClusters_le G hq ω
  have hq0 : (0 : ℝ) ≤ q := le_trans zero_le_one hq
  calc edgeProduct G p ω * q ^ numClusters G ω
      ≤ 1 * q ^ numClusters G ω :=
        mul_le_mul_of_nonneg_right hep_le (pow_nonneg hq0 _)
    _ = q ^ numClusters G ω := one_mul _
    _ ≤ q ^ Fintype.card V := hpow_le




theorem fkc_fkWeight_le_qpow_card' {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 1 ≤ q)
    (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q ω ≤ q ^ (Finset.univ : Finset V).card := by
  rw [Finset.card_univ]
  exact fkc_fkWeight_le_qpow_card G hp hp1 hq ω

end FK

end StatMech.Walls
