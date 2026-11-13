/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






































import Mathlib
import Code.FK.RandomCluster
import Code.FK.EdgeConfigZ
import Code.FK.SecantClose

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.openClassical false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option maxHeartbeats 1000000

namespace StatMech.Walls

open StatMech StatMech.FK StatMech.Lattice








section WeightBound
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]





theorem fkc_fkWeight_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q)
    (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p q ω ≤ q ^ Fintype.card V := by
  unfold fkWeight
  have hep : edgeProduct G p ω ≤ 1 := by
    unfold edgeProduct
    apply Finset.prod_le_one
    · intro e _; split <;> [exact hp.le; linarith]
    · intro e _; split <;> [exact hp1.le; linarith]
  have hqk : q ^ numClusters G ω ≤ q ^ Fintype.card V :=
    pow_le_pow_right₀ hq1 (ecz_numClusters_le G ω)
  calc edgeProduct G p ω * q ^ numClusters G ω
      ≤ 1 * q ^ Fintype.card V := by
        exact mul_le_mul hep hqk (by positivity) (by positivity)
    _ = q ^ Fintype.card V := by ring





theorem fkc_fkZEdge_le {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    ecz_fkZEdge G p q ≤ (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
  unfold ecz_fkZEdge
  calc ∑ ω : ecz_ClosedOff G, fkWeight G p q ω.val
      ≤ ∑ ω : ecz_ClosedOff G, q ^ Fintype.card V :=
        Finset.sum_le_sum (fun ω _ => fkc_fkWeight_le G hp hp1 hq1 ω.val)
    _ = (Fintype.card (ecz_ClosedOff G) : ℝ) * q ^ Fintype.card V := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2 : ℝ) ^ G.edgeFinset.card * q ^ Fintype.card V := by
        rw [ecz_closedOff_card G]; push_cast; ring

end WeightBound






section FreeEnergy



noncomputable def fkc_edgeFreeEnergy (d : ℕ) (s q : ℝ) (n : ℕ) : ℝ :=
  Real.log (ecz_fkZEdge (boxGraph d n) (fsc_logistic s) q) / ((boxGraph d n).edgeFinset.card : ℝ)
    + Real.log (1 + Real.exp s)



theorem fkc_edgeFreeEnergy_eq_ecz (d : ℕ) (s : ℝ) (n : ℕ) :
    fkc_edgeFreeEnergy d s 2 n = ecz_edgeFreeEnergy d s n := by
  unfold fkc_edgeFreeEnergy ecz_edgeFreeEnergy ecz_u
  rw [neg_div, neg_neg]















theorem fkc_rq_bdd (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) (s q : ℝ) (hq1 : 1 ≤ q) :
    fkc_edgeFreeEnergy d s q n ≤ (Real.log 2 + 2 * Real.log q) + Real.log (1 + Real.exp s) := by
  unfold fkc_edgeFreeEnergy
  set E := (boxGraph d n).edgeFinset.card with hEdef
  set Vc := Fintype.card (boxVerts d n) with hVdef
  set p := fsc_logistic s with hpdef
  have hp0 : (0:ℝ) < p := fsc_logistic_pos s
  have hp1 : p < 1 := fsc_logistic_lt_one s
  have hE : 0 < E := ecz_box_edge_pos d hd hn
  have hEr : (0:ℝ) < (E:ℝ) := by exact_mod_cast hE
  have hZpos : 0 < ecz_fkZEdge (boxGraph d n) p q :=
    ecz_fkZEdge_pos _ hp0 hp1 (by linarith)
  have hub : ecz_fkZEdge (boxGraph d n) p q ≤ (2:ℝ)^E * q^Vc :=
    fkc_fkZEdge_le _ hp0 hp1 hq1
  have hlogq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog : Real.log (ecz_fkZEdge (boxGraph d n) p q) ≤ (E:ℝ) * Real.log 2 + (Vc:ℝ) * Real.log q := by
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ Real.log ((2:ℝ)^E * q^Vc) := Real.log_le_log hZpos hub
      _ = (E:ℝ) * Real.log 2 + (Vc:ℝ) * Real.log q := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hVle : (Vc:ℝ) ≤ 2 * E := by exact_mod_cast ecz_boxVerts_le_edges d n hd hn
  have hkey : Real.log (ecz_fkZEdge (boxGraph d n) p q) / (E:ℝ)
      ≤ Real.log 2 + 2 * Real.log q := by
    rw [div_le_iff₀ hEr]
    calc Real.log (ecz_fkZEdge (boxGraph d n) p q)
        ≤ (E:ℝ) * Real.log 2 + (Vc:ℝ) * Real.log q := hlog
      _ ≤ (E:ℝ) * Real.log 2 + (2 * E) * Real.log q := by
          have : (Vc:ℝ) * Real.log q ≤ (2 * E) * Real.log q :=
            mul_le_mul_of_nonneg_right hVle hlogq
          linarith
      _ = (Real.log 2 + 2 * Real.log q) * E := by ring
  linarith

end FreeEnergy

end StatMech.Walls
