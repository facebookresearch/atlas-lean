/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib
import Code.FK.EdgeConfigZ

open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false

namespace StatMech

namespace Walls

open StatMech.FK StatMech.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]





def fc_allClosed : ecz_ClosedOff G := ⟨fun _ => false, fun _ _ => rfl⟩



theorem fc_weight_allClosed (p q : ℝ) :
    fkWeight G p q (fc_allClosed G).val
      = (1 - p) ^ G.edgeFinset.card * q ^ FK.numClusters G (fun _ => false) := by
  unfold fkWeight edgeProduct fc_allClosed
  congr 1
  rw [show (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
        = ∏ _e ∈ G.edgeFinset, (1 - p) from Finset.prod_congr rfl (fun e _ => by simp),
    Finset.prod_const]




theorem fc_weight_allClosed_ge {p q : ℝ} (hp1 : p < 1) (hq1 : 1 ≤ q) :
    (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fc_allClosed G).val := by
  rw [fc_weight_allClosed]
  have hqk : (1 : ℝ) ≤ q ^ FK.numClusters G (fun _ => false) := one_le_pow₀ hq1
  nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) G.edgeFinset.card]









theorem fc_fkZEdge_ge_allClosed {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    (1 - p) ^ G.edgeFinset.card ≤ ecz_fkZEdge G p q :=
  ecz_fkZEdge_ge_allClosed G hp hp1 hq1




theorem fc_neglogZEdge_le_edges {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    -Real.log (ecz_fkZEdge G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) :=
  ecz_neglogZEdge_le_edges G hp hp1 hq1




theorem fc_neglogZEdge_le_edges' {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    -Real.log (ecz_fkZEdge G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hge : (1 - p) ^ G.edgeFinset.card ≤ ecz_fkZEdge G p q := by
    calc (1 - p) ^ G.edgeFinset.card
        ≤ fkWeight G p q (fc_allClosed G).val := fc_weight_allClosed_ge G hp1 hq1
      _ ≤ ecz_fkZEdge G p q := by
          unfold ecz_fkZEdge
          exact Finset.single_le_sum (f := fun ω : ecz_ClosedOff G => fkWeight G p q ω.val)
            (fun ω _ => fkWeight_nonneg G hp hp1 (by linarith) ω.val) (Finset.mem_univ _)
  have hpow : (0 : ℝ) < (1 - p) ^ G.edgeFinset.card := pow_pos h1mp _
  have hZ : 0 < ecz_fkZEdge G p q := ecz_fkZEdge_pos G hp hp1 (by linarith)
  have hlog : Real.log ((1 - p) ^ G.edgeFinset.card) ≤ Real.log (ecz_fkZEdge G p q) :=
    Real.log_le_log hpow hge
  rw [Real.log_pow] at hlog
  nlinarith [hlog]







theorem fc_fkZEdge_ge_allClosed_eq {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    fc_fkZEdge_ge_allClosed G hp hp1 hq1 = ecz_fkZEdge_ge_allClosed G hp hp1 hq1 :=
  rfl


theorem fc_neglogZEdge_le_edges_eq {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    fc_neglogZEdge_le_edges G hp hp1 hq1 = ecz_neglogZEdge_le_edges G hp hp1 hq1 :=
  rfl

end Walls

end StatMech
