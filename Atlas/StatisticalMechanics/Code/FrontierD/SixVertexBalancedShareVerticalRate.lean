/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexWidthFreeEnergy
import Code.FrontierD.SixVertexBalancedTransferBridge

open Filter Topology

namespace StatMech.FrontierD

noncomputable section



def sixVertexBalancedTraceShare (N M : Nat) (c : Real) : Real :=
  Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M) /
    sixVertexFixedWidthPartitionSum N M c



theorem sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum
    (T : EvenTorus) (c : Real) :
    sixVertexTorusArrowPartitionSum T c =
      sixVertexFixedWidthPartitionSum T.width T.height c := by
  classical
  rw [sixVertexTorusArrowPartitionSum, sixVertexFixedWidthPartitionSum]
  calc
    (∑ omega : SixVertexArrows T, omega.weight c) =
        ∑ rows : (Fin T.height → SixVertexRow T.width) ×
            (Fin T.height → SixVertexRow T.width),
          ∏ j : Fin T.height,
            svHorizontalRowWeight T.width_pos c
              (rows.2 (SixVertexArrows.cyclicPred T.height_pos j))
              (rows.2 j) (rows.1 j) := by
      apply Fintype.sum_equiv (svTorusRowsEquiv T)
      intro omega
      exact svTorusWeight_eq_product_rowWeights T c omega
    _ = ∑ vrows : Fin T.height → SixVertexRow T.width,
          ∑ hrows : Fin T.height → SixVertexRow T.width,
            ∏ j : Fin T.height,
              svHorizontalRowWeight T.width_pos c
                (vrows (SixVertexArrows.cyclicPred T.height_pos j))
                (vrows j) (hrows j) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ vrows : Fin T.height → SixVertexRow T.width,
          ∏ j : Fin T.height,
            sixVertexTransfer T.width c
              (vrows (SixVertexArrows.cyclicPred T.height_pos j))
              (vrows j) := by
      apply Finset.sum_congr rfl
      intro vrows hvrows
      rw [← Fintype.prod_sum]
      apply Finset.prod_congr rfl
      intro j hj
      exact svHorizontalRowWeight_sum_eq_transfer T.width_pos c _ _
    _ = ∑ vrows : Fin T.height → SixVertexRow T.width,
          matrixCycleWeight T.height_pos (sixVertexTransfer T.width c)
            vrows := by
      apply Finset.sum_congr rfl
      intro vrows hvrows
      exact svPredTransferProduct_eq_matrixCycleWeight T.height_pos c vrows
    _ = matrixCompatibleCycleSum T.height_pos
          (sixVertexTransfer T.width c) := by
      rw [matrixCompatibleCycleSum]
      symm
      rw [← Finset.sum_subtype
        (Finset.univ.filter fun vrows : Fin T.height → SixVertexRow T.width =>
          ∀ i, sixVertexTransfer T.width c (vrows i)
            (vrows (finitePeriodicSucc T.height_pos i)) ≠ 0) (by simp)]
      apply Finset.sum_filter_of_ne
      intro vrows hvrows hweight i hi
      apply hweight
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    _ = Matrix.trace (sixVertexTransfer T.width c ^ T.height) := by
      exact matrixCompatibleCycleSum_eq_trace_pow T.height_pos _



theorem sixVertexRectangleBalancedShare_eq_traceShare
    (T : EvenTorus) (c : Real) :
    sixVertexRectangleBalancedPartitionSum T.width T.height c /
        sixVertexRectangleToroidalPartitionSum T.width T.height c =
      sixVertexBalancedTraceShare T.width T.height c := by
  rw [sixVertexRectangleBalancedPartitionSum_eq_halfFilledTrace,
    sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum,
    sixVertexTorusArrowPartitionSum_eq_fixedWidthPartitionSum]
  rfl





theorem sixVertexBalancedTraceShare_negLog_div_height_tendsto
    (N : Nat) (hN : Even N) {c : Real} (hc : 0 < c) :
    Tendsto (fun M : Nat =>
      -Real.log (sixVertexBalancedTraceShare N M c) / (M : Real))
      atTop
      (nhds (Real.log (sixVertexWidthTopEigenvalue N c) -
        Real.log (sixVertexLambda N 0 hN (Nat.zero_le _) c))) := by
  have hfull := sixVertexFixedWidth_log_partition_div_height_tendsto N hc
  have hbalanced := sixVertexLambda_log_trace_div_height_tendsto
    N 0 hN (Nat.zero_le _) hc
  apply (hfull.sub hbalanced).congr'
  filter_upwards [eventually_gt_atTop (0 : Nat)] with M hM
  have htrace : 0 < Matrix.trace
      (sixVertexSectorTransfer N (N / 2) c ^ M) :=
    sixVertexSector_trace_pow_pos (Nat.div_le_self N 2) hc M
  have hpartition : 0 < sixVertexFixedWidthPartitionSum N M c :=
    sixVertexFixedWidthPartitionSum_pos N M hM hc
  rw [sixVertexBalancedTraceShare,
    Real.log_div htrace.ne' hpartition.ne']
  simp only [Nat.sub_zero]
  ring

end

end StatMech.FrontierD
