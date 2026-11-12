/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBalancedTransferBridge

open Finset Matrix

namespace StatMech.FrontierD



noncomputable def svTorusSectorArrowPartitionSum
    (T : EvenTorus) (n : Fin (T.width + 1)) (c : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    if sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
      omega.weight c
    else 0

theorem svTorusSectorArrowPartitionSum_eq_rowSum
    (T : EvenTorus) (n : Fin (T.width + 1)) (c : Real) :
    svTorusSectorArrowPartitionSum T n c =
      ∑ vrows : Fin T.height -> SixVertexRow T.width,
        if sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val then
          ∏ j : Fin T.height,
            sixVertexTransfer T.width c
              (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j)
        else 0 := by
  classical
  rw [svTorusSectorArrowPartitionSum]
  calc
    (∑ omega : SixVertexArrows T,
      if sixVertexUpCount
          (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
        omega.weight c else 0) =
        ∑ rows : (Fin T.height -> SixVertexRow T.width) ×
            (Fin T.height -> SixVertexRow T.width),
          if sixVertexUpCount (rows.2 (svFinLast T.height_pos)) = n.val then
            ∏ j : Fin T.height,
              svHorizontalRowWeight T.width_pos c
                (rows.2 (SixVertexArrows.cyclicPred T.height_pos j))
                (rows.2 j) (rows.1 j)
          else 0 := by
      apply Fintype.sum_equiv (svTorusRowsEquiv T)
      intro omega
      apply if_congr
      · rfl
      · exact svTorusWeight_eq_product_rowWeights T c omega
      · rfl
    _ = ∑ vrows : Fin T.height -> SixVertexRow T.width,
          ∑ hrows : Fin T.height -> SixVertexRow T.width,
            if sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val then
              ∏ j : Fin T.height,
                svHorizontalRowWeight T.width_pos c
                  (vrows (SixVertexArrows.cyclicPred T.height_pos j))
                  (vrows j) (hrows j)
            else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ vrows : Fin T.height -> SixVertexRow T.width,
        if sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val then
          ∏ j : Fin T.height,
            sixVertexTransfer T.width c
              (vrows (SixVertexArrows.cyclicPred T.height_pos j)) (vrows j)
        else 0 := by
      apply Finset.sum_congr rfl
      intro vrows hvrows
      by_cases hn :
          sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val
      · simp only [if_pos hn]
        rw [<- Fintype.prod_sum]
        apply Finset.prod_congr rfl
        intro j hj
        exact svHorizontalRowWeight_sum_eq_transfer T.width_pos c _ _
      · simp [hn]



theorem svTorusSectorArrowPartitionSum_eq_sectorTrace
    (T : EvenTorus) (n : Fin (T.width + 1)) (c : Real) :
    svTorusSectorArrowPartitionSum T n c =
      Matrix.trace (sixVertexSectorTransfer T.width n c ^ T.height) := by
  classical
  rw [svTorusSectorArrowPartitionSum_eq_rowSum]
  simp_rw [svPredTransferProduct_eq_matrixCycleWeight T.height_pos c]
  let A := sixVertexTransfer T.width c
  let f : (Fin T.height -> SixVertexRow T.width) -> Real := fun vrows =>
    if sixVertexUpCount (vrows (svFinLast T.height_pos)) = n.val then
      matrixCycleWeight T.height_pos A vrows
    else 0
  have hfiltered :
      (∑ vrows : Fin T.height -> SixVertexRow T.width, f vrows) =
        ∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
          f x.1 := by
    calc
      (∑ vrows : Fin T.height -> SixVertexRow T.width, f vrows) =
          ∑ vrows ∈ Finset.univ.filter (fun vrows =>
            ∀ i, A (vrows i) (vrows (finitePeriodicSucc T.height_pos i)) ≠ 0),
            f vrows := by
        symm
        apply Finset.sum_filter_of_ne
        intro vrows _ hf i
        have hprod : matrixCycleWeight T.height_pos A vrows ≠ 0 := by
          intro hzero
          apply hf
          unfold f
          rw [hzero]
          split_ifs <;> simp
        intro hzero
        apply hprod
        unfold matrixCycleWeight
        exact Finset.prod_eq_zero (Finset.mem_univ i) hzero
      _ = ∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
          f x.1 := by
        exact Finset.sum_subtype _ (by simp [A]) f
  change (∑ vrows : Fin T.height -> SixVertexRow T.width, f vrows) = _
  rw [hfiltered]
  have hcount (x : SixVertexPeriodicRows
      T.width T.height T.height_pos c) :
      sixVertexUpCount (x.1 (svFinLast T.height_pos)) = n.val <->
        sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val := by
    rw [sixVertexPeriodicRows_upCount_eq T.height_pos c x
      (svFinLast T.height_pos)]
  have hsector :
      (∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
          f x.1) =
        ∑ x : SixVertexPeriodicRowsInSector
          T.width T.height T.height_pos c n,
          sixVertexPeriodicRowWeight T.height_pos c x.1 := by
    unfold f
    simp_rw [hcount]
    rw [show (∑ x : SixVertexPeriodicRows T.width T.height T.height_pos c,
        if sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val then
          matrixCycleWeight T.height_pos A x.1 else 0) =
        ∑ x ∈ Finset.univ.filter (fun x :
          SixVertexPeriodicRows T.width T.height T.height_pos c =>
            sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val),
          matrixCycleWeight T.height_pos A x.1 by
            rw [Finset.sum_filter]]
    rw [Finset.sum_subtype (p := fun x :
      SixVertexPeriodicRows T.width T.height T.height_pos c =>
        sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val)
      (Finset.univ.filter fun x :
        SixVertexPeriodicRows T.width T.height T.height_pos c =>
          sixVertexUpCount (x.1 ⟨0, T.height_pos⟩) = n.val)
      (by simp)]
    rfl
  rw [hsector]
  exact svPeriodicRowsInSector_sum_eq_trace
    T.width T.height T.height_pos c n


theorem svTorusBalancedArrowPartitionSum_eq_sectorArrowPartitionSum
    (T : EvenTorus) (c : Real) :
    svTorusBalancedArrowPartitionSum T c =
      svTorusSectorArrowPartitionSum T
        ⟨T.width / 2, Nat.lt_succ_of_le (Nat.div_le_self T.width 2)⟩ c := by
  classical
  rw [svTorusBalancedArrowPartitionSum,
    svTorusSectorArrowPartitionSum]
  apply Finset.sum_congr rfl
  intro omega homega
  apply if_congr
  · exact svTorusSeam_balanced_iff_lastRow T omega
  · rfl
  · rfl



noncomputable def sixVertexTorusFixedChargePartitionSum
    (T : EvenTorus) (r : Nat) (_hr : r <= T.width / 2) (c : Real) : Real :=
  svTorusSectorArrowPartitionSum T
    ⟨T.width / 2 - r, Nat.lt_succ_of_le
      ((Nat.sub_le _ _).trans (Nat.div_le_self T.width 2))⟩ c

theorem sixVertexTorusFixedChargePartitionSum_eq_sectorTrace
    (T : EvenTorus) (r : Nat) (hr : r <= T.width / 2) (c : Real) :
    sixVertexTorusFixedChargePartitionSum T r hr c =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2 - r) c ^ T.height) := by
  exact svTorusSectorArrowPartitionSum_eq_sectorTrace T _ c

end StatMech.FrontierD
