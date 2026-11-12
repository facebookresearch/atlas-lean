/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectSourceSeamBarrier
import Code.FrontierD.FKRectTorusConnected



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def fkRectUnitLeftBarrierGap (R : FKRectTorus) : R.EdgeIndex :=
  (false,
    (⟨1, lt_trans Nat.one_lt_two R.width_gt_two⟩,
      ⟨0, R.height_pos⟩))

theorem fkRectUnitLeftBarrierGap_mem (R : FKRectTorus) :
    fkRectUnitLeftBarrierGap R ∈ fkRectHorizontalCutEdges R := by
  simp [fkRectUnitLeftBarrierGap, mem_fkRectHorizontalCutEdges_iff]


def fkRectUnitLeftBarrierConfiguration (R : FKRectTorus) : R.Configuration :=
  fkRectConfigurationOfEdges R
    ((fkRectHorizontalCutEdges R).erase (fkRectUnitLeftBarrierGap R))

theorem fkRectUnitLeftBarrierConfiguration_seam
    (R : FKRectTorus) :
    fkRectUnitLeftBarrierConfiguration R ∈
      fkRectAllButOneOpenSeamEvent R (fkRectUnitLeftBarrierGap R) := by
  intro a ha
  by_cases hag : a = fkRectUnitLeftBarrierGap R
  · subst a
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectAllButOneOpenConfiguration, fkRectConfigurationOfEdges]
  · have hopen : a ∈ (fkRectHorizontalCutEdges R).erase
        (fkRectUnitLeftBarrierGap R) :=
      Finset.mem_erase.mpr ⟨hag, ha⟩
    simp [fkRectUnitLeftBarrierConfiguration,
      fkRectAllButOneOpenConfiguration, hopen, hag]




theorem fkRectUnitLeftBarrier_inducedAdj_column_eq
    (R : FKRectTorus)
    {u v : fkRectLeftStrip R 1}
    (huv : ((fkRectOpenGraph R (fkRectUnitLeftBarrierConfiguration R)).induce
      (fkRectLeftStrip R 1)).Adj u v) :
    u.1.1.val = v.1.1.val := by
  rcases huv with ⟨⟨b, x, y⟩, hopen, hedge⟩
  have haopen : (b, (x, y)) ∈
      (fkRectHorizontalCutEdges R).erase (fkRectUnitLeftBarrierGap R) :=
    (fkRectConfigurationOfEdges_apply R _ _).mp hopen
  have hne : (b, (x, y)) ≠ fkRectUnitLeftBarrierGap R :=
    (Finset.mem_erase.mp haopen).1
  have hcut : (b, (x, y)) ∈ fkRectHorizontalCutEdges R :=
    (Finset.mem_erase.mp haopen).2
  rw [mem_fkRectHorizontalCutEdges_iff] at hcut
  cases b
  · have heven : Even y.val := by
      rw [hcut]
      norm_num
    simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
      heven, if_true] at hedge
    rcases Sym2.eq_iff.mp hedge with horient | horient
    · have hxu := congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hpv := congrArg (fun z : R.Vertex => z.1.val) horient.2
      change x.val = u.1.1.val at hxu
      change (SixVertexArrows.cyclicPred R.width_pos x).val =
        v.1.1.val at hpv
      have hxle : x.val ≤ 1 := hxu ▸ u.2
      have hpredle :
          (SixVertexArrows.cyclicPred R.width_pos x).val ≤ 1 := hpv ▸ v.2
      rw [fkRectCyclicPred_val] at hpredle
      by_cases hx0 : x.val = 0
      · simp only [hx0, if_true] at hpredle
        have hw := R.width_gt_two
        omega
      · have hx1 : x.val = 1 := by omega
        apply (hne ?_).elim
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · apply Fin.ext
            exact hx1
          · apply Fin.ext
            exact hcut
    · have hxv := congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hpu := congrArg (fun z : R.Vertex => z.1.val) horient.2
      change x.val = v.1.1.val at hxv
      change (SixVertexArrows.cyclicPred R.width_pos x).val =
        u.1.1.val at hpu
      have hxle : x.val ≤ 1 := hxv ▸ v.2
      have hpredle :
          (SixVertexArrows.cyclicPred R.width_pos x).val ≤ 1 := hpu ▸ u.2
      rw [fkRectCyclicPred_val] at hpredle
      by_cases hx0 : x.val = 0
      · simp only [hx0, if_true] at hpredle
        have hw := R.width_gt_two
        omega
      · have hx1 : x.val = 1 := by omega
        apply (hne ?_).elim
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · apply Fin.ext
            exact hx1
          · apply Fin.ext
            exact hcut
  · simp only [fkRectTorusIndexedEdge, if_true] at hedge
    rcases Sym2.eq_iff.mp hedge with horient | horient
    · have hxu : x.val = u.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hxv : x.val = v.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.2
      exact hxu.symm.trans hxv
    · have hxv : x.val = v.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hxu : x.val = u.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.2
      exact hxu.symm.trans hxv



theorem fkRectUnitLeftBarrier_inducedAdj_zero_iff
    (R : FKRectTorus) (right : Nat) (hright : right + 1 < R.width)
    {u v : fkRectLeftStrip R right}
    (huv : ((fkRectOpenGraph R (fkRectUnitLeftBarrierConfiguration R)).induce
      (fkRectLeftStrip R right)).Adj u v) :
    u.1.1.val = 0 ↔ v.1.1.val = 0 := by
  rcases huv with ⟨⟨b, x, y⟩, hopen, hedge⟩
  have haopen : (b, (x, y)) ∈
      (fkRectHorizontalCutEdges R).erase (fkRectUnitLeftBarrierGap R) :=
    (fkRectConfigurationOfEdges_apply R _ _).mp hopen
  have hne : (b, (x, y)) ≠ fkRectUnitLeftBarrierGap R :=
    (Finset.mem_erase.mp haopen).1
  have hcut : (b, (x, y)) ∈ fkRectHorizontalCutEdges R :=
    (Finset.mem_erase.mp haopen).2
  rw [mem_fkRectHorizontalCutEdges_iff] at hcut
  cases b
  · have heven : Even y.val := by rw [hcut]; norm_num
    simp only [fkRectTorusIndexedEdge, Bool.false_eq_true, if_false,
      heven, if_true] at hedge
    rcases Sym2.eq_iff.mp hedge with horient | horient
    · have hxu := congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hpv := congrArg (fun z : R.Vertex => z.1.val) horient.2
      change x.val = u.1.1.val at hxu
      change (SixVertexArrows.cyclicPred R.width_pos x).val =
        v.1.1.val at hpv
      have hpredle :
          (SixVertexArrows.cyclicPred R.width_pos x).val ≤ right := hpv ▸ v.2
      have hx0 : x.val ≠ 0 := by
        intro hx
        rw [fkRectCyclicPred_val] at hpredle
        simp only [hx, if_true] at hpredle
        omega
      have hx1 : x.val ≠ 1 := by
        intro hx
        apply hne
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · apply Fin.ext
            exact hx
          · apply Fin.ext
            exact hcut
      have hpred0 :
          (SixVertexArrows.cyclicPred R.width_pos x).val ≠ 0 := by
        rw [fkRectCyclicPred_val]
        simp only [hx0, if_false]
        omega
      have hu0 : u.1.1.val ≠ 0 := by rw [← hxu]; exact hx0
      have hv0 : v.1.1.val ≠ 0 := by rw [← hpv]; exact hpred0
      exact iff_of_false hu0 hv0
    · have hxv := congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hpu := congrArg (fun z : R.Vertex => z.1.val) horient.2
      change x.val = v.1.1.val at hxv
      change (SixVertexArrows.cyclicPred R.width_pos x).val =
        u.1.1.val at hpu
      have hpredle :
          (SixVertexArrows.cyclicPred R.width_pos x).val ≤ right := hpu ▸ u.2
      have hx0 : x.val ≠ 0 := by
        intro hx
        rw [fkRectCyclicPred_val] at hpredle
        simp only [hx, if_true] at hpredle
        omega
      have hx1 : x.val ≠ 1 := by
        intro hx
        apply hne
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · apply Fin.ext
            exact hx
          · apply Fin.ext
            exact hcut
      have hpred0 :
          (SixVertexArrows.cyclicPred R.width_pos x).val ≠ 0 := by
        rw [fkRectCyclicPred_val]
        simp only [hx0, if_false]
        omega
      have hv0 : v.1.1.val ≠ 0 := by rw [← hxv]; exact hx0
      have hu0 : u.1.1.val ≠ 0 := by rw [← hpu]; exact hpred0
      exact iff_of_false hu0 hv0
  · simp only [fkRectTorusIndexedEdge, if_true] at hedge
    rcases Sym2.eq_iff.mp hedge with horient | horient
    · have hxu : x.val = u.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hxv : x.val = v.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.2
      rw [← hxu, ← hxv]
    · have hxv : x.val = v.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.1
      have hxu : x.val = u.1.1.val := by
        simpa using congrArg (fun z : R.Vertex => z.1.val) horient.2
      rw [← hxu, ← hxv]


theorem fkRectUnitLeftBarrierConfiguration_noCrossing
    (R : FKRectTorus) :
    fkRectUnitLeftBarrierConfiguration R ∈
      fkRectNoLeftStripCrossingEvent R 1 := by
  intro hcross
  rcases hcross with ⟨u, hu, v, hv, hreach⟩
  obtain ⟨w⟩ := hreach
  have hcol : u.1.1.val = v.1.1.val := by
    clear hu hv
    induction w with
    | nil => rfl
    | @cons a b c hab w ih =>
        exact (fkRectUnitLeftBarrier_inducedAdj_column_eq R hab).trans ih
  change u.1.1.val = 0 at hu
  change v.1.1.val = 1 at hv
  omega



theorem fkRectUnitLeftBarrierConfiguration_noCrossing_of_one_le
    (R : FKRectTorus) (right : Nat) (hone : 1 <= right)
    (hright : right + 1 < R.width) :
    fkRectUnitLeftBarrierConfiguration R ∈
      fkRectNoLeftStripCrossingEvent R right := by
  intro hcross
  rcases hcross with ⟨u, hu, v, hv, hreach⟩
  obtain ⟨w⟩ := hreach
  have hzero : u.1.1.val = 0 ↔ v.1.1.val = 0 := by
    clear hu hv
    induction w with
    | nil => rfl
    | @cons a b c hab w ih =>
        exact (fkRectUnitLeftBarrier_inducedAdj_zero_iff
          R right hright hab).trans ih
  change u.1.1.val = 0 at hu
  change v.1.1.val = right at hv
  have := hzero.mp hu
  omega

theorem fkRectUnitLeftBarrierConfiguration_mem_source
    (R : FKRectTorus) :
    fkRectUnitLeftBarrierConfiguration R ∈
      fkRectSourceLeftBarrier R 1 (fkRectUnitLeftBarrierGap R) :=
  ⟨fkRectUnitLeftBarrierConfiguration_noCrossing R,
    fkRectUnitLeftBarrierConfiguration_seam R⟩

theorem fkRectUnitLeftBarrierConfiguration_mem_source_of_one_le
    (R : FKRectTorus) (right : Nat) (hone : 1 <= right)
    (hright : right + 1 < R.width) :
    fkRectUnitLeftBarrierConfiguration R ∈
      fkRectSourceLeftBarrier R right (fkRectUnitLeftBarrierGap R) :=
  ⟨fkRectUnitLeftBarrierConfiguration_noCrossing_of_one_le
      R right hone hright,
    fkRectUnitLeftBarrierConfiguration_seam R⟩

end

end StatMech.FrontierD
