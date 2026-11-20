/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.FrontierD.SixVertexRectangleBoundary

open Finset

namespace StatMech.FrontierD

private def finLastOfPos {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (by omega)⟩

@[simp] private theorem finLastOfPos_succ {N : ℕ} (hN : 0 < N) :
    (finLastOfPos hN).succ = Fin.last N := by
  ext
  simp [finLastOfPos, Nat.sub_add_cancel hN]



def sixVertexTorusSeam (T : EvenTorus) (ω : SixVertexArrows T) :
    SixVertexToroidalBoundary T.width T.height :=
  (fun j => ω.horizontal (finLastOfPos T.width_pos, j),
    fun i => ω.vertical (i, finLastOfPos T.height_pos))



def sixVertexCutTorusArrows (T : EvenTorus) (ω : SixVertexArrows T) :
    SixVertexRectangleArrows T.width T.height where
  horizontal kj := Fin.cases
    (ω.horizontal (finLastOfPos T.width_pos, kj.2))
    (fun i => ω.horizontal (i, kj.2)) kj.1
  vertical ik := Fin.cases
    (ω.vertical (ik.1, finLastOfPos T.height_pos))
    (fun j => ω.vertical (ik.1, j)) ik.2

@[simp] theorem sixVertexCutTorusArrows_horizontal_zero
    (T : EvenTorus) (ω : SixVertexArrows T) (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (0, j) =
      ω.horizontal (finLastOfPos T.width_pos, j) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_horizontal_succ
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (i.succ, j) =
      ω.horizontal (i, j) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_horizontal_last
    (T : EvenTorus) (ω : SixVertexArrows T) (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (Fin.last T.width, j) =
      ω.horizontal (finLastOfPos T.width_pos, j) := by
  simpa only [finLastOfPos_succ] using
    sixVertexCutTorusArrows_horizontal_succ T ω
      (finLastOfPos T.width_pos) j

@[simp] theorem sixVertexCutTorusArrows_vertical_zero
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width) :
    (sixVertexCutTorusArrows T ω).vertical (i, 0) =
      ω.vertical (i, finLastOfPos T.height_pos) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_vertical_succ
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).vertical (i, j.succ) =
      ω.vertical (i, j) := by
  simp [sixVertexCutTorusArrows]

@[simp] theorem sixVertexCutTorusArrows_vertical_last
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width) :
    (sixVertexCutTorusArrows T ω).vertical (i, Fin.last T.height) =
      ω.vertical (i, finLastOfPos T.height_pos) := by
  simpa only [finLastOfPos_succ] using
    sixVertexCutTorusArrows_vertical_succ T ω i
      (finLastOfPos T.height_pos)

theorem sixVertexCutTorusArrows_boundary
    (T : EvenTorus) (ω : SixVertexArrows T) :
    sixVertexRectangleBoundary (sixVertexCutTorusArrows T ω) =
      sixVertexToroidalRectangleBoundary (sixVertexTorusSeam T ω) := by
  apply SixVertexRectangleBoundary.ext
  · funext j
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]
  · funext j
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]
  · funext i
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]
  · funext i
    simp [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
      sixVertexTorusSeam]


def sixVertexGlueTorusArrows (T : EvenTorus)
    (ω : SixVertexRectangleArrows T.width T.height) : SixVertexArrows T where
  horizontal ij := ω.horizontal (ij.1.succ, ij.2)
  vertical ij := ω.vertical (ij.1, ij.2.succ)

@[simp] theorem sixVertexGlue_cut_torus_arrows
    (T : EvenTorus) (ω : SixVertexArrows T) :
    sixVertexGlueTorusArrows T (sixVertexCutTorusArrows T ω) = ω := by
  apply SixVertexArrows.ext <;> funext v <;>
    simp [sixVertexGlueTorusArrows]


abbrev SixVertexCutRectangles (T : EvenTorus) :=
  Σ ξ : SixVertexToroidalBoundary T.width T.height,
    {ω : SixVertexRectangleArrows T.width T.height //
      sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ}



noncomputable def sixVertexTorusCutEquiv (T : EvenTorus) :
    SixVertexArrows T ≃ SixVertexCutRectangles T where
  toFun ω := ⟨sixVertexTorusSeam T ω,
    ⟨sixVertexCutTorusArrows T ω, sixVertexCutTorusArrows_boundary T ω⟩⟩
  invFun ξω := sixVertexGlueTorusArrows T ξω.2.1
  left_inv := sixVertexGlue_cut_torus_arrows T
  right_inv ξω := by
    rcases ξω with ⟨ξ, ⟨ω, hω⟩⟩
    change (⟨sixVertexTorusSeam T (sixVertexGlueTorusArrows T ω),
        ⟨sixVertexCutTorusArrows T (sixVertexGlueTorusArrows T ω),
          sixVertexCutTorusArrows_boundary T (sixVertexGlueTorusArrows T ω)⟩⟩ :
        SixVertexCutRectangles T) = ⟨ξ, ⟨ω, hω⟩⟩
    have hξ : sixVertexTorusSeam T (sixVertexGlueTorusArrows T ω) = ξ := by
      apply Prod.ext
      · funext j
        have h := congrArg (fun b => b.right j) hω
        simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
          sixVertexTorusSeam, sixVertexGlueTorusArrows] using h
      · funext i
        have h := congrArg (fun b => b.top i) hω
        simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary,
          sixVertexTorusSeam, sixVertexGlueTorusArrows] using h
    apply Sigma.ext hξ
    apply (Subtype.heq_iff_coe_eq (fun η => by
      change sixVertexRectangleBoundary η =
          sixVertexToroidalRectangleBoundary
            (sixVertexTorusSeam T (sixVertexGlueTorusArrows T ω)) ↔
        sixVertexRectangleBoundary η = sixVertexToroidalRectangleBoundary ξ
      rw [hξ])).2
    apply SixVertexRectangleArrows.ext
    · funext kj
      rcases kj with ⟨k, j⟩
      refine Fin.cases ?_ (fun i => ?_) k
      · have hl := congrArg (fun b => b.left j) hω
        have hr := congrArg (fun b => b.right j) hω
        have hlr : ω.horizontal (0, j) =
            ω.horizontal (Fin.last T.width, j) := by
          simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
            hl.trans hr.symm
        simpa [sixVertexCutTorusArrows, sixVertexGlueTorusArrows] using hlr.symm
      · simp [sixVertexCutTorusArrows, sixVertexGlueTorusArrows]
    · funext ik
      rcases ik with ⟨i, k⟩
      refine Fin.cases ?_ (fun j => ?_) k
      · have hb := congrArg (fun b => b.bottom i) hω
        have ht := congrArg (fun b => b.top i) hω
        have hbt : ω.vertical (i, 0) =
            ω.vertical (i, Fin.last T.height) := by
          simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
            hb.trans ht.symm
        simpa [sixVertexCutTorusArrows, sixVertexGlueTorusArrows] using hbt.symm
      · simp [sixVertexCutTorusArrows, sixVertexGlueTorusArrows]

private theorem cyclicPred_succ {N : ℕ} (i : Fin N) :
    SixVertexArrows.cyclicPred (Nat.succ_pos N) i.succ = i.castSucc := by
  ext
  simp only [SixVertexArrows.cyclicPred, Fin.val_succ, Fin.val_castSucc]
  rw [show i.val + 1 + (N + 1) - 1 = (N + 1) + i.val by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (i.isLt.trans (Nat.lt_succ_self N))]

private theorem cyclicPred_zero {N : ℕ} :
    SixVertexArrows.cyclicPred (Nat.succ_pos N) (0 : Fin (N + 1)) = Fin.last N := by
  ext
  simp [SixVertexArrows.cyclicPred, Nat.mod_eq_of_lt]

private theorem sixVertexCutTorusArrows_horizontal_castSucc
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (i.castSucc, j) =
      ω.horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) := by
  rcases T with ⟨W, H, hW, hH, eW, eH⟩
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hW.ne'
  have hlast : finLastOfPos hW = Fin.last N := by
    ext
    simp [finLastOfPos]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [sixVertexCutTorusArrows, cyclicPred_zero, hlast]
  · simp [sixVertexCutTorusArrows, cyclicPred_succ]

private theorem sixVertexCutTorusArrows_vertical_castSucc
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).vertical (i, j.castSucc) =
      ω.vertical (i, SixVertexArrows.cyclicPred T.height_pos j) := by
  rcases T with ⟨W, H, hW, hH, eW, eH⟩
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hH.ne'
  have hlast : finLastOfPos hH = Fin.last M := by
    ext
    simp [finLastOfPos]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [sixVertexCutTorusArrows, cyclicPred_zero, hlast]
  · simp [sixVertexCutTorusArrows, cyclicPred_succ]

private theorem sixVertexCutTorusArrows_incomingCount
    (T : EvenTorus) (ω : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexCutTorusArrows T ω).incomingCount v = ω.incomingCount v := by
  simp only [SixVertexRectangleArrows.incomingCount, SixVertexArrows.incomingCount,
    sixVertexCutTorusArrows_horizontal_castSucc,
    sixVertexCutTorusArrows_horizontal_succ,
    sixVertexCutTorusArrows_vertical_castSucc,
    sixVertexCutTorusArrows_vertical_succ]

private theorem sixVertexCutTorusArrows_isCType
    (T : EvenTorus) (ω : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexCutTorusArrows T ω).IsCType v ↔ ω.IsCType v := by
  simp only [SixVertexRectangleArrows.IsCType, SixVertexArrows.IsCType,
    sixVertexCutTorusArrows_horizontal_castSucc,
    sixVertexCutTorusArrows_horizontal_succ]

theorem sixVertexCutTorusArrows_localWeight
    (T : EvenTorus) (c : ℝ) (ω : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexCutTorusArrows T ω).localWeight c v = ω.localWeight c v := by
  classical
  rw [SixVertexRectangleArrows.localWeight, SixVertexArrows.localWeight,
    sixVertexCutTorusArrows_incomingCount]
  rw [if_congr (sixVertexCutTorusArrows_isCType T ω v) rfl rfl]

theorem sixVertexCutTorusArrows_weight
    (T : EvenTorus) (c : ℝ) (ω : SixVertexArrows T) :
    (sixVertexCutTorusArrows T ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexArrows.weight]
  apply Finset.prod_congr rfl
  intro v hv
  exact sixVertexCutTorusArrows_localWeight T c ω v


noncomputable def sixVertexTorusArrowPartitionSum (T : EvenTorus) (c : ℝ) : ℝ :=
  ∑ ω : SixVertexArrows T, ω.weight c



theorem sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum
    (T : EvenTorus) (c : ℝ) :
    sixVertexRectangleToroidalPartitionSum T.width T.height c =
      sixVertexTorusArrowPartitionSum T c := by
  classical
  rw [sixVertexRectangleToroidalPartitionSum, sixVertexTorusArrowPartitionSum]
  simp_rw [sixVertexRectangleBoundaryPartitionSum]
  calc
    ∑ ξ : SixVertexToroidalBoundary T.width T.height,
        ∑ ω : SixVertexRectangleArrows T.width T.height,
          (if sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ
          then ω.weight c else 0 : ℝ) =
      ∑ ξ : SixVertexToroidalBoundary T.width T.height,
        ∑ ω : {ω : SixVertexRectangleArrows T.width T.height //
          sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ},
          ω.1.weight c := by
        apply Finset.sum_congr rfl
        intro ξ hξ
        rw [← Finset.sum_subtype
          (Finset.univ.filter fun ω : SixVertexRectangleArrows T.width T.height =>
            sixVertexRectangleBoundary ω = sixVertexToroidalRectangleBoundary ξ) (by simp)]
        exact (Finset.sum_filter _ _).symm
    _ = ∑ ξω : SixVertexCutRectangles T, ξω.2.1.weight c := by
      rw [Fintype.sum_sigma]
    _ = ∑ ω : SixVertexArrows T, ω.weight c := by
      symm
      calc
        ∑ ω : SixVertexArrows T, ω.weight c =
            ∑ ω : SixVertexArrows T, (sixVertexCutTorusArrows T ω).weight c := by
              apply Finset.sum_congr rfl
              intro ω hω
              exact (sixVertexCutTorusArrows_weight T c ω).symm
        _ = ∑ ξω : SixVertexCutRectangles T, ξω.2.1.weight c :=
          (sixVertexTorusCutEquiv T).sum_comp
            (fun ξω : SixVertexCutRectangles T => ξω.2.1.weight c)



theorem sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum
    (T : EvenTorus) {c : ℝ} (hc : 0 ≤ c) :
    sixVertexRectangleBalancedPartitionSum T.width T.height c ≤
      sixVertexTorusArrowPartitionSum T c := by
  rw [← sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum]
  exact sixVertexRectangleBalancedPartitionSum_le_toroidal
    T.width T.height hc




theorem sixVertexTorusArrowPartitionSum_le_card_mul_maxBoundary
    (T : EvenTorus) (c : ℝ) :
    sixVertexTorusArrowPartitionSum T c ≤
      (2 : ℝ) ^ (T.width + T.height) *
        sixVertexRectangleMaxToroidalBoundaryPartitionSum
          T.width T.height c := by
  rw [← sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum]
  exact sixVertexRectangleToroidalPartitionSum_le_card_mul_maxBoundary
    T.width T.height c

end StatMech.FrontierD
