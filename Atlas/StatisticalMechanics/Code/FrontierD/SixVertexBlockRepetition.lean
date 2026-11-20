/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierD.SixVertexBalancedTransferBridge

open Finset

namespace StatMech.FrontierD

@[simp] private theorem finProdFinEquiv_divNat {m n : ℕ}
    (x : Fin m) (i : Fin n) :
    (finProdFinEquiv (x, i)).divNat = x := by
  have h := (finProdFinEquiv (m := m) (n := n)).symm_apply_apply (x, i)
  simpa only [finProdFinEquiv_symm_apply] using congrArg Prod.fst h

@[simp] private theorem finProdFinEquiv_modNat {m n : ℕ}
    (x : Fin m) (i : Fin n) :
    (finProdFinEquiv (x, i)).modNat = i := by
  have h := (finProdFinEquiv (m := m) (n := n)).symm_apply_apply (x, i)
  simpa only [finProdFinEquiv_symm_apply] using congrArg Prod.snd h



abbrev SixVertexRectangleBlockCopies {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) (a b : ℕ) :=
  Fin (a + 1) × Fin (b + 1) →
    SixVertexRectangleBoundaryFiber (sixVertexToroidalRectangleBoundary ξ)




def sixVertexRectangleTileBlocks {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b) :
    SixVertexRectangleArrows ((a + 1) * N) ((b + 1) * M) where
  horizontal kj :=
    let byj := finProdFinEquiv.symm kj.2
    Fin.lastCases
      ((ω (Fin.last a, byj.1)).1.horizontal (Fin.last N, byj.2))
      (fun gi =>
        let bxi := finProdFinEquiv.symm gi
        (ω (bxi.1, byj.1)).1.horizontal (bxi.2.castSucc, byj.2))
      kj.1
  vertical ik :=
    let bxi := finProdFinEquiv.symm ik.1
    Fin.lastCases
      ((ω (bxi.1, Fin.last b)).1.vertical (bxi.2, Fin.last M))
      (fun gj =>
        let byj := finProdFinEquiv.symm gj
        (ω (bxi.1, byj.1)).1.vertical (bxi.2, byj.2.castSucc))
      ik.2

private theorem block_boundary_left_right {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (0, j) =
      (ω (x, y)).1.horizontal (Fin.last N, j) := by
  have hl := congrArg (fun η => η.left j) (ω (x, y)).2
  have hr := congrArg (fun η => η.right j) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    hl.trans hr.symm

private theorem block_boundary_bottom_top {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, 0) =
      (ω (x, y)).1.vertical (i, Fin.last M) := by
  have hb := congrArg (fun η => η.bottom i) (ω (x, y)).2
  have ht := congrArg (fun η => η.top i) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    hb.trans ht.symm

private theorem block_boundary_right_left {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x x' : Fin (a + 1)) (y y' : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (Fin.last N, j) =
      (ω (x', y')).1.horizontal (0, j) := by
  have hr := congrArg (fun η => η.right j) (ω (x, y)).2
  have hl := congrArg (fun η => η.left j) (ω (x', y')).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    hr.trans hl.symm

private theorem block_boundary_top_bottom {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x x' : Fin (a + 1)) (y y' : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, Fin.last M) =
      (ω (x', y')).1.vertical (i, 0) := by
  have ht := congrArg (fun η => η.top i) (ω (x, y)).2
  have hb := congrArg (fun η => η.bottom i) (ω (x', y')).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    ht.trans hb.symm

@[simp] theorem sixVertexRectangleTileBlocks_horizontal_castSucc
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleTileBlocks ω).horizontal
        ((finProdFinEquiv (x, i)).castSucc, finProdFinEquiv (y, j)) =
      (ω (x, y)).1.horizontal (i.castSucc, j) := by
  simp [sixVertexRectangleTileBlocks]

@[simp] theorem sixVertexRectangleTileBlocks_vertical_castSucc
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleTileBlocks ω).vertical
        (finProdFinEquiv (x, i), (finProdFinEquiv (y, j)).castSucc) =
      (ω (x, y)).1.vertical (i, j.castSucc) := by
  simp [sixVertexRectangleTileBlocks]

@[simp] theorem sixVertexRectangleTileBlocks_horizontal_succ
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1))
    (i : Fin (N + 1)) (j : Fin M) :
    (sixVertexRectangleTileBlocks ω).horizontal
        ((finProdFinEquiv (x, i)).succ, finProdFinEquiv (y, j)) =
      (ω (x, y)).1.horizontal (i.succ, j) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun x => ?_) x
    · have hlast :
          (finProdFinEquiv (Fin.last a, Fin.last N)).succ =
            Fin.last ((a + 1) * (N + 1)) := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hlast]
      simp [sixVertexRectangleTileBlocks]
    · have hnext :
          (finProdFinEquiv (x.castSucc, Fin.last N)).succ =
            (finProdFinEquiv (x.succ, (0 : Fin (N + 1)))).castSucc := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hnext, sixVertexRectangleTileBlocks_horizontal_castSucc]
      exact (block_boundary_right_left ω x.castSucc x.succ y y j).symm
  · have hnext :
        (finProdFinEquiv (x, i.castSucc)).succ =
          (finProdFinEquiv (x, i.succ)).castSucc := by
      ext
      simp [finProdFinEquiv]
      ring
  
    rw [hnext, sixVertexRectangleTileBlocks_horizontal_castSucc]
    rfl

@[simp] theorem sixVertexRectangleTileBlocks_vertical_succ
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary N (M + 1)}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1))
    (i : Fin N) (j : Fin (M + 1)) :
    (sixVertexRectangleTileBlocks ω).vertical
        (finProdFinEquiv (x, i), (finProdFinEquiv (y, j)).succ) =
      (ω (x, y)).1.vertical (i, j.succ) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · refine Fin.lastCases ?_ (fun y => ?_) y
    · have hlast :
          (finProdFinEquiv (Fin.last b, Fin.last M)).succ =
            Fin.last ((b + 1) * (M + 1)) := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hlast]
      simp [sixVertexRectangleTileBlocks]
    · have hnext :
          (finProdFinEquiv (y.castSucc, Fin.last M)).succ =
            (finProdFinEquiv (y.succ, (0 : Fin (M + 1)))).castSucc := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hnext, sixVertexRectangleTileBlocks_vertical_castSucc]
      exact (block_boundary_top_bottom ω x x y.castSucc y.succ i).symm
  · have hnext :
        (finProdFinEquiv (y, j.castSucc)).succ =
          (finProdFinEquiv (y, j.succ)).castSucc := by
      ext
      simp [finProdFinEquiv]
      ring
    rw [hnext, sixVertexRectangleTileBlocks_vertical_castSucc]
    rfl



theorem sixVertexRectangleTileBlocks_localWeight
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (c : ℝ) (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1))
    (i : Fin (N + 1)) (j : Fin (M + 1)) :
    (sixVertexRectangleTileBlocks ω).localWeight c
        (finProdFinEquiv (x, i), finProdFinEquiv (y, j)) =
      (ω (x, y)).1.localWeight c (i, j) := by
  simp [SixVertexRectangleArrows.localWeight,
    SixVertexRectangleArrows.incomingCount,
    SixVertexRectangleArrows.IsCType]



theorem sixVertexRectangleTileBlocks_weight
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (c : ℝ) (ω : SixVertexRectangleBlockCopies ξ a b) :
    (sixVertexRectangleTileBlocks ω).weight c =
      ∏ xy : Fin (a + 1) × Fin (b + 1), (ω xy).1.weight c := by
  rw [SixVertexRectangleArrows.weight]
  let e := Equiv.prodCongr
    (finProdFinEquiv (m := a + 1) (n := N + 1))
    (finProdFinEquiv (m := b + 1) (n := M + 1))
  calc
    (∏ v, (sixVertexRectangleTileBlocks ω).localWeight c v) =
        ∏ p : (Fin (a + 1) × Fin (N + 1)) ×
            (Fin (b + 1) × Fin (M + 1)),
          (sixVertexRectangleTileBlocks ω).localWeight c (e p) := by
      exact (Fintype.prod_equiv e _ _ fun _ => rfl).symm
    _ = ∏ p : (Fin (a + 1) × Fin (N + 1)) ×
            (Fin (b + 1) × Fin (M + 1)),
          (ω (p.1.1, p.2.1)).1.localWeight c (p.1.2, p.2.2) := by
      apply Fintype.prod_congr
      intro p
      exact sixVertexRectangleTileBlocks_localWeight c ω
        p.1.1 p.2.1 p.1.2 p.2.2
    _ = ∏ xy : Fin (a + 1) × Fin (b + 1), (ω xy).1.weight c := by
      simp only [Fintype.prod_prod_type, SixVertexRectangleArrows.weight]
      apply Finset.prod_congr rfl
      intro x hx
      rw [Finset.prod_comm]


def sixVertexRepeatToroidalBoundary {N M a b : ℕ}
    (ξ : SixVertexToroidalBoundary N M) :
    SixVertexToroidalBoundary ((a + 1) * N) ((b + 1) * M) :=
  (fun j => ξ.1 (finProdFinEquiv.symm j).2,
    fun i => ξ.2 (finProdFinEquiv.symm i).2)

private theorem block_boundary_left_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (0, j) = ξ.1 j := by
  have h := congrArg (fun η => η.left j) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h

private theorem block_boundary_right_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (Fin.last N, j) = ξ.1 j := by
  have h := congrArg (fun η => η.right j) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h

private theorem block_boundary_bottom_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, 0) = ξ.2 i := by
  have h := congrArg (fun η => η.bottom i) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h

private theorem block_boundary_top_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, Fin.last M) = ξ.2 i := by
  have h := congrArg (fun η => η.top i) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h


theorem sixVertexRectangleTileBlocks_boundary
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (ω : SixVertexRectangleBlockCopies ξ a b) :
    sixVertexRectangleBoundary (sixVertexRectangleTileBlocks ω) =
      sixVertexToroidalRectangleBoundary
        (sixVertexRepeatToroidalBoundary ξ) := by
  apply SixVertexRectangleBoundary.ext
  · funext gj
    obtain ⟨⟨y, j⟩, rfl⟩ :=
      (finProdFinEquiv (m := b + 1) (n := M + 1)).surjective gj
    have hzero : (0 : Fin ((a + 1) * (N + 1) + 1)) =
        (finProdFinEquiv
          ((0 : Fin (a + 1)), (0 : Fin (N + 1)))).castSucc := by
      ext
      simp [finProdFinEquiv]
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    rw [hzero, sixVertexRectangleTileBlocks_horizontal_castSucc]
    simpa [sixVertexRepeatToroidalBoundary] using
      block_boundary_left_value ω 0 y j
  · funext gj
    obtain ⟨⟨y, j⟩, rfl⟩ :=
      (finProdFinEquiv (m := b + 1) (n := M + 1)).surjective gj
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    simpa [sixVertexRectangleTileBlocks, sixVertexRepeatToroidalBoundary] using
      block_boundary_right_value ω (Fin.last a) y j
  · funext gi
    obtain ⟨⟨x, i⟩, rfl⟩ :=
      (finProdFinEquiv (m := a + 1) (n := N + 1)).surjective gi
    have hzero : (0 : Fin ((b + 1) * (M + 1) + 1)) =
        (finProdFinEquiv
          ((0 : Fin (b + 1)), (0 : Fin (M + 1)))).castSucc := by
      ext
      simp [finProdFinEquiv]
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    rw [hzero, sixVertexRectangleTileBlocks_vertical_castSucc]
    simpa [sixVertexRepeatToroidalBoundary] using
      block_boundary_bottom_value ω x 0 i
  · funext gi
    obtain ⟨⟨x, i⟩, rfl⟩ :=
      (finProdFinEquiv (m := a + 1) (n := N + 1)).surjective gi
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    simpa [sixVertexRectangleTileBlocks, sixVertexRepeatToroidalBoundary] using
      block_boundary_top_value ω x (Fin.last b) i


theorem sixVertexRepeatToroidalBoundary_balanced
    {N M a b : ℕ} (hN : Even N)
    (ξ : SixVertexToroidalBoundary N M) (hξ : ξ.Balanced) :
    (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ).Balanced := by
  unfold SixVertexToroidalBoundary.Balanced at hξ ⊢
  rw [Finset.card_filter]
  calc
    (∑ i : Fin ((a + 1) * N),
        if (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ).2 i = true
        then 1 else 0) =
        ∑ xi : Fin (a + 1) × Fin N,
          if ξ.2 xi.2 = true then 1 else 0 := by
      apply Fintype.sum_equiv
        (finProdFinEquiv (m := a + 1) (n := N)).symm
      intro i
      simp [sixVertexRepeatToroidalBoundary]
    _ = (a + 1) * #{i | ξ.2 i} := by
      rw [Fintype.sum_prod_type, Finset.card_filter]
      simp
    _ = ((a + 1) * N) / 2 := by
      rw [hξ]
      rcases hN with ⟨k, rfl⟩
      have hhalf : (k + k) / 2 = k := by omega
      rw [hhalf]
      have hmul : (a + 1) * (k + k) =
          (a + 1) * k + (a + 1) * k := by ring
      rw [hmul]
      omega



theorem sixVertexRectangleTileBlocks_injective
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
    Function.Injective
      (sixVertexRectangleTileBlocks (ξ := ξ) :
        SixVertexRectangleBlockCopies ξ a b →
          SixVertexRectangleArrows ((a + 1) * (N + 1))
            ((b + 1) * (M + 1))) := by
  intro ω η htile
  funext xy
  apply Subtype.ext
  apply SixVertexRectangleArrows.ext
  · funext kj
    rcases kj with ⟨k, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) k
    · exact (block_boundary_right_value ω xy.1 xy.2 j).trans
        (block_boundary_right_value η xy.1 xy.2 j).symm
    · have h := congrArg (fun ρ => ρ.horizontal
          ((finProdFinEquiv (xy.1, i)).castSucc,
            finProdFinEquiv (xy.2, j))) htile
      simpa using h
  · funext ik
    rcases ik with ⟨i, k⟩
    refine Fin.lastCases ?_ (fun j => ?_) k
    · exact (block_boundary_top_value ω xy.1 xy.2 i).trans
        (block_boundary_top_value η xy.1 xy.2 i).symm
    · have h := congrArg (fun ρ => ρ.vertical
          (finProdFinEquiv (xy.1, i),
            (finProdFinEquiv (xy.2, j)).castSucc)) htile
      simpa using h


def sixVertexRectangleTileBlocksBoundaryFiber
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
    SixVertexRectangleBlockCopies ξ a b →
      SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary
          (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ)) :=
  fun ω => ⟨sixVertexRectangleTileBlocks ω,
    sixVertexRectangleTileBlocks_boundary ω⟩

theorem sixVertexRectangleTileBlocksBoundaryFiber_injective
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
    Function.Injective
      (sixVertexRectangleTileBlocksBoundaryFiber (ξ := ξ) (a := a) (b := b)) := by
  intro ω η h
  apply sixVertexRectangleTileBlocks_injective
  exact congrArg Subtype.val h




theorem sixVertexRectangleBoundaryPartitionSum_pow_blockCount_le_repeated
    {N M a b : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (ξ : SixVertexToroidalBoundary (N + 1) (M + 1)) :
    sixVertexRectangleBoundaryPartitionSum (N + 1) (M + 1) c
        (sixVertexToroidalRectangleBoundary ξ) ^ ((a + 1) * (b + 1)) ≤
      sixVertexRectangleBoundaryPartitionSum
        ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c
        (sixVertexToroidalRectangleBoundary
          (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ)) := by
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum,
    Fintype.sum_pow]
  rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  let e := finProdFinEquiv (m := a + 1) (n := b + 1)
  let reindex := Equiv.arrowCongr e
    (Equiv.refl (SixVertexRectangleBoundaryFiber
      (sixVertexToroidalRectangleBoundary ξ)))
  let tile := sixVertexRectangleTileBlocksBoundaryFiber
    (ξ := ξ) (a := a) (b := b)
  calc
    (∑ p : Fin ((a + 1) * (b + 1)) →
          SixVertexRectangleBoundaryFiber
            (sixVertexToroidalRectangleBoundary ξ),
        ∏ i, (p i).1.weight c) =
        ∑ ω : SixVertexRectangleBlockCopies ξ a b,
          ∏ xy, (ω xy).1.weight c := by
      symm
      apply Fintype.sum_equiv reindex
      intro ω
      apply Fintype.prod_equiv e
      intro xy
      simp [reindex]
    _ = ∑ ω : SixVertexRectangleBlockCopies ξ a b,
          (tile ω).1.weight c := by
      apply Fintype.sum_congr
      intro ω
      exact (sixVertexRectangleTileBlocks_weight c ω).symm
    _ = ∑ η ∈ Finset.univ.image tile, η.1.weight c := by
      rw [Finset.sum_image
        (sixVertexRectangleTileBlocksBoundaryFiber_injective
          (ξ := ξ) (a := a) (b := b)).injOn]
    _ ≤ ∑ η : SixVertexRectangleBoundaryFiber
          (sixVertexToroidalRectangleBoundary
            (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ)),
              η.1.weight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro η hη hnot
        exact SixVertexRectangleArrows.weight_nonneg hc η.1



noncomputable def sixVertexRectangleMaxBalancedBoundaryContribution
    (N M : ℕ) (c : ℝ) : ℝ :=
  (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
    if ξ.Balanced then
      sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ)
    else 0).max' (Finset.image_nonempty.mpr Finset.univ_nonempty)

theorem sixVertexRectangleMaxBalancedBoundaryContribution_exists
    (N M : ℕ) (c : ℝ) :
    ∃ ξ : SixVertexToroidalBoundary N M,
      (if ξ.Balanced then
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)
      else 0) =
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
  obtain ⟨ξ, hξ, hmax⟩ := Finset.mem_image.mp
    (Finset.max'_mem
      (Finset.univ.image fun ξ : SixVertexToroidalBoundary N M =>
        if ξ.Balanced then
          sixVertexRectangleBoundaryPartitionSum N M c
            (sixVertexToroidalRectangleBoundary ξ)
        else 0) _)
  exact ⟨ξ, hmax⟩

theorem sixVertexRectangleMaxBalancedBoundaryContribution_nonneg
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
  obtain ⟨ξ, hξ⟩ :=
    sixVertexRectangleMaxBalancedBoundaryContribution_exists N M c
  rw [← hξ]
  split_ifs
  · exact sixVertexRectangleBoundaryPartitionSum_nonneg N M hc _
  · exact le_rfl



theorem sixVertexRectangleBalancedPartitionSum_le_card_mul_maxBalanced
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleBalancedPartitionSum N M c ≤
      (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
  rw [sixVertexRectangleBalancedPartitionSum]
  let f : SixVertexToroidalBoundary N M → ℝ := fun ξ =>
    if ξ.Balanced then
      sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary ξ)
    else 0
  have hle (ξ : SixVertexToroidalBoundary N M) :
      f ξ ≤ sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
    unfold sixVertexRectangleMaxBalancedBoundaryContribution
    apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨ξ, Finset.mem_univ ξ, rfl⟩
  calc
    (∑ ξ : SixVertexToroidalBoundary N M,
      if ξ.Balanced then
        sixVertexRectangleBoundaryPartitionSum N M c
          (sixVertexToroidalRectangleBoundary ξ)
      else 0) = ∑ ξ, f ξ := rfl
    _ ≤ Fintype.card (SixVertexToroidalBoundary N M) •
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
      exact Finset.sum_le_card_nsmul Finset.univ f _ fun ξ hξ => hle ξ
    _ = (2 : ℝ) ^ (N + M) *
        sixVertexRectangleMaxBalancedBoundaryContribution N M c := by
      rw [nsmul_eq_mul, sixVertexToroidalBoundary_card]
      norm_cast




theorem sixVertexRectangleBalancedPartitionSum_pow_blockCount_le
    {N M a b : ℕ} {c : ℝ} (hc : 0 ≤ c) (hN : Even (N + 1)) :
    sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ^
        ((a + 1) * (b + 1)) ≤
      ((2 : ℝ) ^ ((N + 1) + (M + 1))) ^ ((a + 1) * (b + 1)) *
        sixVertexRectangleBalancedPartitionSum
          ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c := by
  let Q := (a + 1) * (b + 1)
  let B := sixVertexRectangleMaxBalancedBoundaryContribution
    (N + 1) (M + 1) c
  have hbase : 0 ≤ sixVertexRectangleBalancedPartitionSum
      (N + 1) (M + 1) c :=
    sixVertexRectangleBalancedPartitionSum_nonneg _ _ hc
  have hselect := pow_le_pow_left₀ hbase
    (sixVertexRectangleBalancedPartitionSum_le_card_mul_maxBalanced
      (N + 1) (M + 1) c) Q
  obtain ⟨ξ, hξmax⟩ :=
    sixVertexRectangleMaxBalancedBoundaryContribution_exists
      (N + 1) (M + 1) c
  have hmaxpow : B ^ Q ≤
      sixVertexRectangleBalancedPartitionSum
        ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c := by
    by_cases hbal : ξ.Balanced
    · have hB : B = sixVertexRectangleBoundaryPartitionSum
          (N + 1) (M + 1) c (sixVertexToroidalRectangleBoundary ξ) := by
        simpa [B, hbal] using hξmax.symm
      rw [hB]
      have hrepeated :=
        sixVertexRectangleBoundaryPartitionSum_pow_blockCount_le_repeated
          (a := a) (b := b) hc ξ
      refine hrepeated.trans ?_
      unfold sixVertexRectangleBalancedPartitionSum
      have hsingle := Finset.single_le_sum
        (f := fun η : SixVertexToroidalBoundary
            ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) =>
          if η.Balanced then
            sixVertexRectangleBoundaryPartitionSum
              ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c
              (sixVertexToroidalRectangleBoundary η)
          else 0)
        (fun η hη => by
          dsimp
          split_ifs
          · exact sixVertexRectangleBoundaryPartitionSum_nonneg _ _ hc _
          · exact le_rfl)
        (Finset.mem_univ
          (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ))
      simpa [sixVertexRepeatToroidalBoundary_balanced hN ξ hbal] using hsingle
    · have hB : B = 0 := by
        simpa [B, hbal] using hξmax.symm
      rw [hB]
      simpa [Q] using
        (sixVertexRectangleBalancedPartitionSum_nonneg
          ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) hc)
  calc
    sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ^ Q ≤
        ((2 : ℝ) ^ ((N + 1) + (M + 1)) * B) ^ Q := hselect
    _ = ((2 : ℝ) ^ ((N + 1) + (M + 1))) ^ Q * B ^ Q := by
      rw [mul_pow]
    _ ≤ ((2 : ℝ) ^ ((N + 1) + (M + 1))) ^ Q *
        sixVertexRectangleBalancedPartitionSum
          ((a + 1) * (N + 1)) ((b + 1) * (M + 1)) c := by
      gcongr



def sixVertexRectangleStraightExtend {N M r q : ℕ}
    (z : Fin r → Bool) (ω : SixVertexRectangleArrows N M) :
    SixVertexRectangleArrows (N + r) (M + q) where
  horizontal kj :=
    Fin.addCases
      (fun j =>
        Fin.addCases (m := N) (n := r + 1)
          (fun i : Fin N => ω.horizontal (i.castSucc, j))
          (fun _ : Fin (r + 1) => ω.horizontal (Fin.last N, j)) kj.1)
      (fun _ : Fin q => false) kj.2
  vertical ik :=
    Fin.addCases
      (fun i : Fin N =>
        Fin.addCases (m := M) (n := q + 1)
          (fun j : Fin M => ω.vertical (i, j.castSucc))
          (fun _ : Fin (q + 1) => ω.vertical (i, Fin.last M)) ik.2)
      (fun i : Fin r => z i) ik.1

@[simp] theorem sixVertexRectangleStraightExtend_horizontal_castSucc
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows N M) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleStraightExtend (q := q) z ω).horizontal
        ((Fin.castAdd r i).castSucc, Fin.castAdd q j) =
      ω.horizontal (i.castSucc, j) := by
  have hx : (Fin.castAdd r i).castSucc = Fin.castAdd (r + 1) i := by
    ext
    rfl
  rw [hx]
  simp [sixVertexRectangleStraightExtend]

@[simp] theorem sixVertexRectangleStraightExtend_horizontal_succ
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) M)
    (i : Fin (N + 1)) (j : Fin M) :
    (sixVertexRectangleStraightExtend (q := q) z ω).horizontal
        ((Fin.castAdd r i).succ, Fin.castAdd q j) =
      ω.horizontal (i.succ, j) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hx : (Fin.castAdd r (Fin.last N)).succ =
        Fin.natAdd (N + 1) (0 : Fin (r + 1)) := by
      ext
      simp
    rw [hx]
    simp [sixVertexRectangleStraightExtend]
  · have hx : (Fin.castAdd r i.castSucc).succ =
        Fin.castAdd (r + 1) i.succ := by
      ext
      rfl
    rw [hx]
    simp [sixVertexRectangleStraightExtend]

@[simp] theorem sixVertexRectangleStraightExtend_vertical_castSucc
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows N M) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleStraightExtend (q := q) z ω).vertical
        (Fin.castAdd r i, (Fin.castAdd q j).castSucc) =
      ω.vertical (i, j.castSucc) := by
  have hy : (Fin.castAdd q j).castSucc = Fin.castAdd (q + 1) j := by
    ext
    rfl
  rw [hy]
  simp [sixVertexRectangleStraightExtend]

@[simp] theorem sixVertexRectangleStraightExtend_vertical_succ
    {N M r q : ℕ} (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows N (M + 1))
    (i : Fin N) (j : Fin (M + 1)) :
    (sixVertexRectangleStraightExtend (q := q) z ω).vertical
        (Fin.castAdd r i, (Fin.castAdd q j).succ) =
      ω.vertical (i, j.succ) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hy : (Fin.castAdd q (Fin.last M)).succ =
        Fin.natAdd (M + 1) (0 : Fin (q + 1)) := by
      ext
      simp
    rw [hy]
    simp [sixVertexRectangleStraightExtend]
  · have hy : (Fin.castAdd q j.castSucc).succ =
        Fin.castAdd (q + 1) j.succ := by
      ext
      rfl
    rw [hy]
    simp [sixVertexRectangleStraightExtend]


theorem sixVertexRectangleStraightExtend_localWeight_base
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1))
    (i : Fin (N + 1)) (j : Fin (M + 1)) :
    (sixVertexRectangleStraightExtend z ω).localWeight c
        (Fin.castAdd r i, Fin.castAdd q j) = ω.localWeight c (i, j) := by
  simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount,
      SixVertexRectangleArrows.IsCType]



theorem sixVertexRectangleStraightExtend_localWeight_right
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1))
    (i : Fin r) (j : Fin (M + 1)) :
    (sixVertexRectangleStraightExtend z ω).localWeight c
        (Fin.natAdd (N + 1) i, Fin.castAdd q j) = 1 := by
  have hx₀ : (Fin.natAdd (N + 1) i).castSucc =
      Fin.natAdd (N + 1) i.castSucc := by
    ext
    rfl
  have hx₁ : (Fin.natAdd (N + 1) i).succ =
      Fin.natAdd (N + 1) i.succ := by
    ext
    rfl
  cases hz : z i <;> cases hh : ω.horizontal (Fin.last (N + 1), j) <;>
    simp [sixVertexRectangleStraightExtend, hx₀, hx₁,
      SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount,
      SixVertexRectangleArrows.IsCType, hz, hh]


theorem sixVertexRectangleStraightExtend_localWeight_top
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1))
    (i : Fin ((N + 1) + r)) (j : Fin q) :
    (sixVertexRectangleStraightExtend z ω).localWeight c
        (i, Fin.natAdd (M + 1) j) = 1 := by
  have hy₀ : (Fin.natAdd (M + 1) j).castSucc =
      Fin.natAdd (M + 1) j.castSucc := by
    ext
    rfl
  have hy₁ : (Fin.natAdd (M + 1) j).succ =
      Fin.natAdd (M + 1) j.succ := by
    ext
    rfl
  refine Fin.addCases (m := N + 1) (n := r) ?_ ?_ i
  · intro x
    cases hv : ω.vertical (x, Fin.last (M + 1)) <;>
      simp [sixVertexRectangleStraightExtend, hy₀, hy₁,
        SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount,
        SixVertexRectangleArrows.IsCType, hv]
  · intro x
    cases hz : z x <;>
      simp [sixVertexRectangleStraightExtend, hy₀, hy₁,
        SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount,
        SixVertexRectangleArrows.IsCType, hz]


theorem sixVertexRectangleStraightExtend_weight
    {N M r q : ℕ} (c : ℝ) (z : Fin r → Bool)
    (ω : SixVertexRectangleArrows (N + 1) (M + 1)) :
    (sixVertexRectangleStraightExtend (q := q) z ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexRectangleArrows.weight,
    Fintype.prod_prod_type]
  rw [Fin.prod_univ_add]
  have hbase :
      (∏ i : Fin (N + 1),
        ∏ j : Fin ((M + 1) + q),
          (sixVertexRectangleStraightExtend z ω).localWeight c
            (Fin.castAdd r i, j)) =
        ∏ i : Fin (N + 1), ∏ j : Fin (M + 1), ω.localWeight c (i, j) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Fin.prod_univ_add]
    simp [sixVertexRectangleStraightExtend_localWeight_base,
      sixVertexRectangleStraightExtend_localWeight_top]
  rw [hbase]
  have hright :
      (∏ i : Fin r,
        ∏ j : Fin ((M + 1) + q),
          (sixVertexRectangleStraightExtend z ω).localWeight c
            (Fin.natAdd (N + 1) i, j)) = 1 := by
    apply Finset.prod_eq_one
    intro i hi
    rw [Fin.prod_univ_add]
    simp [sixVertexRectangleStraightExtend_localWeight_right,
      sixVertexRectangleStraightExtend_localWeight_top]
  rw [hright, mul_one]
  exact (Fintype.prod_prod_type fun ij : Fin (N + 1) × Fin (M + 1) =>
    ω.localWeight c ij).symm


def sixVertexStraightExtendedToroidalBoundary {N M r : ℕ}
    (q : ℕ) (ξ : SixVertexToroidalBoundary N M) (z : Fin r → Bool) :
    SixVertexToroidalBoundary (N + r) (M + q) :=
  (Fin.addCases ξ.1 (fun _ : Fin q => false), Fin.addCases ξ.2 z)


theorem sixVertexRectangleStraightExtend_boundary
    {N M r q : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (z : Fin r → Bool)
    (ω : SixVertexRectangleBoundaryFiber
      (sixVertexToroidalRectangleBoundary ξ)) :
    sixVertexRectangleBoundary (sixVertexRectangleStraightExtend z ω.1) =
      sixVertexToroidalRectangleBoundary
        (sixVertexStraightExtendedToroidalBoundary q ξ z) := by
  apply SixVertexRectangleBoundary.ext
  · funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have h := congrArg (fun η => η.left k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]
  · funext j
    refine Fin.addCases ?_ ?_ j
    · intro k
      have h := congrArg (fun η => η.right k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      have h := congrArg (fun η => η.bottom k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]
  · funext i
    refine Fin.addCases ?_ ?_ i
    · intro k
      have h := congrArg (fun η => η.top k) ω.2
      simpa [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary] using h
    · intro k
      simp [sixVertexRectangleBoundary, sixVertexRectangleStraightExtend,
        sixVertexToroidalRectangleBoundary,
        sixVertexStraightExtendedToroidalBoundary]


def sixVertexHalfFilledRow (r : ℕ) : Fin r → Bool :=
  fun i => decide (i.val < r / 2)

theorem sixVertexHalfFilledRow_upCount (r : ℕ) :
    #{i | sixVertexHalfFilledRow r i} = r / 2 := by
  simp [sixVertexHalfFilledRow, Fin.card_filter_val_lt,
    Nat.div_le_self]


theorem sixVertexStraightExtendedToroidalBoundary_balanced
    {N M r : ℕ} (hN : Even N) (hr : Even r) (q : ℕ)
    (ξ : SixVertexToroidalBoundary N M) (hξ : ξ.Balanced) :
    (sixVertexStraightExtendedToroidalBoundary q ξ
      (sixVertexHalfFilledRow r)).Balanced := by
  unfold SixVertexToroidalBoundary.Balanced at hξ ⊢
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp only [sixVertexStraightExtendedToroidalBoundary, Fin.addCases_left,
    Fin.addCases_right]
  rw [← Finset.card_filter, ← Finset.card_filter, hξ,
    sixVertexHalfFilledRow_upCount]
  rcases hN with ⟨N, rfl⟩
  rcases hr with ⟨r, rfl⟩
  have hNhalf : (N + N) / 2 = N := by omega
  have hrhalf : (r + r) / 2 = r := by omega
  rw [hNhalf, hrhalf]
  have hadd : (N + N) + (r + r) = (N + r) + (N + r) := by omega
  rw [hadd]
  omega



theorem sixVertexRectangleStraightExtend_injective
    {N M r q : ℕ} (z : Fin r → Bool) :
    Function.Injective
      (sixVertexRectangleStraightExtend (N := N + 1) (M := M + 1)
        (q := q) z) := by
  intro ω η h
  apply SixVertexRectangleArrows.ext
  · funext kj
    rcases kj with ⟨k, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) k
    · have h' := congrArg (fun ρ => ρ.horizontal
          (Fin.natAdd (N + 1) (0 : Fin (r + 1)), Fin.castAdd q j)) h
      simpa [sixVertexRectangleStraightExtend] using h'
    · have h' := congrArg (fun ρ => ρ.horizontal
          (Fin.castAdd (r + 1) i, Fin.castAdd q j)) h
      simpa [sixVertexRectangleStraightExtend] using h'
  · funext ik
    rcases ik with ⟨i, k⟩
    refine Fin.lastCases ?_ (fun j => ?_) k
    · have h' := congrArg (fun ρ => ρ.vertical
          (Fin.castAdd r i, Fin.natAdd (M + 1) (0 : Fin (q + 1)))) h
      simpa [sixVertexRectangleStraightExtend] using h'
    · have h' := congrArg (fun ρ => ρ.vertical
          (Fin.castAdd r i, Fin.castAdd (q + 1) j)) h
      simpa [sixVertexRectangleStraightExtend] using h'


def sixVertexRectangleStraightExtendBoundaryFiber
    {N M r q : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (z : Fin r → Bool) :
    SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary ξ) →
      SixVertexRectangleBoundaryFiber
        (sixVertexToroidalRectangleBoundary
          (sixVertexStraightExtendedToroidalBoundary q ξ z)) :=
  fun ω => ⟨sixVertexRectangleStraightExtend (q := q) z ω.1,
    sixVertexRectangleStraightExtend_boundary z ω⟩

theorem sixVertexRectangleStraightExtendBoundaryFiber_injective
    {N M r q : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (z : Fin r → Bool) :
    Function.Injective
      (sixVertexRectangleStraightExtendBoundaryFiber (q := q) (ξ := ξ) z) := by
  intro ω η h
  apply Subtype.ext
  apply sixVertexRectangleStraightExtend_injective z
  exact congrArg Subtype.val h


abbrev SixVertexRectangleBalancedBoundaryFibers (N M : ℕ) :=
  Σ ξ : {ξ : SixVertexToroidalBoundary N M // ξ.Balanced},
    SixVertexRectangleBoundaryFiber
      (sixVertexToroidalRectangleBoundary ξ.1)



theorem sixVertexRectangleBalancedPartitionSum_eq_fiberSum
    (N M : ℕ) (c : ℝ) :
    sixVertexRectangleBalancedPartitionSum N M c =
      ∑ ξω : SixVertexRectangleBalancedBoundaryFibers N M,
        ξω.2.1.weight c := by
  rw [sixVertexRectangleBalancedPartitionSum]
  simp_rw [sixVertexRectangleBoundaryPartitionSum_eq_fiberSum]
  calc
    (∑ ξ : SixVertexToroidalBoundary N M,
      if ξ.Balanced then
        ∑ ω : SixVertexRectangleBoundaryFiber
          (sixVertexToroidalRectangleBoundary ξ), ω.1.weight c
      else 0) =
        ∑ ξ ∈ Finset.univ.filter
            (fun ξ : SixVertexToroidalBoundary N M => ξ.Balanced),
          ∑ ω : SixVertexRectangleBoundaryFiber
            (sixVertexToroidalRectangleBoundary ξ), ω.1.weight c := by
      rw [Finset.sum_filter]
    _ = ∑ ξ : {ξ : SixVertexToroidalBoundary N M // ξ.Balanced},
          ∑ ω : SixVertexRectangleBoundaryFiber
            (sixVertexToroidalRectangleBoundary ξ.1), ω.1.weight c := by
      rw [Finset.sum_subtype
        (p := fun ξ : SixVertexToroidalBoundary N M => ξ.Balanced)
        (Finset.univ.filter
          fun ξ : SixVertexToroidalBoundary N M => ξ.Balanced) (by simp)]
    _ = ∑ ξω : SixVertexRectangleBalancedBoundaryFibers N M,
          ξω.2.1.weight c := by
      rw [Fintype.sum_sigma]



def sixVertexRectangleStraightExtendBalancedFibers
    {N M r : ℕ} (hN : Even (N + 1)) (hr : Even r) (q : ℕ) :
    SixVertexRectangleBalancedBoundaryFibers (N + 1) (M + 1) →
      SixVertexRectangleBalancedBoundaryFibers
        ((N + 1) + r) ((M + 1) + q) :=
  fun ξω =>
    ⟨⟨sixVertexStraightExtendedToroidalBoundary q ξω.1.1
        (sixVertexHalfFilledRow r),
      sixVertexStraightExtendedToroidalBoundary_balanced
        hN hr q ξω.1.1 ξω.1.2⟩,
      sixVertexRectangleStraightExtendBoundaryFiber
        (q := q) (ξ := ξω.1.1) (sixVertexHalfFilledRow r) ξω.2⟩

theorem sixVertexRectangleStraightExtendBalancedFibers_injective
    {N M r : ℕ} (hN : Even (N + 1)) (hr : Even r) (q : ℕ) :
    Function.Injective
      (sixVertexRectangleStraightExtendBalancedFibers
        (M := M) hN hr q) := by
  rintro ⟨⟨ξ, hξ⟩, ω⟩ ⟨⟨η, hη⟩, ν⟩ h
  have hext := congrArg
    (fun x : SixVertexRectangleBalancedBoundaryFibers
        ((N + 1) + r) ((M + 1) + q) => x.2.1) h
  have hων : ω.1 = ν.1 :=
    sixVertexRectangleStraightExtend_injective
      (sixVertexHalfFilledRow r) hext
  have hrect : sixVertexToroidalRectangleBoundary ξ =
      sixVertexToroidalRectangleBoundary η := by
    rw [← ω.2, ← ν.2, hων]
  have hξη : ξ = η := by
    apply Prod.ext
    · funext j
      have hleft := congrArg (fun b => b.left j) hrect
      simpa [sixVertexToroidalRectangleBoundary] using hleft
    · funext i
      have hbottom := congrArg (fun b => b.bottom i) hrect
      simpa [sixVertexToroidalRectangleBoundary] using hbottom
  subst η
  have hsub : (⟨ξ, hξ⟩ : {ξ : SixVertexToroidalBoundary (N + 1) (M + 1) //
      ξ.Balanced}) = ⟨ξ, hη⟩ := Subtype.ext rfl
  apply Sigma.ext hsub
  cases hsub
  exact heq_of_eq (Subtype.ext hων)

theorem sixVertexRectangleStraightExtendBalancedFibers_weight
    {N M r : ℕ} (hN : Even (N + 1)) (hr : Even r) (q : ℕ)
    (c : ℝ) (ξω : SixVertexRectangleBalancedBoundaryFibers
      (N + 1) (M + 1)) :
    ((sixVertexRectangleStraightExtendBalancedFibers hN hr q ξω).2.1).weight c =
      ξω.2.1.weight c := by
  exact sixVertexRectangleStraightExtend_weight c
    (sixVertexHalfFilledRow r) ξω.2.1



theorem sixVertexRectangleBalancedPartitionSum_le_straightExtend
    {N M r : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : Even (N + 1)) (hr : Even r) (q : ℕ) :
    sixVertexRectangleBalancedPartitionSum (N + 1) (M + 1) c ≤
      sixVertexRectangleBalancedPartitionSum
        ((N + 1) + r) ((M + 1) + q) c := by
  rw [sixVertexRectangleBalancedPartitionSum_eq_fiberSum,
    sixVertexRectangleBalancedPartitionSum_eq_fiberSum]
  let extend := sixVertexRectangleStraightExtendBalancedFibers
    (M := M) hN hr q
  calc
    (∑ ξω : SixVertexRectangleBalancedBoundaryFibers (N + 1) (M + 1),
      ξω.2.1.weight c) =
        ∑ ξω : SixVertexRectangleBalancedBoundaryFibers (N + 1) (M + 1),
          (extend ξω).2.1.weight c := by
      apply Fintype.sum_congr
      intro ξω
      exact (sixVertexRectangleStraightExtendBalancedFibers_weight
        hN hr q c ξω).symm
    _ = ∑ η ∈ Finset.univ.image extend, η.2.1.weight c := by
      rw [Finset.sum_image
        (sixVertexRectangleStraightExtendBalancedFibers_injective
          (M := M) hN hr q).injOn]
    _ ≤ ∑ η : SixVertexRectangleBalancedBoundaryFibers
          ((N + 1) + r) ((M + 1) + q), η.2.1.weight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.subset_univ _
      · intro η hη hnot
        exact SixVertexRectangleArrows.weight_nonneg hc η.2.1


theorem sixVertexRectangleBalancedPartitionSum_pow_mulFactors_le
    {N M A B : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hA : 0 < A) (hB : 0 < B) :
    sixVertexRectangleBalancedPartitionSum N M c ^ (A * B) ≤
      ((2 : ℝ) ^ (N + M)) ^ (A * B) *
        sixVertexRectangleBalancedPartitionSum (A * N) (B * M) c := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  obtain ⟨A, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hA.ne'
  obtain ⟨B, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hB.ne'
  exact sixVertexRectangleBalancedPartitionSum_pow_blockCount_le hc hNeven



theorem sixVertexRectangleBalancedPartitionSum_le_straightExtend_general
    {N M r q : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N) (hr : Even r) :
    sixVertexRectangleBalancedPartitionSum N M c ≤
      sixVertexRectangleBalancedPartitionSum (N + r) (M + q) c := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  exact sixVertexRectangleBalancedPartitionSum_le_straightExtend
    hc hNeven hr q




theorem sixVertexRectangleBalancedPartitionSum_blockRepetition
    {N M n m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hn : N < n) (hm : M < m) (hneven : Even n) :
    sixVertexRectangleBalancedPartitionSum N M c ^
        ((n / N) * (m / M)) ≤
      ((2 : ℝ) ^ (N + M)) ^ ((n / N) * (m / M)) *
        sixVertexRectangleBalancedPartitionSum n m c := by
  let A := n / N
  let B := m / M
  let r := n % N
  let q := m % M
  have hA : 0 < A := Nat.div_pos hn.le hN
  have hB : 0 < B := Nat.div_pos hm.le hM
  have hAN : 0 < A * N := Nat.mul_pos hA hN
  have hBM : 0 < B * M := Nat.mul_pos hB hM
  have hANeven : Even (A * N) := hNeven.mul_left A
  have hr : Even r := by
    exact (Even.mod_even_iff hNeven).mpr hneven
  have hn_decomp : A * N + r = n := by
    dsimp [A, r]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod n N
  have hm_decomp : B * M + q = m := by
    dsimp [B, q]
    rw [Nat.mul_comm]
    exact Nat.div_add_mod m M
  have hexact := sixVertexRectangleBalancedPartitionSum_pow_mulFactors_le
    hc hN hM hNeven hA hB
  have hextend :=
    sixVertexRectangleBalancedPartitionSum_le_straightExtend_general
      (N := A * N) (M := B * M) (r := r) (q := q)
      hc hAN hBM hANeven hr
  calc
    sixVertexRectangleBalancedPartitionSum N M c ^ (A * B) ≤
        ((2 : ℝ) ^ (N + M)) ^ (A * B) *
          sixVertexRectangleBalancedPartitionSum (A * N) (B * M) c := hexact
    _ ≤ ((2 : ℝ) ^ (N + M)) ^ (A * B) *
          sixVertexRectangleBalancedPartitionSum n m c := by
      rw [← hn_decomp, ← hm_decomp]
      gcongr


def sixVertexHalfFilledStraightRectangle (N M : ℕ) :
    SixVertexRectangleArrows N M where
  horizontal _ := false
  vertical ik := sixVertexHalfFilledRow N ik.1


def sixVertexHalfFilledStraightBoundary (N M : ℕ) :
    SixVertexToroidalBoundary N M :=
  (fun _ => false, sixVertexHalfFilledRow N)

theorem sixVertexHalfFilledStraightBoundary_balanced (N M : ℕ) :
    (sixVertexHalfFilledStraightBoundary N M).Balanced := by
  exact sixVertexHalfFilledRow_upCount N

theorem sixVertexHalfFilledStraightRectangle_boundary (N M : ℕ) :
    sixVertexRectangleBoundary (sixVertexHalfFilledStraightRectangle N M) =
      sixVertexToroidalRectangleBoundary
        (sixVertexHalfFilledStraightBoundary N M) := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexRectangleBoundary, sixVertexHalfFilledStraightRectangle,
      sixVertexToroidalRectangleBoundary,
      sixVertexHalfFilledStraightBoundary]

theorem sixVertexHalfFilledStraightRectangle_localWeight
    (N M : ℕ) (c : ℝ) (v : Fin N × Fin M) :
    (sixVertexHalfFilledStraightRectangle N M).localWeight c v = 1 := by
  cases h : sixVertexHalfFilledRow N v.1 <;>
    simp [sixVertexHalfFilledStraightRectangle,
      SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount,
      SixVertexRectangleArrows.IsCType, h]

theorem sixVertexHalfFilledStraightRectangle_weight
    (N M : ℕ) (c : ℝ) :
    (sixVertexHalfFilledStraightRectangle N M).weight c = 1 := by
  rw [SixVertexRectangleArrows.weight]
  simp [sixVertexHalfFilledStraightRectangle_localWeight]



theorem sixVertexRectangleBalancedPartitionSum_pos
    (N M : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    0 < sixVertexRectangleBalancedPartitionSum N M c := by
  rw [sixVertexRectangleBalancedPartitionSum_eq_fiberSum]
  let ξω : SixVertexRectangleBalancedBoundaryFibers N M :=
    ⟨⟨sixVertexHalfFilledStraightBoundary N M,
      sixVertexHalfFilledStraightBoundary_balanced N M⟩,
      ⟨sixVertexHalfFilledStraightRectangle N M,
        sixVertexHalfFilledStraightRectangle_boundary N M⟩⟩
  have hsingle : ξω.2.1.weight c ≤
      ∑ η : SixVertexRectangleBalancedBoundaryFibers N M,
        η.2.1.weight c :=
    Finset.single_le_sum
      (fun η hη => SixVertexRectangleArrows.weight_nonneg hc η.2.1)
      (Finset.mem_univ ξω)
  change (sixVertexHalfFilledStraightRectangle N M).weight c ≤ _ at hsingle
  rw [sixVertexHalfFilledStraightRectangle_weight] at hsingle
  exact zero_lt_one.trans_le hsingle



theorem sixVertexRectangleBalancedPartitionSum_log_blockRepetition
    {N M n m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hn : N < n) (hm : M < m) (hneven : Even n) :
    (((n / N) * (m / M) : ℕ) : ℝ) *
        Real.log (sixVertexRectangleBalancedPartitionSum N M c) ≤
      (((n / N) * (m / M) : ℕ) : ℝ) * (N + M : ℝ) * Real.log 2 +
        Real.log (sixVertexRectangleBalancedPartitionSum n m c) := by
  let Q := (n / N) * (m / M)
  let Z := sixVertexRectangleBalancedPartitionSum N M c
  let Z' := sixVertexRectangleBalancedPartitionSum n m c
  have hZ : 0 < Z := sixVertexRectangleBalancedPartitionSum_pos N M hc
  have hZ' : 0 < Z' := sixVertexRectangleBalancedPartitionSum_pos n m hc
  have hfactor : 0 < ((2 : ℝ) ^ (N + M)) ^ Q := by positivity
  have hfinite := sixVertexRectangleBalancedPartitionSum_blockRepetition
    hc hN hM hNeven hn hm hneven
  have hlog := Real.strictMonoOn_log.monotoneOn
    (pow_pos hZ Q) (mul_pos hfactor hZ') hfinite
  rw [Real.log_pow, Real.log_mul hfactor.ne' hZ'.ne',
    Real.log_pow, Real.log_pow] at hlog
  dsimp [Q, Z, Z'] at hlog ⊢
  norm_num at hlog
  convert hlog using 1 <;> push_cast <;> ring



theorem sixVertexRectangleBalancedDensity_blockRepetition
    {N M n m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hN : 0 < N) (hM : 0 < M) (hNeven : Even N)
    (hn : N < n) (hm : M < m) (hneven : Even n) :
    ((((n / N) * (m / M) : ℕ) : ℝ) *
          (Real.log (sixVertexRectangleBalancedPartitionSum N M c) -
            (N + M : ℝ) * Real.log 2)) /
        ((n : ℝ) * (m : ℝ)) ≤
      Real.log (sixVertexRectangleBalancedPartitionSum n m c) /
        ((n : ℝ) * (m : ℝ)) := by
  have hlog := sixVertexRectangleBalancedPartitionSum_log_blockRepetition
    hc hN hM hNeven hn hm hneven
  have hraw : ((((n / N) * (m / M) : ℕ) : ℝ) *
      (Real.log (sixVertexRectangleBalancedPartitionSum N M c) -
        (N + M : ℝ) * Real.log 2)) ≤
      Real.log (sixVertexRectangleBalancedPartitionSum n m c) := by
    linarith
  exact div_le_div_of_nonneg_right hraw (by positivity)

end StatMech.FrontierD
