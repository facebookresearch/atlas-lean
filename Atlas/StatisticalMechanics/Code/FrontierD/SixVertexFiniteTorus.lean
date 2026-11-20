/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierD.SixVertex
import Mathlib.LinearAlgebra.Matrix.Trace

open Finset Matrix

namespace StatMech.FrontierD




def finitePeriodicSucc {M : ℕ} (hM : 0 < M) (i : Fin M) : Fin M :=
  ⟨(i.val + 1) % M, Nat.mod_lt _ hM⟩

@[simp] theorem finitePeriodicSucc_castSucc {M : ℕ} (i : Fin M) :
    finitePeriodicSucc (Nat.succ_pos M) i.castSucc = i.succ := by
  ext
  simp [finitePeriodicSucc, Nat.mod_eq_of_lt]

@[simp] theorem finitePeriodicSucc_last (M : ℕ) :
    finitePeriodicSucc (Nat.succ_pos M) (Fin.last M) = 0 := by
  ext
  simp [finitePeriodicSucc]


def matrixCycleWeight {α : Type*} [Fintype α] {M : ℕ} (hM : 0 < M)
    (A : Matrix α α ℝ) (x : Fin M → α) : ℝ :=
  ∏ i, A (x i) (x (finitePeriodicSucc hM i))


abbrev MatrixCompatibleCycle {α : Type*} [Fintype α] {M : ℕ}
    (hM : 0 < M) (A : Matrix α α ℝ) :=
  {x : Fin M → α // ∀ i, A (x i) (x (finitePeriodicSucc hM i)) ≠ 0}


noncomputable def matrixCompatibleCycleSum {α : Type*} [Fintype α]
    {M : ℕ} (hM : 0 < M) (A : Matrix α α ℝ) : ℝ :=
  ∑ x : MatrixCompatibleCycle hM A, matrixCycleWeight hM A x

private def matrixChainWeight {α : Type*} [Fintype α] {k : ℕ}
    (A : Matrix α α ℝ) (x : Fin (k + 1) → α) (b : α) : ℝ :=
  (∏ i : Fin k, A (x i.castSucc) (x i.succ)) * A (x (Fin.last k)) b

private theorem matrixChainWeight_snoc {α : Type*} [Fintype α] {k : ℕ}
    (A : Matrix α α ℝ) (a b z : α) (q : Fin k → α) :
    matrixChainWeight A (Fin.cons a (Fin.snoc q z)) b =
      matrixChainWeight A (Fin.cons a q) z * A z b := by
  rw [Fin.cons_snoc_eq_snoc_cons]
  let x : Fin (k + 1) → α := Fin.cons a q
  let y : Fin (k + 2) → α := Fin.snoc x z
  change matrixChainWeight A y b = matrixChainWeight A x z * A z b
  have hsucc (i : Fin k) : i.castSucc.succ = i.succ.castSucc := by
    ext
    rfl
  have hprod :
      ∏ i : Fin k,
          A (y i.castSucc.castSucc) (y i.castSucc.succ) =
        ∏ i : Fin k, A (x i.castSucc) (x i.succ) := by
    apply Finset.prod_congr rfl
    intro i hi
    dsimp [y]
    rw [hsucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
  simp only [matrixChainWeight, Fin.prod_univ_castSucc]
  rw [hprod]
  dsimp [y]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

private theorem matrix_pow_succ_apply_eq_sum_chain {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (k : ℕ) (a b : α) :
    (A ^ (k + 1)) a b =
      ∑ q : Fin k → α, matrixChainWeight A (Fin.cons a q) b := by
  induction k generalizing b with
  | zero =>
      simp [matrixChainWeight]
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      simp_rw [ih]
      simp_rw [Finset.sum_mul]
      calc
        ∑ x, ∑ q, matrixChainWeight A (Fin.cons a q) x * A x b =
            ∑ zq : α × (Fin k → α),
              matrixChainWeight A (Fin.cons a zq.2) zq.1 * A zq.1 b :=
          (Fintype.sum_prod_type (fun zq : α × (Fin k → α) =>
            matrixChainWeight A (Fin.cons a zq.2) zq.1 * A zq.1 b)).symm
        _ = ∑ q : Fin (k + 1) → α, matrixChainWeight A (Fin.cons a q) b := by
          apply Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (k + 1) => α))
          intro zq
          exact (matrixChainWeight_snoc A a b zq.1 zq.2).symm

private theorem matrixCycleWeight_eq_chain {α : Type*} [Fintype α]
    (A : Matrix α α ℝ) (k : ℕ) (x : Fin (k + 1) → α) :
    matrixCycleWeight (Nat.succ_pos k) A x =
      matrixChainWeight A x (x 0) := by
  rw [matrixCycleWeight, Fin.prod_univ_castSucc]
  simp only [finitePeriodicSucc_castSucc, finitePeriodicSucc_last,
    matrixChainWeight]

private theorem matrixCycleWeight_sum_eq_trace_pow {α : Type*} [Fintype α]
    [DecidableEq α] (A : Matrix α α ℝ) (k : ℕ) :
    ∑ x : Fin (k + 1) → α, matrixCycleWeight (Nat.succ_pos k) A x =
      Matrix.trace (A ^ (k + 1)) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  simp_rw [matrix_pow_succ_apply_eq_sum_chain]
  calc
    ∑ x : Fin (k + 1) → α, matrixCycleWeight (Nat.succ_pos k) A x =
        ∑ aq : α × (Fin k → α),
          matrixChainWeight A (Fin.cons aq.1 aq.2) aq.1 := by
      symm
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => α))
      intro aq
      exact (matrixCycleWeight_eq_chain A k (Fin.cons aq.1 aq.2)).symm
    _ = ∑ a : α, ∑ q : Fin k → α,
        matrixChainWeight A (Fin.cons a q) a :=
      Fintype.sum_prod_type _




theorem matrixCompatibleCycleSum_eq_trace_pow {α : Type*} [Fintype α]
    [DecidableEq α] {M : ℕ} (hM : 0 < M) (A : Matrix α α ℝ) :
    matrixCompatibleCycleSum hM A = Matrix.trace (A ^ M) := by
  classical
  have hfilter :
      ∑ x : MatrixCompatibleCycle hM A, matrixCycleWeight hM A x =
        ∑ x : Fin M → α, matrixCycleWeight hM A x := by
    rw [← Finset.sum_subtype
      (Finset.univ.filter fun x : Fin M → α =>
        ∀ i, A (x i) (x (finitePeriodicSucc hM i)) ≠ 0) (by simp)]
    apply Finset.sum_filter_of_ne
    intro x hx hweight i hi
    apply hweight
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  rw [matrixCompatibleCycleSum, hfilter]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  exact matrixCycleWeight_sum_eq_trace_pow A k





abbrev SixVertexPeriodicRows (N M : ℕ) (hM : 0 < M) (c : ℝ) :=
  MatrixCompatibleCycle hM (sixVertexTransfer N c)


noncomputable def sixVertexPeriodicRowWeight {N M : ℕ} (hM : 0 < M) (c : ℝ)
    (x : SixVertexPeriodicRows N M hM c) : ℝ :=
  matrixCycleWeight hM (sixVertexTransfer N c) x




noncomputable def sixVertexPeriodicRowPartitionSum
    (N M : ℕ) (hM : 0 < M) (c : ℝ) : ℝ :=
  ∑ x : SixVertexPeriodicRows N M hM c,
    sixVertexPeriodicRowWeight hM c x

private def sixVertexRowInSector {N n : ℕ} (x : SixVertexRow N)
    (h : sixVertexUpCount x = n) : SixVertexSector N n :=
  ⟨({i | x i} : Finset (Fin N)), by simpa [sixVertexUpCount] using h⟩

@[simp] private theorem sixVertexSectorRow_rowInSector {N n : ℕ}
    (x : SixVertexRow N) (h : sixVertexUpCount x = n) :
    sixVertexSectorRow (sixVertexRowInSector x h) = x := by
  funext i
  simp [sixVertexSectorRow, sixVertexRowInSector]

theorem sixVertexPeriodicRows_upCount_eq {N M : ℕ} (hM : 0 < M) (c : ℝ)
    (x : SixVertexPeriodicRows N M hM c) (i : Fin M) :
    sixVertexUpCount (x.1 i) = sixVertexUpCount (x.1 ⟨0, hM⟩) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      have hs : finitePeriodicSucc hM i.castSucc = i.succ := by
        ext
        simp [finitePeriodicSucc, Nat.mod_eq_of_lt]
      have hstep := sixVertexTransfer_preserves_upCount c (x.property i.castSucc)
      rw [hs] at hstep
      exact hstep.symm.trans ih

private def sixVertexPeriodicSectorIndex {N M : ℕ} {hM : 0 < M} {c : ℝ}
    (x : SixVertexPeriodicRows N M hM c) : Fin (N + 1) :=
  ⟨sixVertexUpCount (x.1 ⟨0, hM⟩), by
    have hcard := Finset.card_le_univ ({i | x.1 ⟨0, hM⟩ i} : Finset (Fin N))
    simpa [sixVertexUpCount] using Nat.lt_succ_of_le hcard⟩


abbrev SixVertexPeriodicRowsInSector
    (N M : ℕ) (hM : 0 < M) (c : ℝ) (n : Fin (N + 1)) :=
  {x : SixVertexPeriodicRows N M hM c //
    sixVertexUpCount (x.1 ⟨0, hM⟩) = n.val}


noncomputable def sixVertexPeriodicRowsLabelEquiv
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    SixVertexPeriodicRows N M hM c ≃
      Σ n : Fin (N + 1), SixVertexPeriodicRowsInSector N M hM c n where
  toFun x := ⟨sixVertexPeriodicSectorIndex x, ⟨x, rfl⟩⟩
  invFun nx := nx.2.1
  left_inv _ := rfl
  right_inv nx := by
    rcases nx with ⟨n, ⟨x, hx⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      exact hx
    · apply (Subtype.heq_iff_coe_eq (fun y => by
          change (sixVertexUpCount (y.1 ⟨0, hM⟩) =
            (sixVertexPeriodicSectorIndex x).val) ↔
            (sixVertexUpCount (y.1 ⟨0, hM⟩) = n.val)
          rw [show (sixVertexPeriodicSectorIndex x).val = n.val from hx])).2
      rfl



noncomputable def sixVertexPeriodicRowsFixedSectorEquiv
    (N M : ℕ) (hM : 0 < M) (c : ℝ) (n : Fin (N + 1)) :
    SixVertexPeriodicRowsInSector N M hM c n ≃
      MatrixCompatibleCycle hM (sixVertexSectorTransfer N n c) where
  toFun x := by
    let y : Fin M → SixVertexSector N n := fun i =>
      sixVertexRowInSector (x.1.1 i)
        ((sixVertexPeriodicRows_upCount_eq hM c x.1 i).trans x.2)
    refine ⟨y, ?_⟩
    intro i
    change sixVertexTransfer N c (sixVertexSectorRow (y i))
      (sixVertexSectorRow (y (finitePeriodicSucc hM i))) ≠ 0
    simpa [y] using x.1.2 i
  invFun y := by
    refine ⟨⟨fun i => sixVertexSectorRow (y.1 i), ?_⟩, ?_⟩
    · intro i
      exact y.2 i
    · simp
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp
  right_inv y := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    ext j
    simp [sixVertexRowInSector, sixVertexSectorRow]

private theorem sixVertexPeriodicRowsFixedSectorEquiv_weight
    (N M : ℕ) (hM : 0 < M) (c : ℝ) (n : Fin (N + 1))
    (x : SixVertexPeriodicRowsInSector N M hM c n) :
    sixVertexPeriodicRowWeight hM c x.1 =
      matrixCycleWeight hM (sixVertexSectorTransfer N n c)
        (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n x) := by
  rw [sixVertexPeriodicRowWeight, matrixCycleWeight, matrixCycleWeight]
  apply Finset.prod_congr rfl
  intro i hi
  change sixVertexTransfer N c (x.1.1 i)
    (x.1.1 (finitePeriodicSucc hM i)) = _
  simp [sixVertexPeriodicRowsFixedSectorEquiv, sixVertexSectorTransfer]



theorem sixVertexPeriodicRowPartitionSum_eq_trace
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexPeriodicRowPartitionSum N M hM c =
      Matrix.trace (sixVertexTransfer N c ^ M) := by
  exact matrixCompatibleCycleSum_eq_trace_pow hM (sixVertexTransfer N c)



theorem sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    sixVertexPeriodicRowPartitionSum N M hM c =
      ∑ n : Fin (N + 1), Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
  rw [sixVertexPeriodicRowPartitionSum]
  calc
    ∑ x : SixVertexPeriodicRows N M hM c, sixVertexPeriodicRowWeight hM c x =
        ∑ nx : Σ n : Fin (N + 1),
          SixVertexPeriodicRowsInSector N M hM c n,
            sixVertexPeriodicRowWeight hM c nx.2.1 := by
      apply Fintype.sum_equiv (sixVertexPeriodicRowsLabelEquiv N M hM c)
      intro x
      rfl
    _ = ∑ n : Fin (N + 1),
        ∑ x : SixVertexPeriodicRowsInSector N M hM c n,
          sixVertexPeriodicRowWeight hM c x.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ n : Fin (N + 1),
        ∑ y : MatrixCompatibleCycle hM (sixVertexSectorTransfer N n c),
          matrixCycleWeight hM (sixVertexSectorTransfer N n c) y := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Fintype.sum_equiv (sixVertexPeriodicRowsFixedSectorEquiv N M hM c n)
      exact sixVertexPeriodicRowsFixedSectorEquiv_weight N M hM c n
    _ = ∑ n : Fin (N + 1),
        matrixCompatibleCycleSum hM (sixVertexSectorTransfer N n c) := by
      rfl
    _ = ∑ n : Fin (N + 1),
        Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact matrixCompatibleCycleSum_eq_trace_pow hM _


noncomputable def sixVertexFiniteTorusRowPartitionSum (T : EvenTorus) (c : ℝ) : ℝ :=
  sixVertexPeriodicRowPartitionSum T.width T.height T.height_pos c



theorem sixVertexFiniteTorusRowPartitionSum_eq_sum_sector_traces
    (T : EvenTorus) (c : ℝ) :
    sixVertexFiniteTorusRowPartitionSum T c =
      ∑ n : Fin (T.width + 1),
        Matrix.trace (sixVertexSectorTransfer T.width n c ^ T.height) := by
  exact sixVertexPeriodicRowPartitionSum_eq_sum_sector_traces
    T.width T.height T.height_pos c

end StatMech.FrontierD
