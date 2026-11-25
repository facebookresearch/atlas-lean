/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.RankManifold

/-! Tests for the local manifold structure of rank-`k` matrices: every public statement is
restated, including the `2 × 2` rank-one codimension-one case. -/

namespace MathlibExtTest.RankManifold

open _root_.Matrix
open scoped Topology ContDiff

section MatrixSection

variable {K : Type*} [Field K]

/-- The rank of a block-diagonal matrix is the sum of the ranks of the diagonal blocks. -/
example {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p]
    [Fintype q] (A : Matrix m n K) (D : Matrix p q K) :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  apply _root_.Matrix.rank_fromBlocks_zero₁₂_zero₂₁

/-- A matrix has rank zero iff it is zero. -/
example {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) :
    A.rank = 0 ↔ A = 0 := by
  apply _root_.Matrix.rank_eq_zero_iff

/-- **Schur rank additivity.** If the top-left block `A` is invertible, the rank of
`[[A, B], [C, D]]` is `card m` plus the rank of the Schur complement `D - C A⁻¹ B`. -/
example {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (A : Matrix m m K) (B : Matrix m q K) (C : Matrix p m K) (D : Matrix p q K)
    (hA : IsUnit A.det) :
    (fromBlocks A B C D).rank = Fintype.card m + (D - C * A⁻¹ * B).rank := by
  apply _root_.Matrix.rank_fromBlocks_of_isUnit_det
  assumption

/-- **Schur-complement characterization.** With `A` invertible, `[[A, B], [C, D]]` has rank
`card m` iff `D - C A⁻¹ B = 0`. -/
example {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (A : Matrix m m K) (B : Matrix m q K) (C : Matrix p m K) (D : Matrix p q K)
    (hA : IsUnit A.det) :
    (fromBlocks A B C D).rank = Fintype.card m ↔ D - C * A⁻¹ * B = 0 := by
  apply _root_.Matrix.rank_fromBlocks_eq_card_iff
  assumption

/-- With `A` invertible, `[[A, B], [C, D]]` has rank at most `card m` iff `D - C A⁻¹ B = 0`. -/
example {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (A : Matrix m m K) (B : Matrix m q K) (C : Matrix p m K) (D : Matrix p q K)
    (hA : IsUnit A.det) :
    (fromBlocks A B C D).rank ≤ Fintype.card m ↔ D - C * A⁻¹ * B = 0 := by
  apply _root_.Matrix.rank_fromBlocks_le_card_iff
  assumption

/-- A matrix of rank `k` has an invertible `k × k` submatrix (a nonzero `k`-minor). -/
example {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (F : Matrix ι κ K) (hF : F.rank = k) :
    ∃ (r : Fin k ↪ ι) (c : Fin k ↪ κ), IsUnit (F.submatrix r c).det := by
  apply _root_.Matrix.exists_isUnit_det_submatrix_of_rank_eq
  assumption

/-- The rows and columns of an `n × r` matrix of rank `k` can be permuted into block form
`[[A, B], [C, D]]` with invertible `k × k` block `A`. -/
example {n r k : ℕ} (F : Matrix (Fin n) (Fin r) K)
    (hF : F.rank = k) :
    ∃ (e₁ : Fin n ≃ Fin k ⊕ Fin (n - k)) (e₂ : Fin r ≃ Fin k ⊕ Fin (r - k)),
      IsUnit (reindex e₁ e₂ F).toBlocks₁₁.det := by
  apply _root_.Matrix.exists_reindex_isUnit_det_toBlocks₁₁
  assumption


end MatrixSection

section RankManifoldSection

open _root_.Matrix.RankManifold


section Defs

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- At `F = 0` the tangent space is `⊥`: every left/right kernel condition is vacuous, so
only `X = 0` is orthogonal to all of them. -/
example : tangentSpace (0 : Matrix (Fin 2) (Fin 2) ℝ) = ⊥ := by
  ext X
  simp only [Submodule.mem_bot]
  constructor
  · intro hX
    ext i j
    have h := hX (Pi.single i 1) (Pi.single j 1) (Matrix.vecMul_zero _) (Matrix.zero_mulVec _)
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h
  · intro h
    rw [h]
    intro u v _ _
    simp

/-- At `F = 0` the normal space is everything. -/
example : normalSpace (0 : Matrix (Fin 2) (Fin 2) ℝ) = ⊤ := by
  ext Y
  simp [normalSpace]

/-- At the rank-one matrix `!![1, 0; 0, 0]`, `!![0, 0; 0, 1]` is normal and `F` itself is
not. -/
example : !![0, 0; 0, 1] ∈ normalSpace (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

example : !![1, 0; 0, 0] ∉ normalSpace (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have h00 : (!![1, 0; 0, 0]ᵀ * !![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 0 := by
    rw [h.1]
    rfl
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

/-- At `!![1, 0; 0, 0]` the swap matrix is tangent (its bottom-right entry is `0`), and
`!![0, 0; 0, 1]` is not. -/
example : !![0, 1; 1, 0] ∈ tangentSpace (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro u v hu hv
  have hu0 : vecHead u = 0 := by
    have h := congrFun hu 0
    simpa [Matrix.vecMul, Fin.sum_univ_two] using h
  have hv0 : vecHead v = 0 := by
    have h := congrFun hv 0
    simpa [Matrix.mulVec, Fin.sum_univ_two] using h
  have hu0' : u 0 = 0 := hu0
  have hv0' : v 0 = 0 := hv0
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hu0', hv0']

example : !![0, 0; 0, 1] ∉ tangentSpace (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have h2 := h ![0, 1] ![0, 1]
    (by ext j; fin_cases j <;> simp [Matrix.vecMul])
    (by ext j; fin_cases j <;> simp [Matrix.mulVec])
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2

end Defs

section Algebra

variable {K : Type*} [Field K]

/-- Block chart, part 1: if the top-left block is invertible, rank `≤ card m` iff
rank `= card m`. -/
example {m p q : Type*} [Fintype m] [Fintype p]
    [Fintype q] [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (M : Matrix (m ⊕ p) (m ⊕ q) K) (hM : IsUnit M.toBlocks₁₁.det) :
    M.rank ≤ Fintype.card m ↔ M.rank = Fintype.card m := by
  apply _root_.Matrix.RankManifold.rank_le_iff_rank_eq_of_isUnit_det_toBlocks₁₁
  assumption

/-- Block chart, part 2: if the top-left block is invertible, rank `= card m` iff the Schur
complement vanishes. -/
example {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (M : Matrix (m ⊕ p) (m ⊕ q) K) (hM : IsUnit M.toBlocks₁₁.det) :
    M.rank = Fintype.card m ↔ M.toBlocks₂₂ = M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ := by
  apply _root_.Matrix.RankManifold.rank_eq_iff_toBlocks₂₂_eq_of_isUnit_det_toBlocks₁₁
  assumption

/-- Dimension count: `k(n+r-k) + (n-k)(r-k) = nr` for `k ≤ n` and `k ≤ r`. -/
example {n r k : ℕ} (hn : k ≤ n) (hr : k ≤ r) :
    k * (n + r - k) + (n - k) * (r - k) = n * r := by
  apply _root_.Matrix.RankManifold.dim_add_codim <;> assumption

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The tangent space at a rank-`k` matrix has dimension `k(n+r-k)`. -/
example (F : Matrix ι κ K) {k : ℕ} (hF : F.rank = k) :
    Module.finrank K (tangentSpace F) = k * (Fintype.card ι + Fintype.card κ - k) := by
  apply _root_.Matrix.RankManifold.finrank_tangentSpace
  assumption

/-- The normal space at a rank-`k` matrix has dimension `(n-k)(r-k)`. -/
example (F : Matrix ι κ K) {k : ℕ} (hF : F.rank = k) :
    Module.finrank K (normalSpace F) = (Fintype.card ι - k) * (Fintype.card κ - k) := by
  apply _root_.Matrix.RankManifold.finrank_normalSpace
  assumption

/-- The normal space is the orthogonal complement of the tangent space for the trace form
`(X, Y) ↦ trace (Xᵀ Y)` (the Frobenius inner product over `ℝ`). -/
example (F Y : Matrix ι κ K) :
    Y ∈ normalSpace F ↔ ∀ X ∈ tangentSpace F, (Xᵀ * Y).trace = 0 := by
  apply _root_.Matrix.RankManifold.mem_normalSpace_iff

end Algebra

section Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Lower semicontinuity of rank: `{M | k ≤ rank M}` is open. -/
example (k : ℕ) : IsOpen {M : Matrix ι κ ℝ | k ≤ M.rank} := by
  apply _root_.Matrix.RankManifold.isOpen_setOf_le_rank

/-- Near `F`, rank at most `rank F` is the same as rank exactly `rank F`. -/
example (F : Matrix ι κ ℝ) :
    ∀ᶠ M in 𝓝 F, (M.rank ≤ F.rank ↔ M.rank = F.rank) := by
  apply _root_.Matrix.RankManifold.eventually_rank_le_iff_rank_eq

/-- The block chart `{M | toBlocks₁₁ M invertible}` is open. -/
example {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] : IsOpen {M : Matrix (m ⊕ p) (m ⊕ q) ℝ | IsUnit M.toBlocks₁₁.det} := by
  apply _root_.Matrix.RankManifold.isOpen_setOf_isUnit_det_toBlocks₁₁

/-- Over `ℝ` the tangent and normal spaces are complementary. -/
example (F : Matrix ι κ ℝ) :
    IsCompl (tangentSpace F) (normalSpace F) := by
  apply _root_.Matrix.RankManifold.isCompl_tangentSpace_normalSpace

/-- The tangent cone of `{rank ≤ k}` at a matrix of rank exactly `k` is the tangent space. -/
example (F : Matrix ι κ ℝ) {k : ℕ} (hF : F.rank = k) :
    tangentConeAt ℝ {M : Matrix ι κ ℝ | M.rank ≤ k} F = (tangentSpace F : Set (Matrix ι κ ℝ)) := by
  apply _root_.Matrix.RankManifold.tangentConeAt_setOf_rank_le
  assumption

/-- **Local manifold structure.** Near a matrix `F` of rank exactly `k`, the set `{rank ≤ k}`
coincides with `{rank = k}`, and in linear coordinates `ℝ^(k(n+r-k)) × ℝ^((n-k)(r-k))` it is
the graph of a `C^∞` map on an open set: a smooth embedded submanifold of dimension
`k(n+r-k)` and codimension `(n-k)(r-k)`. -/
example (F : Matrix ι κ ℝ) {k : ℕ} (hF : F.rank = k) :
    ∃ (e : Matrix ι κ ℝ ≃L[ℝ]
        EuclideanSpace ℝ (Fin (k * (Fintype.card ι + Fintype.card κ - k))) ×
          EuclideanSpace ℝ (Fin ((Fintype.card ι - k) * (Fintype.card κ - k))))
      (U : Set (EuclideanSpace ℝ (Fin (k * (Fintype.card ι + Fintype.card κ - k)))))
      (g : EuclideanSpace ℝ (Fin (k * (Fintype.card ι + Fintype.card κ - k))) →
        EuclideanSpace ℝ (Fin ((Fintype.card ι - k) * (Fintype.card κ - k)))),
      IsOpen U ∧ (e F).1 ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
      ∃ V ∈ 𝓝 F, V ∩ {M | M.rank ≤ k} = V ∩ {M | M.rank = k} ∧
        V ∩ {M | M.rank = k} = V ∩ e ⁻¹' {p | p.1 ∈ U ∧ p.2 = g p.1} := by
  apply _root_.Matrix.RankManifold.exists_localGraph
  assumption

end Real

section Acceptance

variable {K : Type*} [Field K]

/-- Acceptance (`n = r = 2`, `k = 1`): the normal space has dimension `1` (codimension `1`)
and the tangent space has dimension `3`. -/
example (F : Matrix (Fin 2) (Fin 2) K)
    (hF : F.rank = 1) :
    Module.finrank K (normalSpace F) = 1 ∧ Module.finrank K (tangentSpace F) = 3 := by
  apply _root_.Matrix.RankManifold.finrank_normalSpace_tangentSpace_two_two_one
  assumption

/-- Non-vacuity of the acceptance instance: `!![1, 0; 0, 0]` has rank `1`. -/
example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K).rank = 1 := by
  apply _root_.Matrix.RankManifold.rank_two_two_one_example

end Acceptance

end RankManifoldSection

end MathlibExtTest.RankManifold
