/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# The local manifold structure of rank-`k` matrices

Let `F` be an `n × r` real matrix of rank exactly `k` (`n = card ι`, `r = card κ`).

* Block (Schur complement) coordinates, over any field: for `A` invertible,
  `rank [[A, B], [C, D]] = card m + rank (D - C A⁻¹ B)`, hence `[[A, B], [C, D]]` has rank
  `card m` iff `D - C A⁻¹ B = 0`, and rank `≤ card m` iff rank `= card m`
  (`Matrix.rank_fromBlocks_of_isUnit_det`, `Matrix.rank_fromBlocks_eq_card_iff`,
  `Matrix.rank_fromBlocks_le_card_iff`). A rank-`k` matrix has an invertible `k × k`
  submatrix, so its rows and columns can be permuted into this block form
  (`Matrix.exists_isUnit_det_submatrix_of_rank_eq`, `Matrix.exists_reindex_isUnit_det_toBlocks₁₁`).
* Local structure (real matrices): `{M | k ≤ rank M}` is open, so near `F` the sets
  `{rank ≤ k}` and `{rank = k}` coincide; on the open block chart where the top-left block is
  invertible, rank `≤ card m` iff rank `= card m` iff the Schur complement vanishes.
  `RankManifold.exists_localGraph`: near `F`, in linear coordinates
  `ℝ^(k(n+r-k)) × ℝ^((n-k)(r-k))`, `{rank ≤ k} = {rank = k}` is the graph of a `C^∞` map on
  an open set, i.e. a smooth embedded submanifold of dimension `k(n+r-k)`.
* Tangent and normal spaces: `RankManifold.tangentSpace F` is
  `{X | uᵀ X v = 0 whenever uᵀ F = 0 and F v = 0}` and `RankManifold.normalSpace F` is
  `{Y | Fᵀ Y = 0 ∧ Y Fᵀ = 0}`. Over any field they have dimensions `k(n+r-k)` and
  `(n-k)(r-k)`, and the normal space is exactly the trace-form orthogonal complement of the
  tangent space; over `ℝ` they are complementary, and the tangent cone of `{rank ≤ k}` at
  `F` is the tangent space.
* Endpoints: `k = 0` (`F = 0`, the locus is a point, the normal space is everything) and
  `k = min n r` (the locus is open, the normal space is zero) are covered by the same
  statements. For `n = r = 2`, `k = 1` the normal space has dimension `1` (codimension `1`).

## References

* The rank-`k` locus as a smooth submanifold via Schur-complement coordinates is standard;
  see e.g. J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2013, Ch. 5
  (regular level sets), applied to the block chart.
-/

@[expose] public section

open Matrix
open scoped Topology ContDiff

namespace Matrix

variable {K : Type*} [Field K]

/-- The rank of a block-diagonal matrix is the sum of the ranks of the diagonal blocks. -/
theorem rank_fromBlocks_zero₁₂_zero₂₁ {m n p q : Type*} [Fintype m] [Fintype n] [Fintype p]
    [Fintype q] (A : Matrix m n K) (D : Matrix p q K) :
    (fromBlocks A 0 0 D).rank = A.rank + D.rank := by
  classical
  let e₁ := LinearEquiv.sumArrowLequivProdArrow m p K K
  let e₂ := LinearEquiv.sumArrowLequivProdArrow n q K K
  have hcomp : (fromBlocks A 0 0 D).mulVecLin =
      e₁.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap D.mulVecLin) ∘ₗ e₂.toLinearMap := by
    apply LinearMap.ext
    intro x
    funext i
    cases i with
    | inl i => simp [e₁, e₂, fromBlocks_mulVec]; rfl
    | inr i => simp [e₁, e₂, fromBlocks_mulVec]; rfl
  rw [rank, rank, rank, hcomp, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearMap.range_prodMap, LinearEquiv.finrank_map_eq,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- A matrix has rank zero iff it is zero. -/
theorem rank_eq_zero_iff {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n K) :
    A.rank = 0 ↔ A = 0 := by
  classical
  constructor
  · intro h
    rw [rank, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
    ext i j
    have := congrArg (fun f => f (Pi.single j 1) i) h
    simpa [mulVecLin_apply, mulVec_single] using this
  · rintro rfl
    exact rank_zero

/-- **Schur rank additivity.** If the top-left block `A` is invertible, the rank of
`[[A, B], [C, D]]` is `card m` plus the rank of the Schur complement `D - C A⁻¹ B`. -/
theorem rank_fromBlocks_of_isUnit_det {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (A : Matrix m m K) (B : Matrix m q K) (C : Matrix p m K) (D : Matrix p q K)
    (hA : IsUnit A.det) :
    (fromBlocks A B C D).rank = Fintype.card m + (D - C * A⁻¹ * B).rank := by
  let _ := A.invertibleOfIsUnitDet hA
  have hL : IsUnit (fromBlocks 1 0 (C * ⅟A) 1 : Matrix (m ⊕ p) (m ⊕ p) K).det := by
    rw [det_fromBlocks_zero₁₂, det_one, det_one, mul_one]
    exact isUnit_one
  have hU : IsUnit (fromBlocks 1 (⅟A * B) 0 1 : Matrix (m ⊕ q) (m ⊕ q) K).det := by
    rw [det_fromBlocks_zero₂₁, det_one, det_one, mul_one]
    exact isUnit_one
  rw [fromBlocks_eq_of_invertible₁₁ A B C D, rank_mul_eq_left_of_isUnit_det _ _ hU,
    rank_mul_eq_right_of_isUnit_det _ _ hL, rank_fromBlocks_zero₁₂_zero₂₁,
    rank_of_isUnit A ((isUnit_iff_isUnit_det A).mpr hA), invOf_eq_nonsing_inv]

/-- **Schur-complement characterization.** With `A` invertible, `[[A, B], [C, D]]` has rank
`card m` iff `D - C A⁻¹ B = 0`. -/
theorem rank_fromBlocks_eq_card_iff {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (A : Matrix m m K) (B : Matrix m q K) (C : Matrix p m K) (D : Matrix p q K)
    (hA : IsUnit A.det) :
    (fromBlocks A B C D).rank = Fintype.card m ↔ D - C * A⁻¹ * B = 0 := by
  rw [rank_fromBlocks_of_isUnit_det A B C D hA, ← rank_eq_zero_iff]
  omega

/-- With `A` invertible, `[[A, B], [C, D]]` has rank at most `card m` iff `D - C A⁻¹ B = 0`. -/
theorem rank_fromBlocks_le_card_iff {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (A : Matrix m m K) (B : Matrix m q K) (C : Matrix p m K) (D : Matrix p q K)
    (hA : IsUnit A.det) :
    (fromBlocks A B C D).rank ≤ Fintype.card m ↔ D - C * A⁻¹ * B = 0 := by
  rw [rank_fromBlocks_of_isUnit_det A B C D hA, ← rank_eq_zero_iff]
  omega

section MinorHelpers

private theorem exists_linearIndependent_row_of_rank_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (G : Matrix ι κ K) (hG : G.rank = k) :
    ∃ r : Fin k ↪ ι, LinearIndependent K (G.row ∘ r) := by
  classical
  obtain ⟨ι', a, ha, hspan, hli⟩ := exists_linearIndependent' K G.row
  have : Fintype ι' := Fintype.ofInjective a ha
  have hcard : Fintype.card ι' = k := by
    rw [← hG, rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  let e : Fin k ≃ ι' := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨⟨a ∘ e, ha.comp e.injective⟩, hli.comp e e.injective⟩

private theorem exists_linearIndependent_row_of_le_rank {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (G : Matrix ι κ K) (hG : k ≤ G.rank) :
    ∃ r : Fin k ↪ ι, LinearIndependent K (G.row ∘ r) := by
  obtain ⟨r, hr⟩ := exists_linearIndependent_row_of_rank_eq G rfl
  exact ⟨(Fin.castLEEmb hG).trans r, hr.comp _ (Fin.castLEEmb hG).injective⟩

/-- A matrix of rank at least `k` has an invertible `k × k` submatrix. -/
private theorem exists_isUnit_det_submatrix_of_le_rank {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (F : Matrix ι κ K) (hF : k ≤ F.rank) :
    ∃ (r : Fin k ↪ ι) (c : Fin k ↪ κ), IsUnit (F.submatrix r c).det := by
  classical
  obtain ⟨c, hc⟩ := exists_linearIndependent_row_of_le_rank (k := k) Fᵀ
    (by rw [rank_transpose]; exact hF)
  set G : Matrix ι (Fin k) K := F.submatrix id c with hGdef
  have hGt : Gᵀ.row = Fᵀ.row ∘ c := by
    funext j i
    rfl
  have hG : G.rank = k := by
    rw [← rank_transpose, LinearIndependent.rank_matrix (hGt ▸ hc), Fintype.card_fin]
  obtain ⟨r, hr⟩ := exists_linearIndependent_row_of_rank_eq G hG
  refine ⟨r, c, ?_⟩
  have hrow : (F.submatrix r c).row = G.row ∘ r := by
    funext i j
    rfl
  rw [← isUnit_iff_isUnit_det, ← linearIndependent_row_iff_isUnit, hrow]
  exact hr

end MinorHelpers

/-- A matrix of rank `k` has an invertible `k × k` submatrix (a nonzero `k`-minor). -/
theorem exists_isUnit_det_submatrix_of_rank_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {k : ℕ}
    (F : Matrix ι κ K) (hF : F.rank = k) :
    ∃ (r : Fin k ↪ ι) (c : Fin k ↪ κ), IsUnit (F.submatrix r c).det := by
  exact exists_isUnit_det_submatrix_of_le_rank F hF.ge

/-- An embedding `Fin k ↪ Fin n` extends to a splitting `Fin n ≃ Fin k ⊕ Fin (n - k)`. -/
private theorem exists_equiv_sum_symm_inl_fin {n k : ℕ} (r : Fin k ↪ Fin n) :
    ∃ e : Fin n ≃ Fin k ⊕ Fin (n - k), ∀ i, e.symm (Sum.inl i) = r i := by
  classical
  have hcard : Fintype.card {a // a ∉ Set.range r} = n - k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Set.card_range_of_injective r.injective,
      Fintype.card_fin]
  let e : Fin n ≃ Fin k ⊕ Fin (n - k) :=
    (Equiv.sumCompl (· ∈ Set.range r)).symm.trans
      ((Equiv.ofInjective r r.injective).symm.sumCongr (Fintype.equivFinOfCardEq hcard))
  refine ⟨e, fun i => ?_⟩
  simp [e, Equiv.sumCompl_apply_inl]

/-- The rows and columns of an `n × r` matrix of rank `k` can be permuted into block form
`[[A, B], [C, D]]` with invertible `k × k` block `A`. -/
theorem exists_reindex_isUnit_det_toBlocks₁₁ {n r k : ℕ} (F : Matrix (Fin n) (Fin r) K)
    (hF : F.rank = k) :
    ∃ (e₁ : Fin n ≃ Fin k ⊕ Fin (n - k)) (e₂ : Fin r ≃ Fin k ⊕ Fin (r - k)),
      IsUnit (reindex e₁ e₂ F).toBlocks₁₁.det := by
  obtain ⟨ρ, γ, h⟩ := exists_isUnit_det_submatrix_of_rank_eq F hF
  obtain ⟨e₁, he₁⟩ := exists_equiv_sum_symm_inl_fin ρ
  obtain ⟨e₂, he₂⟩ := exists_equiv_sum_symm_inl_fin γ
  refine ⟨e₁, e₂, ?_⟩
  have hblk : (reindex e₁ e₂ F).toBlocks₁₁ = F.submatrix ρ γ := by
    ext i j
    simp [toBlocks₁₁, he₁, he₂]
  rw [hblk]
  exact h

end Matrix

namespace Matrix.RankManifold

section Defs

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The tangent space at `F` to the locus of matrices of rank `F.rank`:
`{X | uᵀ X v = 0 for all u with uᵀ F = 0 and all v with F v = 0}`. -/
def tangentSpace (F : Matrix ι κ K) : Submodule K (Matrix ι κ K) where
  carrier := {X | ∀ (u : ι → K) (v : κ → K), u ᵥ* F = 0 → F *ᵥ v = 0 → u ⬝ᵥ (X *ᵥ v) = 0}
  add_mem' {X Y} hX hY u v hu hv := by
    rw [add_mulVec, dotProduct_add, hX u v hu hv, hY u v hu hv, add_zero]
  zero_mem' u v _ _ := by simp
  smul_mem' c X hX u v hu hv := by
    rw [smul_mulVec, dotProduct_smul, hX u v hu hv, smul_zero]

/-- The normal space at `F`: matrices whose columns lie in the left kernel of `F` and whose
rows lie in the kernel of `F`, i.e. `{Y | Fᵀ Y = 0 ∧ Y Fᵀ = 0}`. -/
def normalSpace (F : Matrix ι κ K) : Submodule K (Matrix ι κ K) where
  carrier := {Y | Fᵀ * Y = 0 ∧ Y * Fᵀ = 0}
  add_mem' {X Y} hX hY := ⟨by rw [Matrix.mul_add, hX.1, hY.1, add_zero],
    by rw [Matrix.add_mul, hX.2, hY.2, add_zero]⟩
  zero_mem' := ⟨Matrix.mul_zero _, Matrix.zero_mul _⟩
  smul_mem' c X hX := ⟨by rw [Matrix.mul_smul, hX.1, smul_zero],
    by rw [Matrix.smul_mul, hX.2, smul_zero]⟩

end Defs

section Algebra

variable {K : Type*} [Field K]

/-- Block chart, part 1: if the top-left block is invertible, rank `≤ card m` iff
rank `= card m`. -/
theorem rank_le_iff_rank_eq_of_isUnit_det_toBlocks₁₁ {m p q : Type*} [Fintype m] [Fintype p]
    [Fintype q] [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (M : Matrix (m ⊕ p) (m ⊕ q) K) (hM : IsUnit M.toBlocks₁₁.det) :
    M.rank ≤ Fintype.card m ↔ M.rank = Fintype.card m := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, M = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks M).symm⟩
  rw [toBlocks_fromBlocks₁₁] at hM
  rw [rank_fromBlocks_le_card_iff A B C D hM, rank_fromBlocks_eq_card_iff A B C D hM]

/-- Block chart, part 2: if the top-left block is invertible, rank `= card m` iff the Schur
complement vanishes. -/
theorem rank_eq_iff_toBlocks₂₂_eq_of_isUnit_det_toBlocks₁₁ {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q] [DecidableEq m] [DecidableEq p] [DecidableEq q]
    (M : Matrix (m ⊕ p) (m ⊕ q) K) (hM : IsUnit M.toBlocks₁₁.det) :
    M.rank = Fintype.card m ↔ M.toBlocks₂₂ = M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, M = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks M).symm⟩
  rw [toBlocks_fromBlocks₁₁] at hM
  rw [rank_fromBlocks_eq_card_iff A B C D hM, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂,
    toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, sub_eq_zero]

/-- Dimension count: `k(n+r-k) + (n-k)(r-k) = nr` for `k ≤ n` and `k ≤ r`. -/
theorem dim_add_codim {n r k : ℕ} (hn : k ≤ n) (hr : k ≤ r) :
    k * (n + r - k) + (n - k) * (r - k) = n * r := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hr
  have h1 : k + a + (k + b) - k = k + a + b := by omega
  rw [h1, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  ring

section Aux

private theorem mem_tangentSpace {ι κ : Type*} [Fintype ι] [Fintype κ] {F X : Matrix ι κ K} :
    X ∈ tangentSpace F ↔
      ∀ (u : ι → K) (v : κ → K), u ᵥ* F = 0 → F *ᵥ v = 0 → u ⬝ᵥ (X *ᵥ v) = 0 :=
  Iff.rfl

private theorem mem_normalSpace {ι κ : Type*} [Fintype ι] [Fintype κ] {F Y : Matrix ι κ K} :
    Y ∈ normalSpace F ↔ Fᵀ * Y = 0 ∧ Y * Fᵀ = 0 :=
  Iff.rfl

variable {ι κ ι' κ' : Type*} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ι'] [DecidableEq κ']

private theorem mul_eq_zero_iff_of_mul_eq_one_left {l m n : Type*} [Fintype l] [Fintype m] [DecidableEq l]
    {A : Matrix m l K} {A' : Matrix l m K} (h : A' * A = 1) (M : Matrix l n K) :
    A * M = 0 ↔ M = 0 :=
  ⟨fun hM => by rw [← Matrix.one_mul M, ← h, Matrix.mul_assoc, hM, Matrix.mul_zero],
    fun hM => by rw [hM, Matrix.mul_zero]⟩

private theorem mul_eq_zero_iff_of_mul_eq_one_right {l m n : Type*} [Fintype l] [Fintype n] [DecidableEq n]
    {B : Matrix n l K} {B' : Matrix l n K} (h : B * B' = 1) (M : Matrix m n K) :
    M * B = 0 ↔ M = 0 :=
  ⟨fun hM => by rw [← Matrix.mul_one M, ← h, ← Matrix.mul_assoc, hM, Matrix.zero_mul],
    fun hM => by rw [hM, Matrix.zero_mul]⟩

private theorem mem_tangentSpace_mul_mul_iff (F : Matrix ι κ K)
    {P : Matrix ι' ι K} {P' : Matrix ι ι' K} {Q : Matrix κ κ' K} {Q' : Matrix κ' κ K}
    (hP : P * P' = 1) (hP' : P' * P = 1) (hQ : Q * Q' = 1) (hQ' : Q' * Q = 1)
    (X : Matrix ι' κ' K) :
    X ∈ tangentSpace (P * F * Q) ↔ P' * X * Q' ∈ tangentSpace F := by
  simp only [mem_tangentSpace]
  constructor
  · intro hX u v hu hv
    have h1 : (u ᵥ* P') ᵥ* (P * F * Q) = 0 := by
      rw [vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP', Matrix.one_mul,
        ← vecMul_vecMul, hu, zero_vecMul]
    have h2 : (P * F * Q) *ᵥ (Q' *ᵥ v) = 0 := by
      rw [mulVec_mulVec, Matrix.mul_assoc, hQ, Matrix.mul_one, ← mulVec_mulVec, hv, mulVec_zero]
    have h3 := hX (u ᵥ* P') (Q' *ᵥ v) h1 h2
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec]
    exact h3
  · intro hX u v hu hv
    have h1 : (u ᵥ* P) ᵥ* F = 0 := by
      have h : u ᵥ* (P * F * Q) ᵥ* Q' = 0 := by rw [hu, zero_vecMul]
      rwa [vecMul_vecMul, Matrix.mul_assoc, hQ, Matrix.mul_one, ← vecMul_vecMul] at h
    have h2 : F *ᵥ (Q *ᵥ v) = 0 := by
      have h : P' *ᵥ ((P * F * Q) *ᵥ v) = 0 := by rw [hv, mulVec_zero]
      rwa [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP', Matrix.one_mul,
        ← mulVec_mulVec] at h
    have h3 := hX (u ᵥ* P) (Q *ᵥ v) h1 h2
    have e1 : (P' * X * Q') *ᵥ (Q *ᵥ v) = P' *ᵥ (X *ᵥ v) := by
      rw [mulVec_mulVec, Matrix.mul_assoc, hQ', Matrix.mul_one, ← mulVec_mulVec]
    rw [e1, dotProduct_mulVec, vecMul_vecMul, hP, vecMul_one] at h3
    exact h3

private theorem mem_normalSpace_mul_mul_iff (F : Matrix ι κ K)
    {P : Matrix ι' ι K} {P' : Matrix ι ι' K} {Q : Matrix κ κ' K} {Q' : Matrix κ' κ K}
    (hP : P * P' = 1) (hP' : P' * P = 1) (hQ : Q * Q' = 1) (hQ' : Q' * Q = 1)
    (Y : Matrix ι' κ' K) :
    Y ∈ normalSpace (P * F * Q) ↔ Pᵀ * Y * Qᵀ ∈ normalSpace F := by
  have tP : P'ᵀ * Pᵀ = 1 := by rw [← transpose_mul, hP, transpose_one]
  have tP' : Pᵀ * P'ᵀ = 1 := by rw [← transpose_mul, hP', transpose_one]
  have tQ : Q'ᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQ, transpose_one]
  have tQ' : Qᵀ * Q'ᵀ = 1 := by rw [← transpose_mul, hQ', transpose_one]
  simp only [mem_normalSpace, transpose_mul, Matrix.mul_assoc]
  have e2 : Fᵀ * (Pᵀ * (Y * Qᵀ)) = Fᵀ * (Pᵀ * Y) * Qᵀ := by simp only [Matrix.mul_assoc]
  have e3 : Y * (Qᵀ * (Fᵀ * Pᵀ)) = Y * (Qᵀ * Fᵀ) * Pᵀ := by simp only [Matrix.mul_assoc]
  rw [e2, e3, mul_eq_zero_iff_of_mul_eq_one_left tQ, mul_eq_zero_iff_of_mul_eq_one_right tQ',
    mul_eq_zero_iff_of_mul_eq_one_right tP', mul_eq_zero_iff_of_mul_eq_one_left tP]

omit [DecidableEq ι'] [DecidableEq κ'] in
private theorem trace_change {P : Matrix ι' ι K} {P' : Matrix ι ι' K} {Q : Matrix κ κ' K}
    {Q' : Matrix κ' κ K} (hP' : P' * P = 1) (hQ : Q * Q' = 1) (X Y : Matrix ι κ K) :
    ((P * X * Q)ᵀ * (P'ᵀ * Y * Q'ᵀ)).trace = (Xᵀ * Y).trace := by
  have tP' : Pᵀ * P'ᵀ = 1 := by rw [← transpose_mul, hP', transpose_one]
  have tQ : Q'ᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQ, transpose_one]
  have e : (P * X * Q)ᵀ * (P'ᵀ * Y * Q'ᵀ) = Qᵀ * (Xᵀ * Y * Q'ᵀ) := by
    simp only [transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pᵀ, tP', Matrix.one_mul]
  rw [e, trace_mul_comm, Matrix.mul_assoc, Matrix.mul_assoc, tQ, Matrix.mul_one]

/-- The linear equivalence `X ↦ P X Q` with inverse `X ↦ P' X Q'`. -/
private def changeEquiv (P : Matrix ι' ι K) (P' : Matrix ι ι' K) (Q : Matrix κ κ' K)
    (Q' : Matrix κ' κ K) (hP : P * P' = 1) (hP' : P' * P = 1) (hQ : Q * Q' = 1)
    (hQ' : Q' * Q = 1) : Matrix ι κ K ≃ₗ[K] Matrix ι' κ' K where
  toFun X := P * X * Q
  invFun X := P' * X * Q'
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
  left_inv X := by
    simp only
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hQ, Matrix.mul_one, ← Matrix.mul_assoc, hP',
      Matrix.one_mul]
  right_inv X := by
    simp only
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hQ', Matrix.mul_one, ← Matrix.mul_assoc, hP,
      Matrix.one_mul]

private theorem finrank_tangentSpace_mul_mul (F : Matrix ι κ K)
    {P : Matrix ι' ι K} {P' : Matrix ι ι' K} {Q : Matrix κ κ' K} {Q' : Matrix κ' κ K}
    (hP : P * P' = 1) (hP' : P' * P = 1) (hQ : Q * Q' = 1) (hQ' : Q' * Q = 1) :
    Module.finrank K (tangentSpace (P * F * Q)) = Module.finrank K (tangentSpace F) := by
  have h : tangentSpace (P * F * Q) = (tangentSpace F).map
      (changeEquiv P P' Q Q' hP hP' hQ hQ' : Matrix ι κ K →ₗ[K] Matrix ι' κ' K) := by
    ext X
    rw [Submodule.mem_map_equiv]
    exact mem_tangentSpace_mul_mul_iff F hP hP' hQ hQ' X
  rw [h, LinearEquiv.finrank_map_eq]

private theorem finrank_normalSpace_mul_mul (F : Matrix ι κ K)
    {P : Matrix ι' ι K} {P' : Matrix ι ι' K} {Q : Matrix κ κ' K} {Q' : Matrix κ' κ K}
    (hP : P * P' = 1) (hP' : P' * P = 1) (hQ : Q * Q' = 1) (hQ' : Q' * Q = 1) :
    Module.finrank K (normalSpace (P * F * Q)) = Module.finrank K (normalSpace F) := by
  have tP : P'ᵀ * Pᵀ = 1 := by rw [← transpose_mul, hP, transpose_one]
  have tP' : Pᵀ * P'ᵀ = 1 := by rw [← transpose_mul, hP', transpose_one]
  have tQ : Q'ᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQ, transpose_one]
  have tQ' : Qᵀ * Q'ᵀ = 1 := by rw [← transpose_mul, hQ', transpose_one]
  have h : normalSpace (P * F * Q) =
      (normalSpace F).map
        (changeEquiv P'ᵀ Pᵀ Q'ᵀ Qᵀ tP tP' tQ tQ' : Matrix ι κ K →ₗ[K] Matrix ι' κ' K) := by
    ext Y
    rw [Submodule.mem_map_equiv]
    exact mem_normalSpace_mul_mul_iff F hP hP' hQ hQ' Y
  rw [h, LinearEquiv.finrank_map_eq]

end Aux

section NormalForm

private theorem exists_equiv_sum_symm_inl' {ι : Type*} [Fintype ι] {k : ℕ} (r : Fin k ↪ ι) :
    ∃ e : ι ≃ Fin k ⊕ Fin (Fintype.card ι - k), ∀ i, e.symm (Sum.inl i) = r i := by
  classical
  have hcard : Fintype.card {a // a ∉ Set.range r} = Fintype.card ι - k := by
    rw [Fintype.card_subtype_compl, Set.card_range_of_injective r.injective, Fintype.card_fin]
  let e : ι ≃ Fin k ⊕ Fin (Fintype.card ι - k) :=
    (Equiv.sumCompl (· ∈ Set.range r)).symm.trans
      ((Equiv.ofInjective r r.injective).symm.sumCongr (Fintype.equivFinOfCardEq hcard))
  exact ⟨e, fun i => by simp [e, Equiv.sumCompl_apply_inl]⟩

private theorem exists_normalForm {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : Matrix ι κ K) {k : ℕ} (hF : F.rank = k) :
    ∃ (P : Matrix (Fin k ⊕ Fin (Fintype.card ι - k)) ι K)
      (P' : Matrix ι (Fin k ⊕ Fin (Fintype.card ι - k)) K)
      (Q : Matrix κ (Fin k ⊕ Fin (Fintype.card κ - k)) K)
      (Q' : Matrix (Fin k ⊕ Fin (Fintype.card κ - k)) κ K),
      P * P' = 1 ∧ P' * P = 1 ∧ Q * Q' = 1 ∧ Q' * Q = 1 ∧
        P * F * Q = fromBlocks 1 0 0 0 := by
  classical
  obtain ⟨r, c, hrc⟩ := exists_isUnit_det_submatrix_of_rank_eq F hF
  obtain ⟨e₁, he₁⟩ := exists_equiv_sum_symm_inl' r
  obtain ⟨e₂, he₂⟩ := exists_equiv_sum_symm_inl' c
  set G := reindex e₁ e₂ F with hG
  have hA : G.toBlocks₁₁ = F.submatrix r c := by
    ext i j
    simp [G, toBlocks₁₁, he₁, he₂]
  have hAu : IsUnit G.toBlocks₁₁.det := hA ▸ hrc
  have hGrank : G.rank = Fintype.card (Fin k) := by
    rw [hG, rank_reindex, hF, Fintype.card_fin]
  have hD := (rank_eq_iff_toBlocks₂₂_eq_of_isUnit_det_toBlocks₁₁ G hAu).mp hGrank
  set A := G.toBlocks₁₁ with hAdef
  set B := G.toBlocks₁₂ with hBdef
  set C := G.toBlocks₂₁ with hCdef
  set D := G.toBlocks₂₂ with hDdef
  have hGblk : G = fromBlocks A B C D := (fromBlocks_toBlocks G).symm
  let P₀ : Matrix (Fin k ⊕ Fin (Fintype.card ι - k)) ι K := (1 : Matrix ι ι K).submatrix e₁.symm id
  let P₀' : Matrix ι (Fin k ⊕ Fin (Fintype.card ι - k)) K :=
    (1 : Matrix ι ι K).submatrix id e₁.symm
  let Q₀ : Matrix κ (Fin k ⊕ Fin (Fintype.card κ - k)) K := (1 : Matrix κ κ K).submatrix id e₂.symm
  let Q₀' : Matrix (Fin k ⊕ Fin (Fintype.card κ - k)) κ K :=
    (1 : Matrix κ κ K).submatrix e₂.symm id
  have hP₀ : P₀ * P₀' = 1 := by
    ext a b
    simp [P₀, P₀', Matrix.mul_apply, Matrix.one_apply]
  have hP₀' : P₀' * P₀ = 1 := by
    simp only [P₀, P₀']
    rw [submatrix_mul_equiv, Matrix.one_mul, submatrix_id_id]
  have hQ₀ : Q₀ * Q₀' = 1 := by
    simp only [Q₀, Q₀']
    rw [submatrix_mul_equiv, Matrix.one_mul, submatrix_id_id]
  have hQ₀' : Q₀' * Q₀ = 1 := by
    ext a b
    simp [Q₀, Q₀', Matrix.mul_apply, Matrix.one_apply]
  have hPFQ : P₀ * F * Q₀ = G := by
    ext a b
    simp [P₀, Q₀, G, Matrix.mul_apply, Matrix.one_apply]
  have hinv : A⁻¹ * A = 1 := nonsing_inv_mul A hAu
  have hinv' : A * A⁻¹ = 1 := mul_nonsing_inv A hAu
  let L : Matrix (Fin k ⊕ Fin (Fintype.card ι - k)) (Fin k ⊕ Fin (Fintype.card ι - k)) K :=
    fromBlocks A⁻¹ 0 (-(C * A⁻¹)) 1
  let L' : Matrix (Fin k ⊕ Fin (Fintype.card ι - k)) (Fin k ⊕ Fin (Fintype.card ι - k)) K :=
    fromBlocks A 0 C 1
  let R : Matrix (Fin k ⊕ Fin (Fintype.card κ - k)) (Fin k ⊕ Fin (Fintype.card κ - k)) K :=
    fromBlocks 1 (-(A⁻¹ * B)) 0 1
  let R' : Matrix (Fin k ⊕ Fin (Fintype.card κ - k)) (Fin k ⊕ Fin (Fintype.card κ - k)) K :=
    fromBlocks 1 (A⁻¹ * B) 0 1
  have hL : L * L' = 1 := by
    simp [L, L', fromBlocks_multiply, hinv, Matrix.mul_assoc]
  have hL' : L' * L = 1 := by
    simp [L, L', fromBlocks_multiply, hinv']
  have hR : R * R' = 1 := by
    simp [R, R', fromBlocks_multiply]
  have hR' : R' * R = 1 := by
    simp [R, R', fromBlocks_multiply]
  have hLGR : L * G * R = fromBlocks 1 0 0 0 := by
    rw [hGblk, hD]
    simp [L, R, fromBlocks_multiply, hinv, Matrix.mul_assoc]
  refine ⟨L * P₀, P₀' * L', Q₀ * R, R' * Q₀', ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P₀, hP₀, Matrix.one_mul, hL]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L', hL', Matrix.one_mul, hP₀']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, hR, Matrix.one_mul, hQ₀]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₀', hQ₀', Matrix.one_mul, hR']
  · rw [show L * P₀ * F * (Q₀ * R) = L * (P₀ * F * Q₀) * R by simp only [Matrix.mul_assoc],
      hPFQ, hLGR]

end NormalForm

section BlockModel

variable {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
  [DecidableEq m] [DecidableEq p] [DecidableEq q]

private theorem mem_tangentSpace_fromBlocks_one (X : Matrix (m ⊕ p) (m ⊕ q) K) :
    X ∈ tangentSpace (fromBlocks (1 : Matrix m m K) 0 0 0) ↔ X.toBlocks₂₂ = 0 := by
  rw [mem_tangentSpace]
  constructor
  · intro hX
    ext i j
    have hu : Pi.single (Sum.inr i) (1 : K) ᵥ*
        fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K) = 0 := by
      ext a
      cases a <;> simp
    have hv : fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K) *ᵥ
        Pi.single (Sum.inr j) (1 : K) = 0 := by
      ext a
      cases a <;> simp
    have h := hX _ _ hu hv
    simpa [mulVec_single, single_dotProduct, toBlocks₂₂] using h
  · intro hX u v hu hv
    have hu' : ∀ a, u (Sum.inl a) = 0 := fun a => by
      have h := congrFun hu (Sum.inl a)
      simpa [vecMul_fromBlocks] using h
    have hv' : ∀ b, v (Sum.inl b) = 0 := fun b => by
      have h := congrFun hv (Sum.inl b)
      simpa [fromBlocks_mulVec] using h
    have hX' : ∀ i j, X (Sum.inr i) (Sum.inr j) = 0 := fun i j => congrFun (congrFun hX i) j
    simp [dotProduct, mulVec, Fintype.sum_sum_type, hu', hv', hX']

omit [DecidableEq p] [DecidableEq q] in
private theorem mem_normalSpace_fromBlocks_one (Y : Matrix (m ⊕ p) (m ⊕ q) K) :
    Y ∈ normalSpace (fromBlocks (1 : Matrix m m K) 0 0 0) ↔ fromBlocks 0 0 0 Y.toBlocks₂₂ = Y := by
  rw [mem_normalSpace]
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, Y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Y).symm⟩
  have h1 : (fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K))ᵀ * fromBlocks A B C D =
      fromBlocks A B 0 0 := by
    simp [fromBlocks_transpose, fromBlocks_multiply]
  have h2 : fromBlocks A B C D * (fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K))ᵀ =
      fromBlocks A 0 C 0 := by
    simp [fromBlocks_transpose, fromBlocks_multiply]
  rw [h1, h2, toBlocks_fromBlocks₂₂, ← fromBlocks_zero, fromBlocks_inj, ← fromBlocks_zero,
    fromBlocks_inj, fromBlocks_inj]
  constructor
  · rintro ⟨⟨hA, hB, -, -⟩, ⟨-, -, hC, -⟩⟩
    exact ⟨hA.symm, hB.symm, hC.symm, rfl⟩
  · rintro ⟨hA, hB, hC, -⟩
    exact ⟨⟨hA.symm, hB.symm, rfl, rfl⟩, ⟨hA.symm, rfl, hC.symm, rfl⟩⟩

/-- `toBlocks₂₂` as a linear map. -/
private def toBlocks₂₂ₗ : Matrix (m ⊕ p) (m ⊕ q) K →ₗ[K] Matrix p q K where
  toFun := toBlocks₂₂
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- `Z ↦ fromBlocks 0 0 0 Z` as a linear map. -/
private def fromBlocks₂₂ₗ : Matrix p q K →ₗ[K] Matrix (m ⊕ p) (m ⊕ q) K where
  toFun Z := fromBlocks 0 0 0 Z
  map_add' Z W := by simp [fromBlocks_add]
  map_smul' c Z := by simp [fromBlocks_smul]

private theorem finrank_tangentSpace_fromBlocks_one :
    Module.finrank K (tangentSpace (fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K))) +
      Fintype.card p * Fintype.card q =
      (Fintype.card m + Fintype.card p) * (Fintype.card m + Fintype.card q) := by
  have hker : tangentSpace (fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K)) =
      LinearMap.ker (toBlocks₂₂ₗ (K := K) (m := m) (p := p) (q := q)) := by
    ext X
    rw [mem_tangentSpace_fromBlocks_one, LinearMap.mem_ker]
    rfl
  have hrange : LinearMap.range (toBlocks₂₂ₗ (K := K) (m := m) (p := p) (q := q)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro Z
    exact ⟨fromBlocks 0 0 0 Z, toBlocks_fromBlocks₂₂ _ _ _ _⟩
  have h := LinearMap.finrank_range_add_finrank_ker
    (toBlocks₂₂ₗ (K := K) (m := m) (p := p) (q := q))
  rw [hrange, finrank_top, ← hker, Module.finrank_matrix, Module.finrank_matrix,
    Module.finrank_self, Fintype.card_sum, Fintype.card_sum] at h
  simpa [add_comm] using h

omit [DecidableEq p] [DecidableEq q] in
private theorem finrank_normalSpace_fromBlocks_one :
    Module.finrank K (normalSpace (fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K))) =
      Fintype.card p * Fintype.card q := by
  have hrange : normalSpace (fromBlocks (1 : Matrix m m K) 0 0 (0 : Matrix p q K)) =
      LinearMap.range (fromBlocks₂₂ₗ (K := K) (m := m) (p := p) (q := q)) := by
    ext Y
    rw [mem_normalSpace_fromBlocks_one, LinearMap.mem_range]
    constructor
    · intro h
      exact ⟨Y.toBlocks₂₂, h⟩
    · rintro ⟨Z, rfl⟩
      rfl
  have hinj : Function.Injective (fromBlocks₂₂ₗ (K := K) (m := m) (p := p) (q := q)) := by
    intro Z W h
    have h' := congrArg toBlocks₂₂ h
    simpa [fromBlocks₂₂ₗ] using h'
  rw [hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_matrix, Module.finrank_self,
    mul_one]

private theorem trace_eq_zero_fromBlocks_one {X Y : Matrix (m ⊕ p) (m ⊕ q) K}
    (hX : X ∈ tangentSpace (fromBlocks (1 : Matrix m m K) 0 0 0))
    (hY : Y ∈ normalSpace (fromBlocks (1 : Matrix m m K) 0 0 0)) :
    (Xᵀ * Y).trace = 0 := by
  rw [mem_tangentSpace_fromBlocks_one] at hX
  rw [mem_normalSpace_fromBlocks_one] at hY
  rw [← hY, ← fromBlocks_toBlocks X, hX]
  simp [fromBlocks_transpose, fromBlocks_multiply, Matrix.trace, Fintype.sum_sum_type]

end BlockModel

section TangentMembers

private theorem mul_mem_tangentSpace {ι κ : Type*} [Fintype ι] [Fintype κ] (F : Matrix ι κ K)
    (Z : Matrix κ κ K) : F * Z ∈ tangentSpace F := by
  intro u v hu _
  rw [← mulVec_mulVec, dotProduct_mulVec, hu, zero_dotProduct]

private theorem mul_mem_tangentSpace' {ι κ : Type*} [Fintype ι] [Fintype κ] (F : Matrix ι κ K)
    (Z : Matrix ι ι K) : Z * F ∈ tangentSpace F := by
  intro u v _ hv
  rw [← mulVec_mulVec, hv, mulVec_zero, dotProduct_zero]

end TangentMembers

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The tangent space at a rank-`k` matrix has dimension `k(n+r-k)`. -/
theorem finrank_tangentSpace (F : Matrix ι κ K) {k : ℕ} (hF : F.rank = k) :
    Module.finrank K (tangentSpace F) = k * (Fintype.card ι + Fintype.card κ - k) := by
  classical
  obtain ⟨P, P', Q, Q', hP, hP', hQ, hQ', hPFQ⟩ := exists_normalForm F hF
  have hk1 : k ≤ Fintype.card ι := hF ▸ rank_le_card_height F
  have hk2 : k ≤ Fintype.card κ := hF ▸ rank_le_card_width F
  have h := finrank_tangentSpace_fromBlocks_one (K := K) (m := Fin k)
    (p := Fin (Fintype.card ι - k)) (q := Fin (Fintype.card κ - k))
  rw [← hPFQ, finrank_tangentSpace_mul_mul F hP hP' hQ hQ'] at h
  simp only [Fintype.card_fin, Nat.add_sub_cancel' hk1, Nat.add_sub_cancel' hk2] at h
  have hd := dim_add_codim hk1 hk2
  omega

/-- The normal space at a rank-`k` matrix has dimension `(n-k)(r-k)`. -/
theorem finrank_normalSpace (F : Matrix ι κ K) {k : ℕ} (hF : F.rank = k) :
    Module.finrank K (normalSpace F) = (Fintype.card ι - k) * (Fintype.card κ - k) := by
  classical
  obtain ⟨P, P', Q, Q', hP, hP', hQ, hQ', hPFQ⟩ := exists_normalForm F hF
  rw [← finrank_normalSpace_mul_mul F hP hP' hQ hQ', hPFQ, finrank_normalSpace_fromBlocks_one,
    Fintype.card_fin, Fintype.card_fin]

/-- The normal space is the orthogonal complement of the tangent space for the trace form
`(X, Y) ↦ trace (Xᵀ Y)` (the Frobenius inner product over `ℝ`). -/
theorem mem_normalSpace_iff (F Y : Matrix ι κ K) :
    Y ∈ normalSpace F ↔ ∀ X ∈ tangentSpace F, (Xᵀ * Y).trace = 0 := by
  classical
  constructor
  · intro hY X hX
    obtain ⟨P, P', Q, Q', hP, hP', hQ, hQ', hPFQ⟩ := exists_normalForm F rfl
    have hX0 : P * X * Q ∈ tangentSpace (P * F * Q) := by
      rw [mem_tangentSpace_mul_mul_iff F hP hP' hQ hQ']
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.mul_assoc, hQ,
        Matrix.mul_one]
    have hY0 : P'ᵀ * Y * Q'ᵀ ∈ normalSpace (P * F * Q) := by
      rw [mem_normalSpace_mul_mul_iff F hP hP' hQ hQ']
      have tP' : Pᵀ * P'ᵀ = 1 := by rw [← transpose_mul, hP', transpose_one]
      have tQ : Q'ᵀ * Qᵀ = 1 := by rw [← transpose_mul, hQ, transpose_one]
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, tP', Matrix.one_mul, Matrix.mul_assoc, tQ,
        Matrix.mul_one]
    rw [hPFQ] at hX0 hY0
    rw [← trace_change hP' hQ X Y]
    exact trace_eq_zero_fromBlocks_one hX0 hY0
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      have h1 := h (F * single i j 1) (mul_mem_tangentSpace F _)
      rw [transpose_mul, transpose_single, Matrix.mul_assoc, trace_single_mul, one_smul] at h1
      exact h1
    · ext i j
      have h1 := h (single i j 1 * F) (mul_mem_tangentSpace' F _)
      rw [transpose_mul, transpose_single, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
        trace_single_mul, one_smul] at h1
      exact h1

end Algebra

section Real

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Lower semicontinuity of rank: `{M | k ≤ rank M}` is open. -/
theorem isOpen_setOf_le_rank (k : ℕ) : IsOpen {M : Matrix ι κ ℝ | k ≤ M.rank} := by
  classical
  have h : {M : Matrix ι κ ℝ | k ≤ M.rank} =
      ⋃ (r : Fin k ↪ ι) (c : Fin k ↪ κ), {M | (M.submatrix r c).det ≠ 0} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hM
      obtain ⟨r, c, h⟩ := exists_isUnit_det_submatrix_of_le_rank M hM
      exact ⟨r, c, h.ne_zero⟩
    · rintro ⟨r, c, h⟩
      calc k = (M.submatrix r c).rank := by
            rw [rank_of_isUnit _ ((isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h)),
              Fintype.card_fin]
        _ ≤ M.rank := rank_submatrix_le M r c
  rw [h]
  refine isOpen_iUnion fun r => isOpen_iUnion fun c => ?_
  exact isOpen_ne_fun ((continuous_id.matrix_submatrix r c).matrix_det) continuous_const

/-- Near `F`, rank at most `rank F` is the same as rank exactly `rank F`. -/
theorem eventually_rank_le_iff_rank_eq (F : Matrix ι κ ℝ) :
    ∀ᶠ M in 𝓝 F, (M.rank ≤ F.rank ↔ M.rank = F.rank) := by
  filter_upwards [(isOpen_setOf_le_rank F.rank).mem_nhds (le_refl F.rank)] with M hM
  have hM' : F.rank ≤ M.rank := hM
  omega

/-- The block chart `{M | toBlocks₁₁ M invertible}` is open. -/
theorem isOpen_setOf_isUnit_det_toBlocks₁₁ {m p q : Type*} [Fintype m] [Fintype p] [Fintype q]
    [DecidableEq m] : IsOpen {M : Matrix (m ⊕ p) (m ⊕ q) ℝ | IsUnit M.toBlocks₁₁.det} := by
  have h : {M : Matrix (m ⊕ p) (m ⊕ q) ℝ | IsUnit M.toBlocks₁₁.det} =
      {M | (M.submatrix Sum.inl Sum.inl).det ≠ 0} := by
    ext M
    simp only [Set.mem_ofPred_eq, isUnit_iff_ne_zero]
    rfl
  rw [h]
  exact isOpen_ne_fun ((continuous_id.matrix_submatrix _ _).matrix_det) continuous_const

/-- Over `ℝ` the tangent and normal spaces are complementary. -/
theorem isCompl_tangentSpace_normalSpace (F : Matrix ι κ ℝ) :
    IsCompl (tangentSpace F) (normalSpace F) := by
  classical
  have hdisj : tangentSpace F ⊓ normalSpace F = ⊥ := by
    rw [eq_bot_iff]
    rintro X ⟨hXT, hXN⟩
    have h := (mem_normalSpace_iff F X).mp hXN X hXT
    rw [← conjTranspose_eq_transpose_of_trivial, trace_conjTranspose_mul_self_eq_zero_iff] at h
    rw [h]
    exact Submodule.zero_mem _
  have hk1 : F.rank ≤ Fintype.card ι := rank_le_card_height F
  have hk2 : F.rank ≤ Fintype.card κ := rank_le_card_width F
  have hdim : Module.finrank ℝ (tangentSpace F) + Module.finrank ℝ (normalSpace F) =
      Module.finrank ℝ (Matrix ι κ ℝ) := by
    rw [finrank_tangentSpace F rfl, finrank_normalSpace F rfl, Module.finrank_matrix,
      Module.finrank_self, mul_one, dim_add_codim hk1 hk2]
  refine ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr ?_⟩
  apply Submodule.eq_top_of_finrank_eq
  have h := Submodule.finrank_sup_add_finrank_inf_eq (tangentSpace F) (normalSpace F)
  rw [hdisj, finrank_bot, add_zero] at h
  rw [h, hdim]

section TangentConeHelpers

open Filter

private theorem mul_mul_mem_tangentConeAt {ι' κ' : Type*} [Fintype ι'] [Fintype κ']
    {s : Set (Matrix ι κ ℝ)} {t : Set (Matrix ι' κ' ℝ)} {x y : Matrix ι κ ℝ}
    (A : Matrix ι' ι ℝ) (B : Matrix κ κ' ℝ) (hst : ∀ M ∈ s, A * M * B ∈ t)
    (hy : y ∈ tangentConeAt ℝ s x) : A * y * B ∈ tangentConeAt ℝ t (A * x * B) := by
  obtain ⟨α, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
  have hcont : Continuous fun M : Matrix ι κ ℝ => A * M * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine mem_tangentConeAt_of_seq l c (fun n => A * d n * B) ?_ ?_ ?_
  · have h := (hcont.tendsto 0).comp hd0
    rw [Matrix.mul_zero, Matrix.zero_mul] at h
    exact h
  · filter_upwards [hds] with n hn
    rw [← Matrix.add_mul, ← Matrix.mul_add]
    exact hst _ hn
  · have h := (hcont.tendsto y).comp hcd
    simpa [Function.comp_def, Matrix.mul_smul, Matrix.smul_mul] using h

variable {k a b : ℕ}

/-- The tangent cone at the model point `fromBlocks 1 0 0 0`. -/
private theorem tangentConeAt_fromBlocks_one :
    tangentConeAt ℝ {M : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ | M.rank ≤ k}
      (fromBlocks 1 0 0 0) =
      (tangentSpace (fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (0 : Matrix (Fin a) (Fin b) ℝ)) :
        Set (Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ)) := by
  ext y
  rw [SetLike.mem_coe, mem_tangentSpace_fromBlocks_one]
  set F₀ : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ := fromBlocks 1 0 0 0 with hF₀
  have c11 : Continuous (toBlocks₁₁ : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ → _) :=
    continuous_id.matrix_submatrix Sum.inl Sum.inl
  have c12 : Continuous (toBlocks₁₂ : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ → _) :=
    continuous_id.matrix_submatrix Sum.inl Sum.inr
  have c21 : Continuous (toBlocks₂₁ : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ → _) :=
    continuous_id.matrix_submatrix Sum.inr Sum.inl
  have c22 : Continuous (toBlocks₂₂ : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ → _) :=
    continuous_id.matrix_submatrix Sum.inr Sum.inr
  constructor
  · intro hy
    obtain ⟨α, l, hl, c, d, hd0, hds, hcd⟩ := exists_fun_of_mem_tangentConeAt hy
    have hF₀d : Tendsto (fun n => F₀ + d n) l (𝓝 F₀) := by
      simpa using tendsto_const_nhds.add hd0
    have hV : ∀ᶠ n in l, IsUnit (F₀ + d n).toBlocks₁₁.det :=
      hF₀d.eventually_mem (isOpen_setOf_isUnit_det_toBlocks₁₁.mem_nhds (by simp [F₀]))
    have hkey : ∀ᶠ n in l, c n • (d n).toBlocks₂₂ =
        (c n • d n).toBlocks₂₁ * ((F₀ + d n).toBlocks₁₁)⁻¹ * (d n).toBlocks₁₂ := by
      filter_upwards [hds, hV] with n hn hu
      have hr : (F₀ + d n).rank = Fintype.card (Fin k) := by
        rw [← rank_le_iff_rank_eq_of_isUnit_det_toBlocks₁₁ _ hu, Fintype.card_fin]
        exact hn
      have h := (rank_eq_iff_toBlocks₂₂_eq_of_isUnit_det_toBlocks₁₁ _ hu).mp hr
      have e22 : (F₀ + d n).toBlocks₂₂ = (d n).toBlocks₂₂ := by
        ext i j
        simp [F₀, toBlocks₂₂]
      have e21 : (F₀ + d n).toBlocks₂₁ = (d n).toBlocks₂₁ := by
        ext i j
        simp [F₀, toBlocks₂₁]
      have e12 : (F₀ + d n).toBlocks₁₂ = (d n).toBlocks₁₂ := by
        ext i j
        simp [F₀, toBlocks₁₂]
      rw [e22, e21, e12] at h
      rw [h]
      have es : (c n • d n).toBlocks₂₁ = c n • (d n).toBlocks₂₁ := by
        ext i j
        simp [toBlocks₂₁]
      rw [es, Matrix.smul_mul, Matrix.smul_mul]
    have hlim1 : Tendsto (fun n => (c n • d n).toBlocks₂₁) l (𝓝 y.toBlocks₂₁) :=
      (c21.tendsto y).comp hcd
    have hlim2 : Tendsto (fun n => ((F₀ + d n).toBlocks₁₁)⁻¹) l (𝓝 1) := by
      have h1 : Tendsto (fun n => (F₀ + d n).toBlocks₁₁) l (𝓝 (1 : Matrix (Fin k) (Fin k) ℝ)) := by
        have h := (c11.tendsto F₀).comp hF₀d
        have e : F₀.toBlocks₁₁ = 1 := by simp [F₀]
        rw [e] at h
        exact h
      have hinv : ContinuousAt Inv.inv (1 : Matrix (Fin k) (Fin k) ℝ) := by
        refine continuousAt_matrix_inv _ ?_
        rw [det_one, Ring.inverse_eq_inv']
        exact continuousAt_inv₀ one_ne_zero
      have h := hinv.tendsto.comp h1
      rw [inv_one] at h
      exact h
    have hlim3 : Tendsto (fun n => (d n).toBlocks₁₂) l (𝓝 0) := by
      have h := (c12.tendsto 0).comp hd0
      have e0 : (0 : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ).toBlocks₁₂ = 0 := by
        ext i j
        rfl
      rw [e0] at h
      exact h
    have hprod : Tendsto (fun n => (c n • d n).toBlocks₂₁ * ((F₀ + d n).toBlocks₁₁)⁻¹ *
        (d n).toBlocks₁₂) l (𝓝 0) := by
      have hc : Continuous fun p : Matrix (Fin a) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ ×
          Matrix (Fin k) (Fin b) ℝ => p.1 * p.2.1 * p.2.2 := by fun_prop
      have hpair : Tendsto (fun n => ((c n • d n).toBlocks₂₁, ((F₀ + d n).toBlocks₁₁)⁻¹,
          (d n).toBlocks₁₂)) l
          (𝓝 (y.toBlocks₂₁, (1 : Matrix (Fin k) (Fin k) ℝ), (0 : Matrix (Fin k) (Fin b) ℝ))) :=
        hlim1.prodMk_nhds (hlim2.prodMk_nhds hlim3)
      have hc0 : (fun p : Matrix (Fin a) (Fin k) ℝ × Matrix (Fin k) (Fin k) ℝ ×
          Matrix (Fin k) (Fin b) ℝ => p.1 * p.2.1 * p.2.2)
          (y.toBlocks₂₁, (1 : Matrix (Fin k) (Fin k) ℝ), (0 : Matrix (Fin k) (Fin b) ℝ)) = 0 := by
        simp
      have h := (hc.tendsto' _ _ hc0).comp hpair
      refine h.congr fun n => ?_
      simp only [Function.comp_apply]
    have hlim22 : Tendsto (fun n => c n • (d n).toBlocks₂₂) l (𝓝 y.toBlocks₂₂) := by
      have := (c22.tendsto y).comp hcd
      refine this.congr fun n => ?_
      ext i j
      simp [toBlocks₂₂]
    exact tendsto_nhds_unique (hlim22.congr' hkey) hprod
  · intro hy
    set Z : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ :=
      fromBlocks 0 0 (y.toBlocks₂₁ * y.toBlocks₁₁) (y.toBlocks₂₁ * y.toBlocks₁₂) with hZ
    have hyb : y = fromBlocks y.toBlocks₁₁ y.toBlocks₁₂ y.toBlocks₂₁ 0 := by
      have h := fromBlocks_toBlocks y
      rw [hy] at h
      exact h.symm
    refine mem_tangentConeAt_of_seq (𝓝[≠] (0 : ℝ)) (fun t => t⁻¹)
      (fun t => t • y + (t ^ 2) • Z) ?_ ?_ ?_
    · have hcont : Continuous fun t : ℝ => t • y + (t ^ 2) • Z := by fun_prop
      have h : Tendsto (fun t : ℝ => t • y + (t ^ 2) • Z) (𝓝 0) (𝓝 0) :=
        hcont.tendsto' 0 0 (by simp)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards with t
      have hfac : F₀ + (t • y + (t ^ 2) • Z) =
          fromRows (1 : Matrix (Fin k) (Fin k) ℝ) (t • y.toBlocks₂₁) *
            fromCols (1 + t • y.toBlocks₁₁) (t • y.toBlocks₁₂) := by
        rw [fromRows_mul_fromCols]
        conv_lhs => rw [hyb]
        simp only [F₀, hZ, fromBlocks_smul, fromBlocks_add]
        simp only [smul_zero, add_zero, zero_add, Matrix.one_mul, Matrix.smul_mul,
          Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, smul_smul, sq]
      show (F₀ + (t • y + (t ^ 2) • Z)).rank ≤ k
      rw [hfac]
      calc _ ≤ (fromRows (1 : Matrix (Fin k) (Fin k) ℝ) (t • y.toBlocks₂₁)).rank :=
            rank_mul_le_left _ _
        _ ≤ Fintype.card (Fin k) := rank_le_card_width _
        _ = k := Fintype.card_fin k
    · have hcont : Continuous fun t : ℝ => y + t • Z := by fun_prop
      have h : Tendsto (fun t : ℝ => y + t • Z) (𝓝 0) (𝓝 y) :=
        hcont.tendsto' 0 y (by simp)
      refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : t ≠ 0 := ht
      rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht', one_smul, sq, ← mul_assoc,
        inv_mul_cancel₀ ht', one_mul]

end TangentConeHelpers

/-- The tangent cone of `{rank ≤ k}` at a matrix of rank exactly `k` is the tangent space. -/
theorem tangentConeAt_setOf_rank_le (F : Matrix ι κ ℝ) {k : ℕ} (hF : F.rank = k) :
    tangentConeAt ℝ {M : Matrix ι κ ℝ | M.rank ≤ k} F = (tangentSpace F : Set (Matrix ι κ ℝ)) := by
  classical
  obtain ⟨P, P', Q, Q', hP, hP', hQ, hQ', hPFQ⟩ := exists_normalForm F hF
  have hcancel : ∀ X : Matrix ι κ ℝ, P' * (P * X * Q) * Q' = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.mul_assoc, hQ,
      Matrix.mul_one]
  ext y
  rw [SetLike.mem_coe]
  constructor
  · intro hy
    have h1 := mul_mul_mem_tangentConeAt
      (t := {M : Matrix (Fin k ⊕ Fin (Fintype.card ι - k)) (Fin k ⊕ Fin (Fintype.card κ - k)) ℝ |
        M.rank ≤ k}) P Q
      (fun M hM => le_trans ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)) hM) hy
    rw [hPFQ, tangentConeAt_fromBlocks_one, SetLike.mem_coe, ← hPFQ,
      mem_tangentSpace_mul_mul_iff F hP hP' hQ hQ', hcancel] at h1
    exact h1
  · intro hy
    have h1 : P * y * Q ∈ tangentSpace (P * F * Q) := by
      rw [mem_tangentSpace_mul_mul_iff F hP hP' hQ hQ', hcancel]
      exact hy
    rw [hPFQ, ← SetLike.mem_coe, ← tangentConeAt_fromBlocks_one] at h1
    have h2 := mul_mul_mem_tangentConeAt (t := {M : Matrix ι κ ℝ | M.rank ≤ k}) P' Q'
      (fun M hM => le_trans ((rank_mul_le_left _ _).trans (rank_mul_le_right _ _)) hM) h1
    rw [← hPFQ, hcancel, hcancel] at h2
    exact h2

section LocalGraphHelpers

open Filter

/-- Parameter space `(A, B, C)` of the Schur block chart. -/
private abbrev ChartParam (k a b : ℕ) : Type :=
  (Fin k → Fin k → ℝ) × (Fin k → Fin b → ℝ) × (Fin a → Fin k → ℝ)

/-- Fibre space `D` of the Schur block chart. -/
private abbrev ChartFiber (a b : ℕ) : Type := Fin a → Fin b → ℝ

private theorem finrank_fun_fun (a b : ℕ) : Module.finrank ℝ (Fin a → Fin b → ℝ) = a * b := by
  rw [Module.finrank_pi_fintype]
  simp

/-- Block coordinates `M ↦ ((M₁₁, M₁₂, M₂₁), M₂₂)`. -/
private def blockEquiv (k a b : ℕ) :
    Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ ≃ₗ[ℝ] ChartParam k a b × ChartFiber a b where
  toFun M := ((M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₁), M.toBlocks₂₂)
  invFun w := fromBlocks w.1.1 w.1.2.1 w.1.2.2 w.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv M := fromBlocks_toBlocks M
  right_inv _ := rfl

/-- The Schur-complement map `(A, B, C) ↦ C A⁻¹ B`. -/
private noncomputable def schurMap (k a b : ℕ) (w : ChartParam k a b) : ChartFiber a b :=
  Matrix.of w.2.2 * (Matrix.of w.1)⁻¹ * Matrix.of w.2.1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem contDiff_det_of_entries {n : Type*} [Fintype n] [DecidableEq n] {M : E → Matrix n n ℝ}
    (hM : ∀ i j, ContDiff ℝ ∞ fun x => M x i j) : ContDiff ℝ ∞ fun x => (M x).det := by
  simp only [det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)

private theorem contDiff_adjugate_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : E → Matrix n n ℝ} (hM : ∀ i j, ContDiff ℝ ∞ fun x => M x i j) (i j : n) :
    ContDiff ℝ ∞ fun x => (M x).adjugate i j := by
  simp only [adjugate_apply]
  apply contDiff_det_of_entries
  intro a c
  by_cases h : a = j
  · subst h
    simp only [updateRow_self]
    exact contDiff_const
  · simp only [updateRow_ne h]
    exact hM a c

private theorem contDiffOn_inv_of_entries {n : Type*} [Fintype n] [DecidableEq n]
    {M : E → Matrix n n ℝ} (hM : ∀ i j, ContDiff ℝ ∞ fun x => M x i j) (i j : n) :
    ContDiffOn ℝ ∞ (fun x => (M x)⁻¹ i j) {x | (M x).det ≠ 0} := by
  have h : ∀ x, (M x)⁻¹ i j = ((M x).det)⁻¹ * (M x).adjugate i j := by
    intro x
    rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  simp only [h]
  exact ((contDiff_det_of_entries hM).contDiffOn.inv fun x hx => hx).mul
    (contDiff_adjugate_of_entries hM i j).contDiffOn

private theorem contDiffOn_schurMap (k a b : ℕ) :
    ContDiffOn ℝ ∞ (schurMap k a b)
      {w : ChartParam k a b | IsUnit (Matrix.of w.1).det} := by
  have hA : ∀ i j, ContDiff ℝ ∞ fun w : ChartParam k a b => Matrix.of w.1 i j :=
    fun i j => (contDiff_apply_apply ℝ i j).comp contDiff_fst
  have hB : ∀ i j, ContDiff ℝ ∞ fun w : ChartParam k a b => w.2.1 i j :=
    fun i j => (contDiff_apply_apply ℝ i j).comp (contDiff_fst.comp contDiff_snd)
  have hC : ∀ i j, ContDiff ℝ ∞ fun w : ChartParam k a b => w.2.2 i j :=
    fun i j => (contDiff_apply_apply ℝ i j).comp (contDiff_snd.comp contDiff_snd)
  have hsub : {w : ChartParam k a b | IsUnit (Matrix.of w.1).det} ⊆
      {w | (Matrix.of w.1).det ≠ 0} := fun w hw => hw.ne_zero
  refine contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => ?_
  simp only [schurMap, Matrix.mul_apply, Matrix.of_apply]
  refine ContDiffOn.sum fun l _ => ContDiffOn.mul (ContDiffOn.sum fun m _ => ?_)
    (hB l j).contDiffOn
  exact (hC i m).contDiffOn.mul ((contDiffOn_inv_of_entries hA m l).mono hsub)

/-- The local graph at the model point `fromBlocks 1 0 0 0`. -/
private theorem exists_localGraph_fromBlocks_one {k a b d₁ d₂ : ℕ} (hd₁ : k * k + (k * b + a * k) = d₁)
    (hd₂ : a * b = d₂) :
    ∃ (e : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ ≃L[ℝ]
        EuclideanSpace ℝ (Fin d₁) × EuclideanSpace ℝ (Fin d₂))
      (U : Set (EuclideanSpace ℝ (Fin d₁)))
      (g : EuclideanSpace ℝ (Fin d₁) → EuclideanSpace ℝ (Fin d₂)),
      IsOpen U ∧ (e (fromBlocks 1 0 0 0)).1 ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
      ∃ V ∈ 𝓝 (fromBlocks 1 0 0 0 : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ),
        V ∩ {M | M.rank ≤ k} = V ∩ {M | M.rank = k} ∧
        V ∩ {M | M.rank = k} = V ∩ e ⁻¹' {p | p.1 ∈ U ∧ p.2 = g p.1} := by
  classical
  have hφ : Module.finrank ℝ (ChartParam k a b) = Module.finrank ℝ (EuclideanSpace ℝ (Fin d₁)) := by
    simp only [ChartParam, Module.finrank_prod, finrank_fun_fun, finrank_euclideanSpace_fin, hd₁]
  have hψ : Module.finrank ℝ (ChartFiber a b) = Module.finrank ℝ (EuclideanSpace ℝ (Fin d₂)) := by
    simp only [ChartFiber, finrank_fun_fun, finrank_euclideanSpace_fin, hd₂]
  let φ : ChartParam k a b ≃L[ℝ] EuclideanSpace ℝ (Fin d₁) :=
    (LinearEquiv.ofFinrankEq _ _ hφ).toContinuousLinearEquiv
  let ψ : ChartFiber a b ≃L[ℝ] EuclideanSpace ℝ (Fin d₂) :=
    (LinearEquiv.ofFinrankEq _ _ hψ).toContinuousLinearEquiv
  let β : Matrix (Fin k ⊕ Fin a) (Fin k ⊕ Fin b) ℝ ≃L[ℝ] ChartParam k a b × ChartFiber a b :=
    (blockEquiv k a b).toContinuousLinearEquiv
  let e := β.trans (φ.prodCongr ψ)
  let S : Set (ChartParam k a b) := {w | IsUnit (Matrix.of w.1).det}
  let U : Set (EuclideanSpace ℝ (Fin d₁)) := φ.symm ⁻¹' S
  let g : EuclideanSpace ℝ (Fin d₁) → EuclideanSpace ℝ (Fin d₂) :=
    fun x => ψ (schurMap k a b (φ.symm x))
  have he : ∀ M, e M = (φ (M.toBlocks₁₁, M.toBlocks₁₂, M.toBlocks₂₁), ψ M.toBlocks₂₂) :=
    fun M => rfl
  have hSopen : IsOpen S := by
    have hc : Continuous fun w : ChartParam k a b => (Matrix.of w.1).det :=
      Continuous.matrix_det (A := fun w : ChartParam k a b => Matrix.of w.1) continuous_fst
    simpa [S, isUnit_iff_ne_zero] using isOpen_ne_fun hc continuous_const
  refine ⟨e, U, g, hSopen.preimage φ.symm.continuous, ?_, ?_, ?_⟩
  · show φ.symm (e (fromBlocks 1 0 0 0)).1 ∈ S
    rw [he, ContinuousLinearEquiv.symm_apply_apply]
    show IsUnit (fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0
      (0 : Matrix (Fin a) (Fin b) ℝ)).toBlocks₁₁.det
    simp
  · exact ψ.contDiff.comp_contDiffOn ((contDiffOn_schurMap k a b).comp φ.symm.contDiff.contDiffOn
      (fun x hx => hx))
  · refine ⟨{M | IsUnit M.toBlocks₁₁.det},
      isOpen_setOf_isUnit_det_toBlocks₁₁.mem_nhds (by simp), ?_, ?_⟩
    · ext M
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hM, hr⟩
        refine ⟨hM, ?_⟩
        have := (rank_le_iff_rank_eq_of_isUnit_det_toBlocks₁₁ M hM)
        rw [Fintype.card_fin] at this
        exact this.mp hr
      · rintro ⟨hM, hr⟩
        exact ⟨hM, hr.le⟩
    · ext M
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · rintro ⟨hM, hr⟩
        refine ⟨hM, ?_, ?_⟩
        · show φ.symm (e M).1 ∈ S
          rw [he, ContinuousLinearEquiv.symm_apply_apply]
          exact hM
        · have h := (rank_eq_iff_toBlocks₂₂_eq_of_isUnit_det_toBlocks₁₁ M hM).mp
            (by rw [Fintype.card_fin]; exact hr)
          rw [he]
          simp only [g, ContinuousLinearEquiv.symm_apply_apply]
          rw [h]
          rfl
      · rintro ⟨hM, -, hg⟩
        refine ⟨hM, ?_⟩
        have h2 : (e M).2 = g (e M).1 := hg
        rw [he] at h2
        simp only [g, ContinuousLinearEquiv.symm_apply_apply] at h2
        have h3 : M.toBlocks₂₂ = M.toBlocks₂₁ * M.toBlocks₁₁⁻¹ * M.toBlocks₁₂ := ψ.injective h2
        have := (rank_eq_iff_toBlocks₂₂_eq_of_isUnit_det_toBlocks₁₁ M hM).mpr h3
        rwa [Fintype.card_fin] at this

end LocalGraphHelpers

/-- **Local manifold structure.** Near a matrix `F` of rank exactly `k`, the set `{rank ≤ k}`
coincides with `{rank = k}`, and in linear coordinates `ℝ^(k(n+r-k)) × ℝ^((n-k)(r-k))` it is
the graph of a `C^∞` map on an open set: a smooth embedded submanifold of dimension
`k(n+r-k)` and codimension `(n-k)(r-k)`. -/
theorem exists_localGraph (F : Matrix ι κ ℝ) {k : ℕ} (hF : F.rank = k) :
    ∃ (e : Matrix ι κ ℝ ≃L[ℝ]
        EuclideanSpace ℝ (Fin (k * (Fintype.card ι + Fintype.card κ - k))) ×
          EuclideanSpace ℝ (Fin ((Fintype.card ι - k) * (Fintype.card κ - k))))
      (U : Set (EuclideanSpace ℝ (Fin (k * (Fintype.card ι + Fintype.card κ - k)))))
      (g : EuclideanSpace ℝ (Fin (k * (Fintype.card ι + Fintype.card κ - k))) →
        EuclideanSpace ℝ (Fin ((Fintype.card ι - k) * (Fintype.card κ - k)))),
      IsOpen U ∧ (e F).1 ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
      ∃ V ∈ 𝓝 F, V ∩ {M | M.rank ≤ k} = V ∩ {M | M.rank = k} ∧
        V ∩ {M | M.rank = k} = V ∩ e ⁻¹' {p | p.1 ∈ U ∧ p.2 = g p.1} := by
  classical
  obtain ⟨P, P', Q, Q', hP, hP', hQ, hQ', hPFQ⟩ := exists_normalForm F hF
  have hk1 : k ≤ Fintype.card ι := hF ▸ rank_le_card_height F
  have hk2 : k ≤ Fintype.card κ := hF ▸ rank_le_card_width F
  have hd₁ : k * k + (k * (Fintype.card κ - k) + (Fintype.card ι - k) * k) =
      k * (Fintype.card ι + Fintype.card κ - k) := by
    obtain ⟨a, ha⟩ := Nat.exists_eq_add_of_le hk1
    obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hk2
    have h3 : k + a + (k + b) - k = k + a + b := by omega
    rw [ha, hb, h3, Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    ring
  obtain ⟨e₀, U, g, hU, hUF, hg, V₀, hV₀, h1, h2⟩ :=
    exists_localGraph_fromBlocks_one (k := k) (a := Fintype.card ι - k)
      (b := Fintype.card κ - k) hd₁ rfl
  let c : Matrix ι κ ℝ ≃L[ℝ]
      Matrix (Fin k ⊕ Fin (Fintype.card ι - k)) (Fin k ⊕ Fin (Fintype.card κ - k)) ℝ :=
    (changeEquiv P P' Q Q' hP hP' hQ hQ').toContinuousLinearEquiv
  have hc : ∀ M, c M = P * M * Q := fun M => rfl
  have hcancel : ∀ X : Matrix ι κ ℝ, P' * (P * X * Q) * Q' = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP', Matrix.one_mul, Matrix.mul_assoc, hQ,
      Matrix.mul_one]
  have hrank : ∀ M : Matrix ι κ ℝ, (c M).rank = M.rank := by
    intro M
    apply le_antisymm
    · rw [hc]
      exact (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
    · calc M.rank = (P' * (P * M * Q) * Q').rank := by rw [hcancel]
        _ ≤ (P * M * Q).rank := (rank_mul_le_left _ _).trans (rank_mul_le_right _ _)
        _ = (c M).rank := by rw [hc]
  refine ⟨c.trans e₀, U, g, hU, ?_, hg, c ⁻¹' V₀, ?_, ?_, ?_⟩
  · show (e₀ (c F)).1 ∈ U
    rw [hc, hPFQ]
    exact hUF
  · exact c.continuous.continuousAt.preimage_mem_nhds (by rw [hc, hPFQ]; exact hV₀)
  · ext M
    have h1M := Set.ext_iff.mp h1 (c M)
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hrank] at h1M
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
    exact h1M
  · ext M
    have h2M := Set.ext_iff.mp h2 (c M)
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, hrank] at h2M
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
      ContinuousLinearEquiv.trans_apply]
    exact h2M

end Real

section Acceptance

variable {K : Type*} [Field K]

/-- Acceptance (`n = r = 2`, `k = 1`): the normal space has dimension `1` (codimension `1`)
and the tangent space has dimension `3`. -/
theorem finrank_normalSpace_tangentSpace_two_two_one (F : Matrix (Fin 2) (Fin 2) K)
    (hF : F.rank = 1) :
    Module.finrank K (normalSpace F) = 1 ∧ Module.finrank K (tangentSpace F) = 3 := by
  rw [finrank_normalSpace F hF, finrank_tangentSpace F hF]
  simp

/-- Non-vacuity of the acceptance instance: `!![1, 0; 0, 0]` has rank `1`. -/
theorem rank_two_two_one_example : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K).rank = 1 := by
  classical
  have h : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) K) = diagonal ![1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [h, rank_diagonal, Fintype.card_subtype]
  have hs : (Finset.univ.filter fun x : Fin 2 => ![(1 : K), 0] x ≠ 0) = {0} := by
    ext x
    fin_cases x <;> simp
  rw [hs, Finset.card_singleton]

end Acceptance

end Matrix.RankManifold
