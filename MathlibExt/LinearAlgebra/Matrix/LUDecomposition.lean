/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# LU decomposition

This file proves existence of LU decomposition from nonvanishing leading principal minors and
uniqueness when the lower factor has unit diagonal.
-/

@[expose] public section

namespace MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted

variable {K : Type*} [Field K]

private theorem lu_lower_mul_apply_diag {n : ℕ} {M N : Matrix (Fin n) (Fin n) K}
    (hM : M.IsLowerTriangular) (hN : N.IsLowerTriangular) (i : Fin n) :
    (M * N) i i = M i i * N i i := by
  rw [Matrix.mul_apply]
  classical
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hji | hji
    · rw [hN hji, mul_zero]
    · rw [hM hji, zero_mul]
  · simp

private theorem lu_det_eq_one_of_lower_unit {n : ℕ} (L : Matrix (Fin n) (Fin n) K)
    (hL : L.IsLowerTriangular) (hdiag : ∀ i, L i i = 1) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L hL]
  simp [hdiag]

private theorem lu_lower_inv_unit {n : ℕ} (L : Matrix (Fin n) (Fin n) K)
    (hL : L.IsLowerTriangular) (hdiag : ∀ i, L i i = 1) :
    L⁻¹.IsLowerTriangular ∧ ∀ i, L⁻¹ i i = 1 := by
  have hdet : IsUnit L.det := by
    rw [lu_det_eq_one_of_lower_unit L hL hdiag]
    exact isUnit_one
  let hInv : Invertible L := Matrix.invertibleOfIsUnitDet L hdet
  have hinv : L⁻¹.IsLowerTriangular :=
    @Matrix.blockTriangular_inv_of_blockTriangular _ _ _ L _ _ _ _ _ hInv hL
  refine ⟨hinv, fun i ↦ ?_⟩
  have hi := congr_fun (congr_fun (Matrix.nonsing_inv_mul L hdet) i) i
  rw [lu_lower_mul_apply_diag hinv hL i, hdiag i] at hi
  simpa using hi

private theorem lu_upper_inv {n : ℕ} (U : Matrix (Fin n) (Fin n) K)
    (hU : U.IsUpperTriangular) (hdet : IsUnit U.det) : U⁻¹.IsUpperTriangular := by
  let hInv : Invertible U := Matrix.invertibleOfIsUnitDet U hdet
  exact @Matrix.blockTriangular_inv_of_blockTriangular _ _ _ U _ _ _ _ _ hInv hU

private theorem lu_lower_upper_unit_eq_one {n : ℕ} (M : Matrix (Fin n) (Fin n) K)
    (hLower : M.IsLowerTriangular) (hUpper : M.IsUpperTriangular)
    (hdiag : ∀ i, M i i = 1) : M = 1 := by
  ext i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [hLower hij]
    simp [hij.ne]
  · simpa using hdiag i
  · rw [hUpper hji]
    simp [hji.ne']

private theorem lu_unique_aux (n : ℕ) (A L₁ L₂ U₁ U₂ : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A.det)
    (hL₁ : L₁.IsLowerTriangular) (hU₁ : U₁.IsUpperTriangular) (hd₁ : ∀ i, L₁ i i = 1)
    (hL₂ : L₂.IsLowerTriangular) (hU₂ : U₂.IsUpperTriangular) (hd₂ : ∀ i, L₂ i i = 1)
    (e₁ : A = L₁ * U₁) (e₂ : A = L₂ * U₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  have hdetL₁ : L₁.det = 1 := lu_det_eq_one_of_lower_unit L₁ hL₁ hd₁
  have hdetL₂ : L₂.det = 1 := lu_det_eq_one_of_lower_unit L₂ hL₂ hd₂
  have hunitL₂ : IsUnit L₂.det := by
    rw [hdetL₂]
    exact isUnit_one
  have hdetU₁ : U₁.det = A.det := by
    rw [e₁, Matrix.det_mul, hdetL₁, one_mul]
  have hunitU₁ : IsUnit U₁.det := by
    rw [hdetU₁]
    exact hA
  obtain ⟨hL₂inv, hdL₂inv⟩ := lu_lower_inv_unit L₂ hL₂ hd₂
  have hU₁inv : U₁⁻¹.IsUpperTriangular := lu_upper_inv U₁ hU₁ hunitU₁
  have hfac : L₁ * U₁ = L₂ * U₂ := e₁.symm.trans e₂
  have he := congrArg (fun M ↦ L₂⁻¹ * M * U₁⁻¹) hfac
  have hcommon : L₂⁻¹ * L₁ = U₂ * U₁⁻¹ := by
    calc
      L₂⁻¹ * L₁ = (L₂⁻¹ * L₁) * (U₁ * U₁⁻¹) := by
        rw [Matrix.mul_nonsing_inv U₁ hunitU₁, Matrix.mul_one]
      _ = L₂⁻¹ * (L₁ * U₁) * U₁⁻¹ := by simp only [Matrix.mul_assoc]
      _ = L₂⁻¹ * (L₂ * U₂) * U₁⁻¹ := he
      _ = (L₂⁻¹ * L₂) * (U₂ * U₁⁻¹) := by simp only [Matrix.mul_assoc]
      _ = U₂ * U₁⁻¹ := by rw [Matrix.nonsing_inv_mul L₂ hunitL₂, Matrix.one_mul]
  have hcommonLower : (L₂⁻¹ * L₁).IsLowerTriangular := hL₂inv.mul hL₁
  have hcommonUpper : (L₂⁻¹ * L₁).IsUpperTriangular := by
    rw [hcommon]
    exact hU₂.mul hU₁inv
  have hcommonDiag : ∀ i, (L₂⁻¹ * L₁) i i = 1 := by
    intro i
    rw [lu_lower_mul_apply_diag hL₂inv hL₁ i, hdL₂inv i, hd₁ i, one_mul]
  have hcommonOne : L₂⁻¹ * L₁ = 1 :=
    lu_lower_upper_unit_eq_one _ hcommonLower hcommonUpper hcommonDiag
  have hL : L₁ = L₂ := by
    calc
      L₁ = 1 * L₁ := (Matrix.one_mul L₁).symm
      _ = (L₂ * L₂⁻¹) * L₁ := by rw [Matrix.mul_nonsing_inv L₂ hunitL₂]
      _ = L₂ * (L₂⁻¹ * L₁) := Matrix.mul_assoc _ _ _
      _ = L₂ * 1 := by rw [hcommonOne]
      _ = L₂ := Matrix.mul_one _
  have hupperOne : U₂ * U₁⁻¹ = 1 := hcommon.symm.trans hcommonOne
  have hU : U₂ = U₁ := by
    calc
      U₂ = U₂ * 1 := (Matrix.mul_one U₂).symm
      _ = U₂ * (U₁⁻¹ * U₁) := by rw [Matrix.nonsing_inv_mul U₁ hunitU₁]
      _ = (U₂ * U₁⁻¹) * U₁ := (Matrix.mul_assoc _ _ _).symm
      _ = 1 * U₁ := by rw [hupperOne]
      _ = U₁ := Matrix.one_mul _
  exact ⟨hL, hU.symm⟩

private theorem lu_fromBlocks_lower {n : ℕ} (L : Matrix (Fin n) (Fin n) K)
    (C : Matrix (Fin 1) (Fin n) K) (D : Matrix (Fin 1) (Fin 1) K)
    (hL : L.IsLowerTriangular) :
    (Matrix.fromBlocks L 0 C D).BlockTriangular
      (fun i ↦ OrderDual.toDual
        ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) i)) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · apply hL
    simp only [finSumFinEquiv_apply_left] at hij
    exact (Fin.castAddOrderEmb 1).lt_iff_lt.mp hij
  · rfl
  · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hij
    change n + i.val < j.val at hij
    omega
  · fin_cases i
    fin_cases j
    exact (lt_irrefl _ hij).elim

private theorem lu_fromBlocks_upper {n : ℕ} (U : Matrix (Fin n) (Fin n) K)
    (B : Matrix (Fin n) (Fin 1) K) (D : Matrix (Fin 1) (Fin 1) K)
    (hU : U.IsUpperTriangular) :
    (Matrix.fromBlocks U B 0 D).BlockTriangular
      (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · apply hU
    simp only [finSumFinEquiv_apply_left] at hij
    exact (Fin.castAddOrderEmb 1).lt_iff_lt.mp hij
  · simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right] at hij
    change n + j.val < i.val at hij
    omega
  · rfl
  · fin_cases i
    fin_cases j
    exact (lt_irrefl _ hij).elim

private theorem lu_block_factor {n : ℕ}
    (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) K)
    (L₀ U₀ : Matrix (Fin n) (Fin n) K)
    (hL₀ : L₀.IsLowerTriangular) (hU₀ : U₀.IsUpperTriangular)
    (hd₀ : ∀ i, L₀ i i = 1) (hfac : A.toBlocks₁₁ = L₀ * U₀)
    (hdet : A.toBlocks₁₁.det ≠ 0) :
    ∃ L U : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) K,
      L.BlockTriangular
          (fun i ↦ OrderDual.toDual
            ((finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) i)) ∧
        U.BlockTriangular (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)) ∧
        (∀ i, L i i = 1) ∧ A = L * U := by
  have hdetL₀ : L₀.det = 1 := lu_det_eq_one_of_lower_unit L₀ hL₀ hd₀
  have hunitL₀ : IsUnit L₀.det := by
    rw [hdetL₀]
    exact isUnit_one
  have hdetU₀ : U₀.det ≠ 0 := by
    intro hzero
    apply hdet
    rw [hfac, Matrix.det_mul, hzero, mul_zero]
  have hunitU₀ : IsUnit U₀.det := isUnit_iff_ne_zero.mpr hdetU₀
  let X := A.toBlocks₂₁ * U₀⁻¹
  let Y := L₀⁻¹ * A.toBlocks₁₂
  let Z := A.toBlocks₂₂ - X * Y
  let L := Matrix.fromBlocks L₀ 0 X (1 : Matrix (Fin 1) (Fin 1) K)
  let U := Matrix.fromBlocks U₀ Y 0 Z
  refine ⟨L, U, lu_fromBlocks_lower L₀ X 1 hL₀,
    lu_fromBlocks_upper U₀ Y Z hU₀, ?_, ?_⟩
  · intro i
    rcases i with i | i
    · exact hd₀ i
    · fin_cases i
      simp [L]
  · dsimp [L, U]
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_toBlocks A]
    congr 1
    · simp [hfac]
    · simpa [Y] using
        (Matrix.mul_nonsing_inv_cancel_left L₀ A.toBlocks₁₂ hunitL₀).symm
    · simpa [X] using
        (Matrix.nonsing_inv_mul_cancel_right U₀ A.toBlocks₂₁ hunitU₀).symm
    · simp [Z]

omit [Field K] in
private theorem lu_reindexed_topLeft {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A).toBlocks₁₁ =
      A.submatrix Fin.castSucc Fin.castSucc := by
  ext i j
  simp only [Matrix.toBlocks₁₁, Matrix.reindex_apply, Matrix.of_apply,
    Matrix.submatrix_apply]
  change A (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) =
    A i.castSucc j.castSucc
  have hi : Fin.castAdd 1 i = i.castSucc := Fin.ext rfl
  have hj : Fin.castAdd 1 j = j.castSucc := Fin.ext rfl
  rw [finSumFinEquiv_apply_left, finSumFinEquiv_apply_left, hi, hj]

private theorem lu_leading_topLeft_nonzero {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (h : ∀ (k : ℕ) (hk : k ≤ n + 1),
      Matrix.det (A.submatrix (Fin.castLE hk) (Fin.castLE hk)) ≠ 0) :
    ∀ (k : ℕ) (hk : k ≤ n),
      Matrix.det ((A.submatrix Fin.castSucc Fin.castSucc).submatrix
        (Fin.castLE hk) (Fin.castLE hk)) ≠ 0 := by
  intro k hk
  simpa only [Matrix.submatrix_submatrix, Function.comp_def, Fin.castSucc_castLE] using
    h k (Nat.le.step hk)

private theorem lu_exists_aux (n : ℕ) (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ (k : ℕ) (hk : k ≤ n),
      Matrix.det (A.submatrix (Fin.castLE hk) (Fin.castLE hk)) ≠ 0) :
    ∃ L U : Matrix (Fin n) (Fin n) K,
      L.IsLowerTriangular ∧ U.IsUpperTriangular ∧ (∀ i, L i i = 1) ∧ A = L * U := by
  induction n with
  | zero =>
      refine ⟨1, A, Matrix.blockTriangular_one, ?_, ?_, by simp⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      let A₀ := A.submatrix Fin.castSucc Fin.castSucc
      have h₀ : ∀ (k : ℕ) (hk : k ≤ n),
          Matrix.det (A₀.submatrix (Fin.castLE hk) (Fin.castLE hk)) ≠ 0 := by
        dsimp [A₀]
        exact lu_leading_topLeft_nonzero A h
      obtain ⟨L₀, U₀, hL₀, hU₀, hd₀, hfac₀⟩ := ih A₀ h₀
      let A' := Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm A
      have htop : A'.toBlocks₁₁ = A₀ := by
        dsimp [A']
        exact lu_reindexed_topLeft A
      have hfac : A'.toBlocks₁₁ = L₀ * U₀ := htop.trans hfac₀
      have hdetA₀ : A₀.det ≠ 0 := by
        have hc : Fin.castLE (Nat.le_succ n) = Fin.castSucc := by
          funext i
          exact Fin.ext rfl
        dsimp [A₀]
        simpa only [hc] using h n (Nat.le_succ n)
      have hdet : A'.toBlocks₁₁.det ≠ 0 := by
        rw [htop]
        exact hdetA₀
      obtain ⟨L', U', hL', hU', hd', hfac'⟩ :=
        lu_block_factor A' L₀ U₀ hL₀ hU₀ hd₀ hfac hdet
      let L := Matrix.reindex finSumFinEquiv finSumFinEquiv L'
      let U := Matrix.reindex finSumFinEquiv finSumFinEquiv U'
      have hL : L.IsLowerTriangular := by
        have hcomp : L'.BlockTriangular
            (OrderDual.toDual ∘ (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))) := by
          intro i j hij
          exact hL' hij
        exact (Matrix.blockTriangular_reindex_iff (M := L')
          (b := OrderDual.toDual) (e := finSumFinEquiv)).2 hcomp
      have hU : U.IsUpperTriangular := by
        refine (Matrix.blockTriangular_reindex_iff (M := U')
          (b := id) (e := finSumFinEquiv)).2 ?_
        intro i j hij
        exact hU' hij
      have hd : ∀ i, L i i = 1 := by
        intro i
        dsimp [L]
        exact hd' _
      refine ⟨L, U, hL, hU, hd, ?_⟩
      have hback : Matrix.reindex finSumFinEquiv finSumFinEquiv A' = A := by
        dsimp [A']
        ext i j
        simp
      have hmul : Matrix.reindex finSumFinEquiv finSumFinEquiv (L' * U') =
          Matrix.reindex finSumFinEquiv finSumFinEquiv L' *
            Matrix.reindex finSumFinEquiv finSumFinEquiv U' := by
        simpa only [Matrix.reindex_apply] using
          (Matrix.submatrix_mul_equiv L' U' finSumFinEquiv.symm finSumFinEquiv.symm
            finSumFinEquiv.symm).symm
      dsimp [L, U]
      exact hback.symm.trans ((congrArg
        (fun M ↦ Matrix.reindex finSumFinEquiv finSumFinEquiv M) hfac').trans hmul)

/--
**LU decomposition without pivoting.** Let $K$ be a field and $A$ an $n \times n$ matrix over
$K$ whose leading principal minors are all nonzero: for every $k \le n$, the determinant of the
upper-left $k \times k$ block of $A$ is nonzero. Then $A = LU$ for some $n \times n$ matrices
$L$ and $U$ over $K$ such that $L$ is lower triangular with every diagonal entry equal to $1$ and
$U$ is upper triangular.

Proof: Induct on the dimension and extend the factorization of the leading principal block by a
bordered (Schur-complement) step. The statement is the existence half of Wikipedia, "LU
decomposition", section "Existence and uniqueness".

Proves `Wanted` entry `exists_lu_decomposition_of_minors_ne_zero`.

Sources: Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear
inequalities / LU decomposition; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM
(1997), Lecture 20.
-/
theorem exists_lu_decomposition_of_minors_ne_zero (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ (k : ℕ) (hk : k ≤ n),
      Matrix.det (A.submatrix (Fin.castLE hk) (Fin.castLE hk)) ≠ 0) :
    ∃ L U : Matrix (Fin n) (Fin n) K,
      L.IsLowerTriangular ∧ U.IsUpperTriangular ∧ (∀ i, L i i = 1) ∧ A = L * U := by
  exact lu_exists_aux n A h

/--
**Uniqueness of the LU decomposition.** Let $K$ be a field and $A$ an invertible $n \times n$
matrix over $K$. Suppose $A = L_1 U_1 = L_2 U_2$, where $L_1$ and $L_2$ are lower triangular
$n \times n$ matrices over $K$ with every diagonal entry equal to $1$, and $U_1$ and $U_2$ are
upper triangular $n \times n$ matrices over $K$. Then $L_1 = L_2$ and $U_1 = U_2$.

Proof: Move the invertible triangular factors across the equality, then use the triangular inverse
and diagonal formulas to show the resulting matrix is the identity. The statement is the
uniqueness half of Wikipedia, "LU decomposition", section "Existence and uniqueness".

Proves `Wanted` entry `lu_decomposition_unique`.

Sources: Mathlib `docs/undergrad.yaml`, Numerical Analysis / Solving systems of linear
inequalities / LU decomposition; L. N. Trefethen and D. Bau, Numerical Linear Algebra, SIAM
(1997), Lecture 20.
-/
theorem lu_decomposition_unique (n : ℕ)
    (A L₁ L₂ U₁ U₂ : Matrix (Fin n) (Fin n) K)
    (hA : IsUnit A.det)
    (hL₁ : L₁.IsLowerTriangular) (hU₁ : U₁.IsUpperTriangular) (hd₁ : ∀ i, L₁ i i = 1)
    (hL₂ : L₂.IsLowerTriangular) (hU₂ : U₂.IsUpperTriangular) (hd₂ : ∀ i, L₂ i i = 1)
    (e₁ : A = L₁ * U₁) (e₂ : A = L₂ * U₂) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  exact lu_unique_aux n A L₁ L₂ U₁ U₂ hA hL₁ hU₁ hd₁ hL₂ hU₂ hd₂ e₁ e₂

end MathlibExt.LinearAlgebra.Matrix.LUDecompositionWanted
