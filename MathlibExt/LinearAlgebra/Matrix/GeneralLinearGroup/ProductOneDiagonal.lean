/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Field
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockStabilization

@[expose] public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Unit on `Fin n ⊕ Fin 1` extending `u` by final entry
`(∏ i, u i)⁻¹`. Empty product `1` gives `1` for `n = 0`. -/
def productOneDiagonal (u : Fin n → Rˣ) :
    Fin n ⊕ Fin 1 → Rˣ :=
  Sum.elim u fun _ => (Finset.univ.prod u)⁻¹

/-- Determinant of `diagonalUnitsHom` of `productOneDiagonal` is `1`. -/
theorem det_diagonalUnitsHom_productOneDiagonal (u : Fin n → Rˣ) :
    det (diagonalUnitsHom R (Fin n ⊕ Fin 1)
      (productOneDiagonal u)) = 1 := by
  rw [det_diagonalUnitsHom, Fintype.prod_sum_type]
  simp only [productOneDiagonal, Sum.elim_inl, Sum.elim_inr,
    Fintype.prod_unique, mul_inv_cancel]

/-- `diagonalUnitsHom` of `productOneDiagonal u` equals
`blockDiagonalOne` of `diagonalUnitsHom u` iff `∏ i, u i = 1`. -/
theorem diagonalUnitsHom_productOneDiagonal_eq_blockDiagonalOne_iff
    (u : Fin n → Rˣ) :
    diagonalUnitsHom R (Fin n ⊕ Fin 1) (productOneDiagonal u) =
      blockDiagonalOne (Fin n) (Fin 1) R
        (diagonalUnitsHom R (Fin n) u) ↔
      Finset.univ.prod u = 1 := by
  constructor
  · intro h
    have hM : (↑(diagonalUnitsHom R (Fin n ⊕ Fin 1)
        (productOneDiagonal u)) :
        Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R) =
        ↑(blockDiagonalOne (Fin n) (Fin 1) R
          (diagonalUnitsHom R (Fin n) u)) := by rw [h]
    simp only [coe_diagonalUnitsHom,
      coe_blockDiagonalOne] at hM
    have h_entry : (Matrix.diagonal (fun s =>
        (productOneDiagonal (R := R) u s : R)))
        (Sum.inr (0 : Fin 1)) (Sum.inr (0 : Fin 1)) =
        (Matrix.fromBlocks
          (Matrix.diagonal (fun i : Fin n => (u i : R)))
          0 0 (1 : Matrix (Fin 1) (Fin 1) R))
          (Sum.inr 0) (Sum.inr 0) := by rw [hM]
    simp only [Matrix.diagonal_apply_eq,
      Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq,
      productOneDiagonal] at h_entry
    have h_val : ((Finset.univ.prod u)⁻¹ : Rˣ).val = (1 : R) :=
      h_entry
    have h_unit : (Finset.univ.prod u)⁻¹ = 1 := Units.ext h_val
    calc Finset.univ.prod u
        = ((Finset.univ.prod u)⁻¹)⁻¹ := by rw [inv_inv]
      _ = (1 : Rˣ)⁻¹ := by rw [h_unit]
      _ = 1 := inv_one
  · intro h_prod
    have h_inv : (Finset.univ.prod u)⁻¹ = 1 := by
      rw [h_prod, inv_one]
    apply Units.ext
    simp only [coe_diagonalUnitsHom, coe_blockDiagonalOne,
      productOneDiagonal, h_inv]
    have h1 : (Matrix.diagonal (fun _ : Fin 1 => (1 : R))) =
        (1 : Matrix (Fin 1) (Fin 1) R) := by
      simp [Matrix.diagonal_one]
    calc Matrix.diagonal (fun i =>
            ↑(Sum.elim u (fun _ : Fin 1 => (1 : Rˣ)) i))
        = Matrix.diagonal (Sum.elim (fun i : Fin n => (u i : R))
            fun _ : Fin 1 => (1 : R)) := by
          congr 1
          funext s
          cases s <;> rfl
      _ = Matrix.fromBlocks
            (Matrix.diagonal fun i : Fin n => (u i : R))
            0 0 (Matrix.diagonal fun _ : Fin 1 => (1 : R)) := by
          rw [Matrix.fromBlocks_diagonal]
      _ = Matrix.fromBlocks
            (Matrix.diagonal fun i : Fin n => (u i : R))
            0 0 (1 : Matrix (Fin 1) (Fin 1) R) := by
          rw [h1]

/-- After reindexing along `finSumFinEquiv`, the product-one diagonal is the
one-step `blockStabilization` of the original diagonal exactly when the
coordinate product is one. Uniform at `n = 0` and does not shift the stage. -/
theorem reindex_diagonalUnitsHom_productOneDiagonal_eq_blockStabilization_iff
    {R : Type*} [CommRing R] {n : ℕ} (u : Fin n → Rˣ) :
    reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
      (diagonalUnitsHom R (Fin n ⊕ Fin 1) (productOneDiagonal (R := R) u)) =
    blockStabilization n 1 R (diagonalUnitsHom R (Fin n) u) ↔
    Finset.univ.prod u = 1 := by
  have h_stab :
      blockStabilization n 1 R (diagonalUnitsHom R (Fin n) u) =
        reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
          (blockDiagonalOne (Fin n) (Fin 1) R
            (diagonalUnitsHom R (Fin n) u)) := rfl
  rw [h_stab]
  have h_inj := (reindexMulEquiv
      (finSumFinEquiv (m := n) (n := 1)) (A := R)).injective
  rw [h_inj.eq_iff]
  exact diagonalUnitsHom_productOneDiagonal_eq_blockDiagonalOne_iff u

/-- Product-one diagonal matrices over a field lie in the elementary subgroup. -/
theorem diagonalUnitsHom_productOneDiagonal_mem_elementarySubgroup
    {F : Type*} [Field F] {n : ℕ} (u : Fin n → Fˣ) :
    diagonalUnitsHom F (Fin n ⊕ Fin 1) (productOneDiagonal u) ∈
      elementarySubgroup (Fin n ⊕ Fin 1) F := by
  have h_det := det_diagonalUnitsHom_productOneDiagonal (R := F) u
  cases n with
  | zero =>
    have h_eq_one : productOneDiagonal (R := F) u = 1 := by
      funext s
      cases s with
      | inl e => exact Fin.elim0 e
      | inr _ => simp [productOneDiagonal]
    have h_GL_one : diagonalUnitsHom F (Fin 0 ⊕ Fin 1)
        (productOneDiagonal u) = 1 := by
      rw [h_eq_one, map_one]
    rw [h_GL_one]
    exact Subgroup.one_mem _
  | succ m =>
    have : Nontrivial (Fin (Nat.succ m) ⊕ Fin 1) :=
      ⟨⟨Sum.inl 0, Sum.inr 0, by intro h; cases h⟩⟩
    exact mem_elementarySubgroup_of_det_eq_one h_det

/-- Boundary `diag2n` product equals reindexed product-one diagonal.
For `u : Fin n → Fˣ`, `diag2n (castSucc_ne_last i)` has `u i` at
`castSucc i` and `(u i)⁻¹` at `last`. Product is diagonal with `u i`
at `castSucc i` and `(∏ u)⁻¹` at `last`, equal to
`diagonalUnitsHom (productOneDiagonal u)` reindexed by `finSumFinEquiv`.
Uniform for `n = 0` and char 2. Orientation:
`∏ i, toGL (diag2n ...) = reindex finSumFinEquiv (diagonalUnitsHom ...)`. -/
theorem boundary_diag2n_prod_eq_reindex_diagonalUnitsHom_productOneDiagonal
    {F : Type*} [Field F] {n : ℕ} (u : Fin n → Fˣ) :
    (Finset.univ.noncommProd (fun i : Fin n =>
      (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.diag2n (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
        Matrix.GeneralLinearGroup (Fin (n + 1)) F))
      (fun (i : Fin n) _ (j : Fin n) _ _hij => by
        apply Units.ext
        simp only [Units.val_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
          Matrix.SpecialLinearGroup.diag2n_coe, Matrix.diagonal_mul_diagonal]
        congr 1; funext k; exact mul_comm _ _)) =
    Matrix.GeneralLinearGroup.reindexMulEquiv (finSumFinEquiv (m := n) (n := 1))
      (diagonalUnitsHom F (Fin n ⊕ Fin 1) (productOneDiagonal (R := F) u)) := by
  let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv (m := n) (n := 1)
  let fU : Fin n ⊕ Fin 1 → Fˣ := productOneDiagonal (R := F) u
  let D : Fin (n + 1) → F := fun j => (fU (e.symm j) : F)
  let de : Fin n → Fin (n + 1) → F := fun i k =>
    if k = Fin.castSucc i then (u i : F) else if k = Fin.last n then (u i : F)⁻¹ else 1
  have hdeM : ∀ i : Fin n,
    ((Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.diag2n (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    Matrix.diagonal (de i) := by intro i; rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.diag2n_coe]
  have hComm : Set.Pairwise (↑(Finset.univ (α := Fin n)) : Set (Fin n))
    (Function.onFun Commute (fun i => (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.diag2n (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F))) := by
    intro i _ j _ _; apply Units.ext
    simp only [Units.val_mul, hdeM i, hdeM j, Matrix.diagonal_mul_diagonal]
    congr 1; funext k; exact mul_comm _ _
  have hProdM : ∀ (s : Finset (Fin n)) (hC : Set.Pairwise (↑s : Set (Fin n))
    (Function.onFun Commute (fun i => (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.diag2n (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F)))),
    (↑(s.noncommProd (fun i => (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.diag2n (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F)) hC) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    Matrix.diagonal (fun k => s.prod (fun i => de i k)) := by
    intro s; induction s using Finset.cons_induction with
    | empty => intro _; simp [Matrix.diagonal_one]
    | cons a s ha ih =>
      intro hC
      have hC' : Set.Pairwise (↑s : Set (Fin n))
          (Function.onFun Commute (fun i =>
            (Matrix.SpecialLinearGroup.toGL
              (Matrix.SpecialLinearGroup.diag2n
                (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
              Matrix.GeneralLinearGroup (Fin (n + 1)) F))) := by
        intro x hx y hy hxy
        exact hC (Finset.mem_coe.mpr
          (Finset.mem_cons_of_mem (Finset.mem_coe.mp hx)))
          (Finset.mem_coe.mpr
            (Finset.mem_cons_of_mem (Finset.mem_coe.mp hy))) hxy
      have hs_eq := ih hC'
      ext i j
      simp only [Finset.noncommProd_cons, Units.val_mul,
        hdeM a, hs_eq, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp only [Finset.prod_cons]
      · simp [hij]
  have hUnivM : (↑(Finset.univ.noncommProd (fun i : Fin n =>
    (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.diag2n (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F)) hComm) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
    Matrix.diagonal (fun k => Finset.univ.prod (fun i => de i k)) := hProdM _ _
  have hdeCS : ∀ (i j : Fin n), de i (Fin.castSucc j) = if i = j then (u j : F) else 1 := by
    intro i j; simp only [de]; by_cases hij : i = j
    · subst hij; simp
    · have h1 : Fin.castSucc j ≠ Fin.castSucc i := by
        intro heq; exact hij (Fin.castSucc_injective n heq).symm
      have h2 : Fin.castSucc j ≠ Fin.last n := Fin.castSucc_ne_last j
      simp [h1, h2, hij]
  have hPt : ∀ k : Fin (n + 1), Finset.univ.prod (fun i => de i k) = D k := by
    intro k; rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
    · have heq : (fun i => de i (Fin.castSucc j)) =
          (fun i => if i = j then (u j : F) else 1) := by
        funext i; exact hdeCS i j
      rw [heq]
      have h_prod : Finset.univ.prod
            (fun i => if i = j then (u j : F) else 1) = (u j : F) := by
        exact
          (Fintype.prod_ite_eq' (M := F) j fun _ : Fin n => (u j : F))
      rw [h_prod]
      simp only [D, fU, productOneDiagonal, e,
        finSumFinEquiv_symm_apply_castSucc, Sum.elim_inl]
    · have hL : ∀ i : Fin n, de i (Fin.last n) = (u i : F)⁻¹ := by
        intro i
        simp only [de, (Fin.castSucc_ne_last i).symm, ite_false, ite_true]
      have hPL : Finset.univ.prod (fun i => de i (Fin.last n)) =
          Finset.univ.prod fun i => (u i : F)⁻¹ := by
        congr 1; funext i; exact hL i
      rw [hPL]
      have h_prod_val : Finset.univ.prod (fun i => (u i : F)⁻¹) =
          (↑(Finset.univ.prod fun i => (u i)⁻¹ : Fˣ) : F) := by
        simpa only [Units.val_inv_eq_inv_val] using
          (Units.coe_prod (fun i : Fin n => (u i)⁻¹) Finset.univ).symm
      rw [h_prod_val, Finset.prod_inv_distrib]
      simp only [D, fU, productOneDiagonal, e, finSumFinEquiv_symm_last,
        Sum.elim_inr, Units.val_inv_eq_inv_val]
  have hLHS : (↑(Finset.univ.noncommProd (fun i : Fin n =>
    (Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.diag2n (Fin.castSucc_ne_last i) (u i : F) (u i).ne_zero) :
      Matrix.GeneralLinearGroup (Fin (n + 1)) F)) hComm) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F) = Matrix.diagonal D := by
    rw [hUnivM]; congr 1; funext k; exact hPt k
  have hRHS : (↑(Matrix.GeneralLinearGroup.reindexMulEquiv e
    (diagonalUnitsHom F (Fin n ⊕ Fin 1) fU) : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F) = Matrix.diagonal D := by
    simp only [Matrix.GeneralLinearGroup.coe_reindexMulEquiv,
      coe_diagonalUnitsHom]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.diagonal_apply, D]
    by_cases hij : i = j
    · subst hij; simp
    · have h_ne : e.symm i ≠ e.symm j := fun h_eq =>
        hij (e.symm.injective h_eq)
      simp [hij, h_ne]
  apply Units.ext; rw [hLHS, hRHS]

end Matrix.GeneralLinearGroup
