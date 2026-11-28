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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Whitehead
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.BlockElementary

/-!
# Two-coordinate diagonal matrices in the elementary subgroup

Over a field, determinant-one diagonal matrices supported on two distinct
coordinates (`diag2n` with entries `a` and `a⁻¹` and `1` elsewhere) lie in the
elementary subgroup.
-/

@[expose] public section

namespace Matrix.SpecialLinearGroup

open Matrix.GeneralLinearGroup

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {F : Type*} [Field F]

/-- **Two marked indices as two singleton summands.** Let ι be an index type with
decidable equality and i,j∈ι with i≠j. The union of these two indices is
equivalent to Fin 1⊕Fin 1. No field or finiteness assumption is required. -/
def twoEquiv {i j : ι} (hij : i ≠ j) :
    Fin 1 ⊕ Fin 1 ≃ {k : ι // k = i ∨ k = j} where
  toFun
    | Sum.inl _ => ⟨i, Or.inl rfl⟩
    | Sum.inr _ => ⟨j, Or.inr rfl⟩
  invFun k := if k.val = i then Sum.inl 0 else Sum.inr 0
  left_inv := by
    intro x
    cases x with
    | inl y => fin_cases y; simp
    | inr y => fin_cases y; simp [hij.symm]
  right_inv := by
    intro k
    obtain ⟨k, hk⟩ := k
    by_cases h : k = i
    · subst h; simp
    · have hk' : k = j := by
        rcases hk with rfl | rfl
        · exact absurd rfl h
        · rfl
      subst hk'; simp [h]

/-- **Two marked indices and their complement exhaust the index type.** Let ι be
an index type with decidable equality and i,j∈ι with i≠j. There is an equivalence
Fin 2⊕{k∈ι | k≠i and k≠j}≃ι sending the two marked coordinates to i and j.
No field or finiteness assumption is required. -/
def pairComplEquiv {i j : ι} (hij : i ≠ j) :
    Fin 2 ⊕ {k : ι // ¬(k = i ∨ k = j)} ≃ ι :=
  let p : ι → Prop := fun k => k = i ∨ k = j
  let ePair : Fin 2 ≃ {k : ι // p k} :=
    (finSumFinEquiv (m := 1) (n := 1)).symm.trans (twoEquiv hij)
  (Equiv.sumCongr ePair (Equiv.refl _)).trans (Equiv.sumCompl p)

omit [Fintype ι] in
/-- **The first marked index returns to the first coordinate.** Let ι have
decidable equality and i,j∈ι satisfy i≠j. The inverse of pairComplEquiv maps
i to the Fin 2 summand's coordinate zero. No finiteness hypothesis is required. -/
@[simp]
theorem pairComplEquiv_symm_apply_i {i j : ι} (hij : i ≠ j) :
    (pairComplEquiv hij).symm i = Sum.inl (0 : Fin 2) := by
  let p : ι → Prop := fun k => k = i ∨ k = j
  have hpi : p i := Or.inl rfl
  have h1 : (Equiv.sumCompl p).symm i = Sum.inl ⟨i, hpi⟩ :=
    Equiv.sumCompl_symm_apply_of_pos hpi
  simp [pairComplEquiv, twoEquiv, finSumFinEquiv]

omit [Fintype ι] in
/-- **The second marked index returns to the second coordinate.** Let ι have
decidable equality and i,j∈ι satisfy i≠j. The inverse of pairComplEquiv maps
j to the Fin 2 summand's coordinate one. No finiteness hypothesis is required. -/
@[simp]
theorem pairComplEquiv_symm_apply_j {i j : ι} (hij : i ≠ j) :
    (pairComplEquiv hij).symm j = Sum.inl (1 : Fin 2) := by
  let p : ι → Prop := fun k => k = i ∨ k = j
  have hpj : p j := Or.inr rfl
  have h1 : (Equiv.sumCompl p).symm j = Sum.inl ⟨j, hpj⟩ :=
    Equiv.sumCompl_symm_apply_of_pos hpj
  simp [pairComplEquiv, twoEquiv, finSumFinEquiv, hij.symm]

/-- **A two-coordinate inverse diagonal is elementary over a field.** Let F be a
field, ι a finite index type with decidable equality, i,j∈ι with i≠j, and a∈F
with a≠0. The diagonal with entries a at i, a⁻¹ at j, and one elsewhere belongs
to the elementary subgroup of GL ι F. -/
theorem toGL_diag2n_mem_elementarySubgroup {i j : ι} (hij : i ≠ j)
    (a : F) (ha : a ≠ 0) :
    (toGL (diag2n hij a ha) : Matrix.GeneralLinearGroup ι F) ∈
      Matrix.GeneralLinearGroup.elementarySubgroup ι F := by
  let u : Fˣ := Units.mk0 a ha
  let g : Matrix.GeneralLinearGroup (Fin 1) F :=
    Matrix.GeneralLinearGroup.scalar (Fin 1) u
  have hg_mem : Matrix.GeneralLinearGroup.diagUnit g ∈
      Matrix.GeneralLinearGroup.elementarySubgroup (Fin 1 ⊕ Fin 1) F :=
    Matrix.GeneralLinearGroup.diagUnit_mem g
  let p : ι → Prop := fun k => k = i ∨ k = j
  let C := {k : ι // ¬ p k}
  let e₀ : (Fin 1 ⊕ Fin 1) ⊕ C ≃ {k : ι // p k} ⊕ C :=
    Equiv.sumCongr (twoEquiv hij) (Equiv.refl C)
  let e : (Fin 1 ⊕ Fin 1) ⊕ C ≃ ι :=
    e₀.trans (Equiv.sumCompl p)
  have h_block :
      Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 1 ⊕ Fin 1) C F
        (Matrix.GeneralLinearGroup.diagUnit g) ∈
        Matrix.GeneralLinearGroup.elementarySubgroup
          ((Fin 1 ⊕ Fin 1) ⊕ C) F :=
    Matrix.GeneralLinearGroup.BlockElementary.blockDiagonalOne_mem_elementarySubgroup hg_mem
  have h_reindex :
      (Matrix.GeneralLinearGroup.reindexMulEquiv e
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 1 ⊕ Fin 1) C F
          (Matrix.GeneralLinearGroup.diagUnit g))) ∈
        Matrix.GeneralLinearGroup.elementarySubgroup ι F :=
    Matrix.GeneralLinearGroup.reindexMulEquiv_mem_elementarySubgroup e h_block
  suffices heq :
      (Matrix.GeneralLinearGroup.reindexMulEquiv e
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 1 ⊕ Fin 1) C F
          (Matrix.GeneralLinearGroup.diagUnit g)) :
        Matrix.GeneralLinearGroup ι F) =
      (toGL (diag2n hij a ha) : Matrix.GeneralLinearGroup ι F) from
    heq ▸ h_reindex
  apply Units.ext
  have hD_eq : (diag2n hij a ha).1 =
      Matrix.diagonal (fun k : ι => if k = i then a else if k = j then a⁻¹ else 1) :=
    diag2n_coe hij a ha
  have h_toGL :
      ((toGL (diag2n hij a ha) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F) =
      Matrix.diagonal (fun k : ι => if k = i then a else if k = j then a⁻¹ else 1) := by
    calc ((toGL (diag2n hij a ha) : Matrix.GeneralLinearGroup ι F) : Matrix ι ι F)
        = (diag2n hij a ha).1 := rfl
      _ = _ := hD_eq
  rw [h_toGL]
  simp only [Matrix.GeneralLinearGroup.coe_reindexMulEquiv,
    Matrix.GeneralLinearGroup.coe_blockDiagonalOne, Matrix.reindex_apply]
  let D : ι → F := fun k => if k = i then a else if k = j then a⁻¹ else 1
  let d₁ : Fin 1 ⊕ Fin 1 → F := Sum.elim (fun _ : Fin 1 => a) (fun _ : Fin 1 => a⁻¹)
  let d : (Fin 1 ⊕ Fin 1) ⊕ C → F := Sum.elim d₁ (fun _ : C => 1)
  have hg_coe : (↑g : Matrix (Fin 1) (Fin 1) F) = Matrix.diagonal (fun _ : Fin 1 => a) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [g, u, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
  have hg_inv_coe : (↑(g⁻¹) : Matrix (Fin 1) (Fin 1) F) =
      Matrix.diagonal (fun _ : Fin 1 => a⁻¹) := by
    ext i j
    fin_cases i
    fin_cases j
    simp [g, u, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply]
  have h_diagUnit : (↑(Matrix.GeneralLinearGroup.diagUnit g) :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) = Matrix.diagonal d₁ := by
    rw [Matrix.GeneralLinearGroup.coe_diagUnit, hg_coe, hg_inv_coe, Matrix.fromBlocks_diagonal]
  have hM : Matrix.fromBlocks
      (↑(Matrix.GeneralLinearGroup.diagUnit g) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F)
      (0 : Matrix (Fin 1 ⊕ Fin 1) C F) (0 : Matrix C (Fin 1 ⊕ Fin 1) F)
      (1 : Matrix C C F) = Matrix.diagonal d := by
    rw [h_diagUnit, ← Matrix.diagonal_one (n := C) (α := F), Matrix.fromBlocks_diagonal]
  have h_reindex_diag :
      (Matrix.fromBlocks
        (↑(Matrix.GeneralLinearGroup.diagUnit g) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F)
        (0 : Matrix (Fin 1 ⊕ Fin 1) C F) (0 : Matrix C (Fin 1 ⊕ Fin 1) F)
        (1 : Matrix C C F)).submatrix ⇑e.symm ⇑e.symm =
      Matrix.diagonal (d ∘ ⇑e.symm) := by
    rw [hM, Matrix.submatrix_diagonal_equiv]
  rw [h_reindex_diag]
  have h_eq : d ∘ ⇑e.symm = D := by
    funext k
    by_cases hki : k = i
    · have hpi : p k := by simp [p, hki]
      have he : e.symm k = Sum.inl (Sum.inl (0 : Fin 1)) := by
        have h1 : (Equiv.sumCompl p).symm k = Sum.inl ⟨k, hpi⟩ :=
          Equiv.sumCompl_symm_apply_of_pos hpi
        have h2 : e₀.symm (Sum.inl ⟨k, hpi⟩) = Sum.inl (Sum.inl (0 : Fin 1)) := by
          simp [e₀, twoEquiv, hki]
        calc e.symm k = e₀.symm ((Equiv.sumCompl p).symm k) := by simp [e]
          _ = e₀.symm (Sum.inl ⟨k, hpi⟩) := by rw [h1]
          _ = Sum.inl (Sum.inl (0 : Fin 1)) := h2
      have hD : D k = a := by simp [D, hki]
      simp [he, hD, d, d₁]
    · by_cases hkj : k = j
      · have hpj : p k := by simp [p, hkj]
        have he : e.symm k = Sum.inl (Sum.inr (0 : Fin 1)) := by
          have h1 : (Equiv.sumCompl p).symm k = Sum.inl ⟨k, hpj⟩ :=
            Equiv.sumCompl_symm_apply_of_pos hpj
          have h2 : e₀.symm (Sum.inl ⟨k, hpj⟩) = Sum.inl (Sum.inr (0 : Fin 1)) := by
            simp [e₀, twoEquiv, hij.symm, hkj]
          calc e.symm k = e₀.symm ((Equiv.sumCompl p).symm k) := by simp [e]
            _ = e₀.symm (Sum.inl ⟨k, hpj⟩) := by rw [h1]
            _ = Sum.inl (Sum.inr (0 : Fin 1)) := h2
        have hD : D k = a⁻¹ := by simp [D, hkj, hij.symm]
        simp [he, hD, d, d₁]
      · have hnp : ¬ p k := by simp [p, hki, hkj]
        have he : e.symm k = Sum.inr ⟨k, hnp⟩ := by
          have h1 : (Equiv.sumCompl p).symm k = Sum.inr ⟨k, hnp⟩ :=
            Equiv.sumCompl_symm_apply_of_neg hnp
          calc e.symm k = e₀.symm ((Equiv.sumCompl p).symm k) := by simp [e]
            _ = e₀.symm (Sum.inr ⟨k, hnp⟩) := by rw [h1]
            _ = Sum.inr ⟨k, hnp⟩ := by simp [e₀]
        have hD : D k = 1 := by simp [D, hki, hkj]
        simp [he, hD, d]
  rw [h_eq]

/-- **A marked inverse diagonal is an identity-block extension.** Let F be a field,
ι a finite index type with decidable equality, i,j∈ι with i≠j, and u∈Fˣ.
The diagonal u,u⁻¹ at i,j and one elsewhere is the Fin 2 diagonal diag2,
adjoined to the identity on the complementary indices and reindexed by pairComplEquiv. -/
theorem toGL_diag2n_eq_reindex_blockDiagonalOne_diag2 {i j : ι} (hij : i ≠ j)
    (u : Fˣ) :
    (toGL (diag2n hij (u : F) u.ne_zero) : Matrix.GeneralLinearGroup ι F) =
      Matrix.GeneralLinearGroup.reindexMulEquiv (pairComplEquiv hij)
        (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
          {k : ι // ¬(k = i ∨ k = j)} F
          (toGL (diag2 (u : F) u.ne_zero) :
            Matrix.GeneralLinearGroup (Fin 2) F)) := by
  apply Units.ext
  have hD : (diag2n hij (u : F) u.ne_zero).1 =
      Matrix.diagonal
        (fun k => if k = i then (u : F) else if k = j then (u : F)⁻¹ else 1) :=
    diag2n_coe hij _ _
  have h_toGL : ((toGL (diag2n hij (u : F) u.ne_zero) : Matrix.GeneralLinearGroup ι F) :
      Matrix ι ι F) = Matrix.diagonal
        (fun k => if k = i then (u : F) else if k = j then (u : F)⁻¹ else 1) := by
    calc _ = (diag2n hij (u : F) u.ne_zero).1 := rfl
      _ = _ := hD
  rw [h_toGL]
  simp only [Matrix.GeneralLinearGroup.coe_reindexMulEquiv,
    Matrix.GeneralLinearGroup.coe_blockDiagonalOne, Matrix.reindex_apply]
  let p : ι → Prop := fun k => k = i ∨ k = j
  let C := {k : ι // ¬p k}
  let e : Fin 2 ⊕ C ≃ ι := pairComplEquiv hij
  let D : ι → F := fun k => if k = i then (u : F)
    else if k = j then (u : F)⁻¹ else 1
  let d₂ : Fin 2 → F := fun k => if k = 0 then (u : F) else (u : F)⁻¹
  let d : Fin 2 ⊕ C → F := Sum.elim d₂ (fun _ : C => 1)
  have h_diag2 : (↑(toGL (diag2 (u : F) u.ne_zero) :
      Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal d₂ := by
    have h := diag2n_coe (ι := Fin 2) zero_ne_one (u : F) u.ne_zero
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h, d₂]
  have hM : Matrix.fromBlocks
      (↑(toGL (diag2 (u : F) u.ne_zero) :
        Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      (0 : Matrix (Fin 2) C F) (0 : Matrix C (Fin 2) F)
      (1 : Matrix C C F) = Matrix.diagonal d := by
    rw [h_diag2, ← Matrix.diagonal_one (n := C) (α := F),
      Matrix.fromBlocks_diagonal]
  have h_reindex :
      (Matrix.fromBlocks
        (↑(toGL (diag2 (u : F) u.ne_zero) :
          Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        (0 : Matrix (Fin 2) C F) (0 : Matrix C (Fin 2) F)
        (1 : Matrix C C F)).submatrix ⇑e.symm ⇑e.symm =
      Matrix.diagonal (d ∘ ⇑e.symm) := by
    rw [hM, Matrix.submatrix_diagonal_equiv]
  rw [h_reindex]
  have h_eq : d ∘ ⇑e.symm = D := by
    funext k
    by_cases hki : k = i
    · have he : e.symm k = Sum.inl (0 : Fin 2) := by
        rw [hki]; exact pairComplEquiv_symm_apply_i hij
      have hD : D k = (u : F) := by simp [D, hki]
      simp only [Function.comp_apply, d, d₂, he, hD, Sum.elim_inl]
      simp
    · by_cases hkj : k = j
      · have he : e.symm k = Sum.inl (1 : Fin 2) := by
          rw [hkj]; exact pairComplEquiv_symm_apply_j hij
        have hD : D k = (u : F)⁻¹ := by simp [D, hkj, hij.symm]
        simp only [Function.comp_apply, d, d₂, he, hD, Sum.elim_inl]
        simp
      · have hnp : ¬p k := by simp [p, hki, hkj]
        have h1 : (Equiv.sumCompl
            (fun k : ι => k = i ∨ k = j)).symm k = Sum.inr ⟨k, hnp⟩ :=
          Equiv.sumCompl_symm_apply_of_neg hnp
        have he : e.symm k = Sum.inr ⟨k, hnp⟩ := by
          calc e.symm k = (pairComplEquiv hij).symm k := rfl
            _ = Sum.inr ⟨k, hnp⟩ := by simp [pairComplEquiv, h1]
        have hD : D k = 1 := by simp [D, hki, hkj]
        simp only [Function.comp_apply, d, he, hD, Sum.elim_inr]
  rw [h_eq]

private lemma toGL_transvection_eq_elementary {i j : Fin 2} (hij : i ≠ j) (a : F) :
    (toGL (transvection hij a) : Matrix.GeneralLinearGroup (Fin 2) F) =
      Matrix.GeneralLinearGroup.elementary i j hij a := by
  apply Units.ext
  simp [Matrix.SpecialLinearGroup.transvection_coe]

/-- **Six transvections factor a two-dimensional inverse diagonal.** Let F be a
field and u∈Fˣ. Write Eᵢⱼ(a)=I+a eᵢⱼ. In GL (Fin 2) F,
diag(u,u⁻¹)=E₀₁(u)E₁₀(−u⁻¹)E₀₁(u)E₀₁(−1)E₁₀(1)E₀₁(−1), in that order. -/
theorem toGL_diag2_eq_six_elementary (u : Fˣ) :
    (toGL (diag2 (u : F) u.ne_zero) : Matrix.GeneralLinearGroup (Fin 2) F) =
      Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
        Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero (-((u : F)⁻¹)) *
          Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
            Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1) *
              Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero 1 *
                Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1) := by
  have h := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin 2) F =>
      (toGL A : Matrix.GeneralLinearGroup (Fin 2) F))
    (diag2_decompose (u : F) u.ne_zero)
  simpa only [map_mul, toGL_transvection_eq_elementary] using h

/-- **Six transvections factor a marked inverse diagonal.** Let F be a field,
ι a finite index type with decidable equality, i,j∈ι with i≠j, and u∈Fˣ.
With Eᵢⱼ(a)=I+a eᵢⱼ, the diagonal u,u⁻¹ at i,j and one elsewhere equals
Eᵢⱼ(u)Eⱼᵢ(−u⁻¹)Eᵢⱼ(u)Eᵢⱼ(−1)Eⱼᵢ(1)Eᵢⱼ(−1), in the displayed order. -/
theorem toGL_diag2n_eq_six_elementary {i j : ι} (hij : i ≠ j) (u : Fˣ) :
    (toGL (diag2n hij (u : F) u.ne_zero) : Matrix.GeneralLinearGroup ι F) =
      Matrix.GeneralLinearGroup.elementary i j hij (u : F) *
        Matrix.GeneralLinearGroup.elementary j i hij.symm (-((u : F)⁻¹)) *
          Matrix.GeneralLinearGroup.elementary i j hij (u : F) *
            Matrix.GeneralLinearGroup.elementary i j hij (-1) *
              Matrix.GeneralLinearGroup.elementary j i hij.symm 1 *
                Matrix.GeneralLinearGroup.elementary i j hij (-1) := by
  let e := pairComplEquiv hij
  have hi : e (Sum.inl (0 : Fin 2)) = i := by
    have h : e.symm i = Sum.inl (0 : Fin 2) := pairComplEquiv_symm_apply_i hij
    calc e (Sum.inl (0 : Fin 2)) = e (e.symm i) := by rw [h]
      _ = i := by simp
  have hj : e (Sum.inl (1 : Fin 2)) = j := by
    have h : e.symm j = Sum.inl (1 : Fin 2) := pairComplEquiv_symm_apply_j hij
    calc e (Sum.inl (1 : Fin 2)) = e (e.symm j) := by rw [h]
      _ = j := by simp
  have h01 : ∀ a : F,
      Matrix.GeneralLinearGroup.reindexMulEquiv e
          (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
            {k : ι // ¬(k = i ∨ k = j)} F
            (Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one a)) =
        Matrix.GeneralLinearGroup.elementary i j hij a := by
    intro a
    calc Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
              {k : ι // ¬(k = i ∨ k = j)} F
              (Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one a))
        = Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.elementary
              (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) _ a) := by
          rw [Matrix.GeneralLinearGroup.blockDiagonalOne_elementary]
      _ = Matrix.GeneralLinearGroup.elementary
            (e (Sum.inl (0 : Fin 2))) (e (Sum.inl (1 : Fin 2))) _ a := by
          rw [Matrix.GeneralLinearGroup.reindexMulEquiv_elementary]
      _ = Matrix.GeneralLinearGroup.elementary i j hij a := by
          apply Units.ext; simp [hi, hj]
  have h10 : ∀ a : F,
      Matrix.GeneralLinearGroup.reindexMulEquiv e
          (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
            {k : ι // ¬(k = i ∨ k = j)} F
            (Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero a)) =
        Matrix.GeneralLinearGroup.elementary j i hij.symm a := by
    intro a
    calc Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
              {k : ι // ¬(k = i ∨ k = j)} F
              (Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero a))
        = Matrix.GeneralLinearGroup.reindexMulEquiv e
            (Matrix.GeneralLinearGroup.elementary
              (Sum.inl (1 : Fin 2)) (Sum.inl (0 : Fin 2)) _ a) := by
          rw [Matrix.GeneralLinearGroup.blockDiagonalOne_elementary]
      _ = Matrix.GeneralLinearGroup.elementary
            (e (Sum.inl (1 : Fin 2))) (e (Sum.inl (0 : Fin 2))) _ a := by
          rw [Matrix.GeneralLinearGroup.reindexMulEquiv_elementary]
      _ = Matrix.GeneralLinearGroup.elementary j i hij.symm a := by
          apply Units.ext; simp [hj, hi]
  calc (toGL (diag2n hij (u : F) u.ne_zero) : Matrix.GeneralLinearGroup ι F)
      = Matrix.GeneralLinearGroup.reindexMulEquiv e
          (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
            {k : ι // ¬(k = i ∨ k = j)} F
            (toGL (diag2 (u : F) u.ne_zero) :
              Matrix.GeneralLinearGroup (Fin 2) F)) :=
        toGL_diag2n_eq_reindex_blockDiagonalOne_diag2 hij u
    _ = Matrix.GeneralLinearGroup.reindexMulEquiv e
          (Matrix.GeneralLinearGroup.blockDiagonalOne (Fin 2)
            {k : ι // ¬(k = i ∨ k = j)} F
            (Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
              Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero (-((u : F)⁻¹)) *
                Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (u : F) *
                  Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1) *
                    Matrix.GeneralLinearGroup.elementary 1 0 one_ne_zero 1 *
                      Matrix.GeneralLinearGroup.elementary 0 1 zero_ne_one (-1))) := by
        rw [toGL_diag2_eq_six_elementary]
    _ = Matrix.GeneralLinearGroup.elementary i j hij (u : F) *
          Matrix.GeneralLinearGroup.elementary j i hij.symm (-((u : F)⁻¹)) *
            Matrix.GeneralLinearGroup.elementary i j hij (u : F) *
              Matrix.GeneralLinearGroup.elementary i j hij (-1) *
                Matrix.GeneralLinearGroup.elementary j i hij.symm 1 *
                  Matrix.GeneralLinearGroup.elementary i j hij (-1) := by
        simp only [map_mul, h01, h10]

end Matrix.SpecialLinearGroup
