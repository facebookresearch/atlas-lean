/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Matrix morphisms in the finite-row idempotent model

A rectangular matrix satisfying the two idempotent corner conditions defines
a morphism in the finite-row Karoubi model.  This is the public Ring-generic
constructor used by block-biproduct and algebraic-equivalence comparisons.
-/

@[expose] public section

namespace FGProjectiveCat.IdempotentModel

noncomputable section

universe u

/-- Construct a finite-row Karoubi morphism from a rectangular matrix in the
appropriate source/target corner. -/
noncomputable def homOfMatrix
    (A : Type u) [Ring A]
    {P Q : FGProjectiveCat.IdempotentModel A}
    (b : Matrix (Fin P.X) (Fin Q.X) A)
    (hb : rowHomEquiv A P.X P.X P.p * b *
      rowHomEquiv A Q.X Q.X Q.p = b) : P ⟶ Q where
  f := (rowHomEquiv A P.X Q.X).symm b
  comm := by
    apply (rowHomEquiv A P.X Q.X).injective
    rw [(equivalence_characteristic A).2.2.1,
      (equivalence_characteristic A).2.2.1]
    simpa only [AddEquiv.apply_symm_apply, Matrix.mul_assoc] using hb

/-- The row matrix of `homOfMatrix` is the supplied rectangular matrix. -/
@[simp]
theorem homOfMatrix_matrix
    (A : Type u) [Ring A]
    {P Q : FGProjectiveCat.IdempotentModel A}
    (b : Matrix (Fin P.X) (Fin Q.X) A)
    (hb : rowHomEquiv A P.X P.X P.p * b *
      rowHomEquiv A Q.X Q.X Q.p = b) :
    rowHomEquiv A P.X Q.X (homOfMatrix A b hb).f = b :=
  AddEquiv.apply_symm_apply _ _

section BlockModels

open CategoryTheory CategoryTheory.Limits

universe v

local instance canonicalFiniteRowsCategory (A : Type u) [Ring A] :
    Category.{u} (FGProjectiveCat.FiniteRowRanks A) := by
  unfold FGProjectiveCat.FiniteRowRanks
  infer_instance

/-- The finite row model of an actual idempotent square matrix. -/
@[reducible] def matrixModel (A : Type u) [Ring A] {n : ℕ}
    (p : Matrix (Fin n) (Fin n) A) (hp : p * p = p) : IdempotentModel A where
  X := n
  p := (rowHomEquiv A n n).symm p
  idem := by
    apply (rowHomEquiv A n n).injective
    rw [(equivalence_characteristic A).2.2.1]
    simp only [AddEquiv.apply_symm_apply]
    exact hp

/-- The whole row matrix of the actual idempotent model. -/
theorem matrixModel_matrix (A : Type u) [Ring A] {n : ℕ}
    (p : Matrix (Fin n) (Fin n) A) (hp : p * p = p) :
    rowHomEquiv A n n (matrixModel A p hp).p = p :=
  AddEquiv.apply_symm_apply _ _

/-- The literal block diagonal, reindexed into the original sum of finite ranks. -/
def blockMatrix (A : Type u) [Ring A] {n m : ℕ}
    (p : Matrix (Fin n) (Fin n) A) (q : Matrix (Fin m) (Fin m) A) :
    Matrix (Fin (n + m)) (Fin (n + m)) A :=
  Matrix.reindexLinearEquiv A A (finSumFinEquiv (m := n) (n := m))
    (finSumFinEquiv (m := n) (n := m)) (Matrix.fromBlocks p 0 0 q)

/-- Entrywise ring maps preserve both whole blocks and their literal finite-rank reindexing. -/
theorem blockMatrix_map {A : Type u} {B : Type v} [Ring A] [Ring B]
    (f : A →+* B) {n m : ℕ} (p : Matrix (Fin n) (Fin n) A) (q : Matrix (Fin m) (Fin m) A) :
    (blockMatrix A p q).map f = blockMatrix B (p.map f) (q.map f) := by
  let e := finSumFinEquiv (m := n) (n := m)
  have h : (Matrix.fromBlocks p 0 0 q : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) A).map f =
      Matrix.fromBlocks (p.map f) 0 0 (q.map f) := by
    simp only [Matrix.fromBlocks_map, Matrix.map_zero f f.map_zero]
  apply Matrix.ext
  intro i j
  exact congrArg (fun a : Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) B => a (e.symm i) (e.symm j)) h

/-- The whole block diagonal of two actual idempotents is idempotent. -/
theorem blockMatrix_idempotent (A : Type u) [Ring A] {n m : ℕ}
    (p : Matrix (Fin n) (Fin n) A) (q : Matrix (Fin m) (Fin m) A)
    (hp : p * p = p) (hq : q * q = q) :
    blockMatrix A p q * blockMatrix A p q = blockMatrix A p q := by
  unfold blockMatrix
  rw [Matrix.reindexLinearEquiv_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp only [hp, hq, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

/-- The original row model of the full block diagonal of two finite idempotent models. -/
@[reducible] def blockModel (A : Type u) [Ring A] (P Q : IdempotentModel A) :
    IdempotentModel A :=
  matrixModel A
    (blockMatrix A (rowHomEquiv A P.X P.X P.p) (rowHomEquiv A Q.X Q.X Q.p))
    (blockMatrix_idempotent A _ _ ((equivalence_characteristic A).2.2.2.1 P)
      ((equivalence_characteristic A).2.2.2.1 Q))

/-- The literal block model has the sum of the two original ambient finite ranks. -/
theorem blockModel_rank (A : Type u) [Ring A] (P Q : IdempotentModel A) :
    let n : ℕ := P.X
    let m : ℕ := Q.X
    (blockModel A P Q).X = n + m := rfl

/-- The whole row matrix of the literal block model retains both original idempotents. -/
theorem blockModel_matrix (A : Type u) [Ring A] (P Q : IdempotentModel A) :
    let n : ℕ := P.X
    let m : ℕ := Q.X
    rowHomEquiv A (n + m) (n + m) (blockModel A P Q).p =
      blockMatrix A (rowHomEquiv A P.X P.X P.p) (rowHomEquiv A Q.X Q.X Q.p) :=
  matrixModel_matrix A _ _

/-- The literal block model is a genuine biproduct, with its actual rectangular
inclusions and projections providing both complete inverse equations. -/
def blockModelIso (A : Type u) [Ring A] (P Q : IdempotentModel A) :
    blockModel A P Q ≅ P ⊞ Q := by
  let n : ℕ := P.X
  let m : ℕ := Q.X
  let p := rowHomEquiv A P.X P.X P.p
  let q := rowHomEquiv A Q.X Q.X Q.p
  let E := finSumFinEquiv (m := P.X) (n := Q.X)
  let b := blockMatrix A p q
  let H := blockModel A P Q
  have hp : p * p = p := (equivalence_characteristic A).2.2.2.1 P
  have hq : q * q = q := (equivalence_characteristic A).2.2.2.1 Q
  let iM : Matrix (Fin n) (Fin (n + m)) A :=
    Matrix.reindexLinearEquiv A A (Equiv.refl _) E (Matrix.fromCols p 0)
  let rM : Matrix (Fin (n + m)) (Fin n) A :=
    Matrix.reindexLinearEquiv A A E (Equiv.refl _) (Matrix.fromRows p 0)
  let sM : Matrix (Fin m) (Fin (n + m)) A :=
    Matrix.reindexLinearEquiv A A (Equiv.refl _) E (Matrix.fromCols 0 q)
  let tM : Matrix (Fin (n + m)) (Fin m) A :=
    Matrix.reindexLinearEquiv A A E (Equiv.refl _) (Matrix.fromRows 0 q)
  have hi : p * iM * b = iM := by
    change (Matrix.reindexLinearEquiv A A (Equiv.refl _) (Equiv.refl _) p) * iM * b = iM
    dsimp only [iM, b, blockMatrix, E]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
    congr 1
    simp only [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hp,
      Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hr : b * rM * p = rM := by
    change b * rM * (Matrix.reindexLinearEquiv A A (Equiv.refl _) (Equiv.refl _) p) = rM
    dsimp only [rM, b, blockMatrix, E]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
    congr 1
    simp only [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, hp,
      Matrix.mul_zero, Matrix.zero_mul, add_zero]
  have hs : q * sM * b = sM := by
    change (Matrix.reindexLinearEquiv A A (Equiv.refl _) (Equiv.refl _) q) * sM * b = sM
    dsimp only [sM, b, blockMatrix, E]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
    congr 1
    simp only [Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hq,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have ht : b * tM * q = tM := by
    change b * tM * (Matrix.reindexLinearEquiv A A (Equiv.refl _) (Equiv.refl _) q) = tM
    dsimp only [tM, b, blockMatrix, E]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul]
    congr 1
    simp only [Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, hq,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hir : iM * rM = p := by
    dsimp only [iM, rM]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_refl_refl,
      Matrix.fromCols_mul_fromRows]
    simp only [hp, Matrix.mul_zero, add_zero]
    rfl
  have hst : sM * tM = q := by
    dsimp only [sM, tM]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_refl_refl,
      Matrix.fromCols_mul_fromRows]
    simp only [hq, Matrix.mul_zero, zero_add]
    rfl
  have hit : iM * tM = 0 := by
    dsimp only [iM, tM]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_refl_refl,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rfl
  have hsr : sM * rM = 0 := by
    dsimp only [sM, rM]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_refl_refl,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    rfl
  have hsum : rM * iM + tM * sM = b := by
    dsimp only [rM, iM, tM, sM, b, blockMatrix, E]
    rw [Matrix.reindexLinearEquiv_mul, Matrix.reindexLinearEquiv_mul,
      ← map_add, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols]
    congr 1
    simp only [hp, hq, Matrix.mul_zero, Matrix.zero_mul, Matrix.fromBlocks_add, add_zero, zero_add]
  have hH : rowHomEquiv A H.X H.X H.p = b := by
    exact matrixModel_matrix A b (blockMatrix_idempotent A p q hp hq)
  let i : P ⟶ H := homOfMatrix A iM (by
    change p * iM * rowHomEquiv A H.X H.X H.p = iM
    rw [hH]
    exact hi)
  let r : H ⟶ P := homOfMatrix A rM (by
    change rowHomEquiv A H.X H.X H.p * rM * p = rM
    rw [hH]
    exact hr)
  let s : Q ⟶ H := homOfMatrix A sM (by
    change q * sM * rowHomEquiv A H.X H.X H.p = sM
    rw [hH]
    exact hs)
  let t : H ⟶ Q := homOfMatrix A tM (by
    change rowHomEquiv A H.X H.X H.p * tM * q = tM
    rw [hH]
    exact ht)
  have matrixComp {U V W : IdempotentModel A} (f : U ⟶ V) (g : V ⟶ W) :
      rowHomEquiv A U.X W.X (f ≫ g).f =
        rowHomEquiv A U.X V.X f.f * rowHomEquiv A V.X W.X g.f :=
    (equivalence_characteristic A).2.2.1 _ _ _ f.f g.f
  have hir' : i ≫ r = 𝟙 P := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv A P.X P.X).injective
    rw [matrixComp, homOfMatrix_matrix, homOfMatrix_matrix]
    exact hir
  have hst' : s ≫ t = 𝟙 Q := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv A Q.X Q.X).injective
    rw [matrixComp, homOfMatrix_matrix, homOfMatrix_matrix]
    exact hst
  have hit' : i ≫ t = 0 := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv A P.X Q.X).injective
    rw [matrixComp, homOfMatrix_matrix, homOfMatrix_matrix]
    change iM * tM = rowHomEquiv A P.X Q.X (0 : _)
    rw [map_zero]
    exact hit
  have hsr' : s ≫ r = 0 := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv A Q.X P.X).injective
    rw [matrixComp, homOfMatrix_matrix, homOfMatrix_matrix]
    change sM * rM = rowHomEquiv A Q.X P.X (0 : _)
    rw [map_zero]
    exact hsr
  have hsum' : r ≫ i + t ≫ s = 𝟙 H := by
    apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv A H.X H.X).injective
    change rowHomEquiv A H.X H.X ((r ≫ i).f + (t ≫ s).f) = rowHomEquiv A H.X H.X H.p
    rw [map_add, matrixComp, matrixComp, homOfMatrix_matrix, homOfMatrix_matrix,
      homOfMatrix_matrix, homOfMatrix_matrix, hH]
    exact hsum
  refine ⟨biprod.lift r t, biprod.desc i s, ?_, ?_⟩
  · rw [biprod.lift_desc]
    exact hsum'
  · apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp only [Category.assoc, biprod.lift_fst, Category.comp_id, biprod.inl_fst]
        rw [← Category.assoc, biprod.inl_desc]
        exact hir'
      · simp only [Category.assoc, biprod.lift_snd, Category.comp_id, biprod.inl_snd]
        rw [← Category.assoc, biprod.inl_desc]
        exact hit'
    · apply biprod.hom_ext
      · simp only [Category.assoc, biprod.lift_fst, Category.comp_id, biprod.inr_fst]
        rw [← Category.assoc, biprod.inr_desc]
        exact hsr'
      · simp only [Category.assoc, biprod.lift_snd, Category.comp_id, biprod.inr_snd]
        rw [← Category.assoc, biprod.inr_desc]
        exact hst'

/-- Actual rectangular corner matrices with both inverse equations give an Iso
of the complete original finite idempotent models. -/
def modelIsoOfInverseMatrices (A : Type u) [Ring A] (P Q : IdempotentModel A)
    (b : Matrix (Fin P.X) (Fin Q.X) A) (c : Matrix (Fin Q.X) (Fin P.X) A)
    (hb : rowHomEquiv A P.X P.X P.p * b * rowHomEquiv A Q.X Q.X Q.p = b)
    (hc : rowHomEquiv A Q.X Q.X Q.p * c * rowHomEquiv A P.X P.X P.p = c)
    (hbc : b * c = rowHomEquiv A P.X P.X P.p)
    (hcb : c * b = rowHomEquiv A Q.X Q.X Q.p) : P ≅ Q := by
  let f := homOfMatrix A b hb
  let g := homOfMatrix A c hc
  have hf : rowHomEquiv A P.X Q.X f.f = b := homOfMatrix_matrix A b hb
  have hg : rowHomEquiv A Q.X P.X g.f = c := homOfMatrix_matrix A c hc
  refine ⟨f, g, ?_, ?_⟩
  · apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv A P.X P.X).injective
    change rowHomEquiv A P.X P.X (f.f ≫ g.f) = _
    rw [(equivalence_characteristic A).2.2.1]
    change rowHomEquiv A P.X Q.X f.f * rowHomEquiv A Q.X P.X g.f = _
    rw [hf, hg]
    exact hbc
  · apply Idempotents.Karoubi.hom_ext
    apply (rowHomEquiv A Q.X Q.X).injective
    change rowHomEquiv A Q.X Q.X (g.f ≫ f.f) = _
    rw [(equivalence_characteristic A).2.2.1]
    change rowHomEquiv A Q.X P.X g.f * rowHomEquiv A P.X Q.X f.f = _
    rw [hg, hf]
    exact hcb

end BlockModels

end

end FGProjectiveCat.IdempotentModel
