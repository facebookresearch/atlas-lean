/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.Ring

/-!
# Reindexing and corners of locally finite matrices

Equivalences reindex the original coefficient matrices and their products.
Injections extend a rectangular matrix by zero outside the two original
images. This extension preserves multiplication when the intermediate
injection is the same on both factors. Restriction back to the actual images
returns the original matrix.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe um un up um' un' up' um'' un'' uR uS

namespace Matrix.LocallyFinite

variable {m : Type um} {n : Type un} {p : Type up}
  {m' : Type um'} {n' : Type un'} {p' : Type up'}
  {m'' : Type um''} {n'' : Type un''} {R : Type uR} {S : Type uS}

/-- Reindex the original rows and columns along the supplied actual equivalences. -/
def reindex [Zero R] (e : m ≃ m') (f : n ≃ n') (A : Matrix.LocallyFinite m n R) :
    Matrix.LocallyFinite m' n' R where
  toMatrix := Matrix.reindex e f A.toMatrix
  row_finite i := (A.row_finite (e.symm i)).preimage f.symm.injective.injOn
  column_finite j := (A.column_finite (f.symm j)).preimage e.symm.injective.injOn

/-- Reindexing reads the same original entry at the supplied inverse indices. -/
@[simp]
theorem reindex_apply [Zero R] (e : m ≃ m') (f : n ≃ n')
    (A : Matrix.LocallyFinite m n R) (i : m') (j : n') :
    reindex e f A i j = A (e.symm i) (f.symm j) := rfl

/-- An actual image pair reads its original coefficient. -/
theorem reindex_apply_image [Zero R] (e : m ≃ m') (f : n ≃ n')
    (A : Matrix.LocallyFinite m n R) (i : m) (j : n) :
    reindex e f A (e i) (f j) = A i j := by simp

/-- The exact row of a reindexed matrix is the original Finsupp reindexing. -/
@[simp]
theorem row_reindex [Zero R] (e : m ≃ m') (f : n ≃ n')
    (A : Matrix.LocallyFinite m n R) (i : m') :
    (reindex e f A).row i = Finsupp.equivMapDomain f (A.row (e.symm i)) := by
  ext j
  rfl

/-- Actual inverse reindexing returns the original matrix. -/
@[simp]
theorem reindex_symm [Zero R] (e : m ≃ m') (f : n ≃ n')
    (A : Matrix.LocallyFinite m n R) : reindex e.symm f.symm (reindex e f A) = A := by
  ext i j
  simp

/-- Reindexing by identities retains every original coefficient. -/
@[simp]
theorem reindex_refl [Zero R] (A : Matrix.LocallyFinite m n R) :
    reindex (Equiv.refl m) (Equiv.refl n) A = A := by
  ext i j
  rfl

/-- Composition of the actual index equivalences gives strict reindex composition. -/
theorem reindex_trans [Zero R] (e : m ≃ m') (f : n ≃ n')
    (e' : m' ≃ m'') (f' : n' ≃ n'') (A : Matrix.LocallyFinite m n R) :
    reindex (e.trans e') (f.trans f') A = reindex e' f' (reindex e f A) := by
  ext i j
  rfl

/-- Reindexing retains the original product with the same intermediate equivalence. -/
theorem reindex_comp_product [Semiring R] (e : m ≃ m') (f : n ≃ n') (g : p ≃ p')
    (A : Matrix.LocallyFinite m n R) (B : Matrix.LocallyFinite n p R) :
    (reindex e f A).comp (reindex f g B) = reindex e g (A.comp B) := by
  ext i j
  rw [comp_apply_sum, row_reindex, Finsupp.sum_equivMapDomain]
  simp only [reindex_apply, Equiv.symm_apply_apply, comp_apply_sum]

/-- Reindexing commutes with the actual coefficient map. -/
theorem reindex_map [Zero R] [Zero S] (e : m ≃ m') (f : n ≃ n')
    (g : ZeroHom R S) (A : Matrix.LocallyFinite m n R) :
    reindex e f (map g A) = map g (reindex e f A) := by
  ext i j
  rfl

/-- Reindexing both indices gives an equivalence of the original square matrix rings. -/
def reindexRingEquiv [Semiring R] (e : n ≃ n') :
    Matrix.LocallyFinite n n R ≃+* Matrix.LocallyFinite n' n' R where
  toFun := reindex e e
  invFun := reindex e.symm e.symm
  left_inv := reindex_symm e e
  right_inv A := by simpa using reindex_symm e.symm e.symm A
  map_add' A B := by ext i j; rfl
  map_mul' A B := (reindex_comp_product e e e A B).symm

/-- The square ring equivalence uses the original inverse index formula. -/
@[simp]
theorem reindexRingEquiv_apply [Semiring R] (e : n ≃ n')
    (A : Matrix.LocallyFinite n n R) (i j : n') :
    reindexRingEquiv e A i j = A (e.symm i) (e.symm j) := rfl

/-- The inverse square-ring map returns the same actual original index formula. -/
@[simp]
theorem reindexRingEquiv_symm_apply [Semiring R] (e : n ≃ n')
    (A : Matrix.LocallyFinite n' n' R) (i j : n) :
    (reindexRingEquiv e).symm A i j = A (e i) (e j) := rfl

/-- Actual index identities give the identity equivalence of matrix rings. -/
@[simp]
theorem reindexRingEquiv_refl [Semiring R] :
    reindexRingEquiv (R := R) (Equiv.refl n) = RingEquiv.refl (Matrix.LocallyFinite n n R) := by
  ext A i j
  rfl

/-- Actual index composition gives composition of the original square-ring equivalences. -/
theorem reindexRingEquiv_trans [Semiring R] (e : n ≃ n') (f : n' ≃ n'') :
    reindexRingEquiv (R := R) (e.trans f) = (reindexRingEquiv e).trans (reindexRingEquiv f) := by
  ext A i j
  rfl

/-- Reindexing is natural for the original entrywise coefficient homomorphism. -/
theorem reindexRingEquiv_map [Semiring R] [Semiring S] (e : n ≃ n')
    (f : R →+* S) (A : Matrix.LocallyFinite n n R) :
    reindexRingEquiv e (mapRingHom f A) = mapRingHom f (reindexRingEquiv e A) := by
  ext i j
  rfl

/-- Restrict original rows and columns along actual injections. -/
def submatrix [Zero R] (e : m' ↪ m) (f : n' ↪ n) (A : Matrix.LocallyFinite m n R) :
    Matrix.LocallyFinite m' n' R where
  toMatrix := A.toMatrix.submatrix e f
  row_finite i := (A.row_finite (e i)).preimage f.injective.injOn
  column_finite j := (A.column_finite (f j)).preimage e.injective.injOn

/-- Restriction reads exactly the original entry at the supplied image indices. -/
@[simp]
theorem submatrix_apply [Zero R] (e : m' ↪ m) (f : n' ↪ n)
    (A : Matrix.LocallyFinite m n R) (i : m') (j : n') :
    submatrix e f A i j = A (e i) (f j) := rfl

/-- The zero extension of exact finite rows has earned finite original columns. -/
theorem extendedRows_column_finite [Zero R] (e : m ↪ m') (f : n ↪ n')
    (A : Matrix.LocallyFinite m n R) (j' : n') :
    (Function.support (fun i' =>
      Function.extend e (fun i => Finsupp.embDomain f (A.row i)) 0 i' j')).Finite := by
  classical
  by_cases hj : j' ∈ Set.range f
  · obtain ⟨j, rfl⟩ := hj
    refine ((A.column_finite j).image e).subset ?_
    intro i' hi'
    change Function.extend e (fun i => Finsupp.embDomain f (A.row i)) 0 i' (f j) ≠ 0 at hi'
    have he : i' ∈ Set.range e := by
      by_contra he
      rw [Function.extend_apply' _ _ _ he] at hi'
      exact hi' rfl
    obtain ⟨i, rfl⟩ := he
    refine ⟨i, ?_, rfl⟩
    simpa only [Function.mem_support, e.injective.extend_apply,
      Finsupp.embDomain_apply_self, row_apply] using hi'
  · have hzero : ∀ i',
        Function.extend e (fun i => Finsupp.embDomain f (A.row i)) 0 i' j' = 0 := by
      intro i'
      by_cases hi : i' ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hi
        rw [e.injective.extend_apply]
        exact Finsupp.embDomain_of_notMem_range f (A.row i) j' hj
      · rw [Function.extend_apply' _ _ _ hi]
        rfl
    rw [funext hzero]
    simp [Function.support]

/-- Extend the original matrix by zero outside the supplied row and column images. -/
def extend [Zero R] (e : m ↪ m') (f : n ↪ n') (A : Matrix.LocallyFinite m n R) :
    Matrix.LocallyFinite m' n' R :=
  ofRows (Function.extend e (fun i => Finsupp.embDomain f (A.row i)) 0)
    (extendedRows_column_finite e f A)

/-- The actual row at an image index is the original finitely supported column extension. -/
@[simp]
theorem row_extend_image [Zero R] (e : m ↪ m') (f : n ↪ n')
    (A : Matrix.LocallyFinite m n R) (i : m) :
    (extend e f A).row (e i) = Finsupp.embDomain f (A.row i) := by
  rw [extend, row_ofRows, e.injective.extend_apply]

/-- Every original image pair retains its actual coefficient under zero extension. -/
@[simp]
theorem extend_apply_image [Zero R] (e : m ↪ m') (f : n ↪ n')
    (A : Matrix.LocallyFinite m n R) (i : m) (j : n) :
    extend e f A (e i) (f j) = A i j := by
  rw [← row_apply, row_extend_image, Finsupp.embDomain_apply_self, row_apply]

/-- A row outside the original row image is the actual zero vector. -/
theorem row_extend_of_notMem_range [Zero R] (e : m ↪ m') (f : n ↪ n')
    (A : Matrix.LocallyFinite m n R) (i' : m') (hi : i' ∉ Set.range e) :
    (extend e f A).row i' = 0 := by
  rw [extend, row_ofRows, Function.extend_apply' _ _ _ hi]
  rfl

/-- An entry outside the original row image is zero. -/
theorem extend_apply_of_notMem_row_range [Zero R] (e : m ↪ m') (f : n ↪ n')
    (A : Matrix.LocallyFinite m n R) (i' : m') (j' : n') (hi : i' ∉ Set.range e) :
    extend e f A i' j' = 0 := by
  rw [← row_apply, row_extend_of_notMem_range e f A i' hi]
  rfl

/-- An entry outside the original column image is zero. -/
theorem extend_apply_of_notMem_column_range [Zero R] (e : m ↪ m') (f : n ↪ n')
    (A : Matrix.LocallyFinite m n R) (i' : m') (j' : n') (hj : j' ∉ Set.range f) :
    extend e f A i' j' = 0 := by
  classical
  by_cases hi : i' ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hi
    rw [← row_apply, row_extend_image]
    exact Finsupp.embDomain_of_notMem_range f (A.row i) j' hj
  · exact extend_apply_of_notMem_row_range e f A i' j' hi

/-- Zero extension is faithful on the original matrix coefficients. -/
theorem extend_injective [Zero R] (e : m ↪ m') (f : n ↪ n') :
    Function.Injective
      (extend e f : Matrix.LocallyFinite m n R → Matrix.LocallyFinite m' n' R) := by
  intro A B h
  ext i j
  simpa using congrArg (fun C : Matrix.LocallyFinite m' n' R => C (e i) (f j)) h

/-- Restriction back to the original images returns the exact original matrix. -/
@[simp]
theorem submatrix_extend [Zero R] (e : m ↪ m') (f : n ↪ n')
    (A : Matrix.LocallyFinite m n R) : submatrix e f (extend e f A) = A := by
  ext i j
  exact extend_apply_image e f A i j

/-- Zero extension along identity injections is the original matrix. -/
@[simp]
theorem extend_refl [Zero R] (A : Matrix.LocallyFinite m n R) :
    extend (Function.Embedding.refl m) (Function.Embedding.refl n) A = A := by
  ext i j
  exact extend_apply_image _ _ A i j

/-- Original zero extension takes zero to zero. -/
@[simp]
theorem extend_zero [Zero R] (e : m ↪ m') (f : n ↪ n') :
    extend e f (0 : Matrix.LocallyFinite m n R) = 0 := by
  classical
  ext i' j'
  by_cases hi : i' ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hi
    by_cases hj : j' ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hj
      exact extend_apply_image e f 0 i j
    · exact extend_apply_of_notMem_column_range e f 0 (e i) j' hj
  · exact extend_apply_of_notMem_row_range e f 0 i' j' hi

/-- Original zero extension preserves actual pointwise addition. -/
theorem extend_add [AddZeroClass R] (e : m ↪ m') (f : n ↪ n')
    (A B : Matrix.LocallyFinite m n R) : extend e f (A + B) = extend e f A + extend e f B := by
  classical
  ext i' j'
  by_cases hi : i' ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hi
    by_cases hj : j' ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hj
      simp only [extend_apply_image, add_apply]
    · simp only [extend_apply_of_notMem_column_range e f _ _ j' hj, add_apply, add_zero]
  · simp only [extend_apply_of_notMem_row_range e f _ i' _ hi, add_apply, add_zero]

/-- Zero extension preserves the original product with the same intermediate injection. -/
theorem extend_comp_product [Semiring R] (e : m ↪ m') (f : n ↪ n') (g : p ↪ p')
    (A : Matrix.LocallyFinite m n R) (B : Matrix.LocallyFinite n p R) :
    (extend e f A).comp (extend f g B) = extend e g (A.comp B) := by
  classical
  ext i' j'
  by_cases hi : i' ∈ Set.range e
  · obtain ⟨i, rfl⟩ := hi
    rw [comp_apply_sum, row_extend_image, Finsupp.sum_embDomain]
    by_cases hj : j' ∈ Set.range g
    · obtain ⟨j, rfl⟩ := hj
      simp only [extend_apply_image, comp_apply_sum]
    · rw [extend_apply_of_notMem_column_range e g _ _ j' hj]
      simp only [extend_apply_of_notMem_column_range f g _ _ j' hj, mul_zero,
        Finsupp.sum_fun_zero]
  · rw [comp_apply_sum, row_extend_of_notMem_range e f A i' hi,
      extend_apply_of_notMem_row_range e g _ i' j' hi]
    exact Finsupp.sum_zero_index

/-- Original corner extension is an injective homomorphism of nonunital matrix rings. -/
def extendRingHom [Semiring R] (e : n ↪ n') :
    NonUnitalRingHom (Matrix.LocallyFinite n n R) (Matrix.LocallyFinite n' n' R) where
  toFun := extend e e
  map_zero' := extend_zero e e
  map_add' := extend_add e e
  map_mul' A B := (extend_comp_product e e e A B).symm

/-- The actual corner homomorphism remains injective for arbitrary original indices. -/
theorem extendRingHom_injective [Semiring R] (e : n ↪ n') :
    Function.Injective (extendRingHom (R := R) e) := extend_injective e e

end Matrix.LocallyFinite

end
