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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.IsolatedCoordinate
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial
public import MathlibExt.GroupTheory.PermutationBilinearMonomialExtension
public import Mathlib.Logic.Equiv.Basic

/-!
# Inserting monomial coordinates

Extends permutations on a deleted index set by fixing the missing coordinate
and inserts a selected value into coefficient tuples and monomial data. Proves
the homomorphism and naturality laws and computes the isolated row, column,
and remaining matrix block.
-/

@[expose] public section

open PermutationBilinearCocycle
open Matrix

namespace Matrix.GeneralLinearGroup

universe uι uA uB uR vR

section PermutationLayer

variable {ι : Type uι} [DecidableEq ι] (c : ι)

/-- Extend a permutation of `DeletedIndex ι c` to a permutation of `ι` fixing `c`. -/
def extendPerm (σ : Equiv.Perm (DeletedIndex ι c)) : Equiv.Perm ι where
  toFun i := if h : i = c then c else (σ ⟨i, h⟩).val
  invFun i := if h : i = c then c else (σ⁻¹ ⟨i, h⟩).val
  left_inv := by
    intro i
    by_cases hc : i = c
    · subst hc
      simp
    · have hi : i ≠ c := hc
      have h_toFun : (if h : i = c then c else (σ ⟨i, h⟩).val) = (σ ⟨i, hi⟩).val := by
        simp [dite_eq_right hc]
      have hk_ne : (σ ⟨i, hi⟩).val ≠ c := (σ ⟨i, hi⟩).property
      have h_eq : (⟨(σ ⟨i, hi⟩).val, hk_ne⟩ : DeletedIndex ι c) = σ ⟨i, hi⟩ := by
        apply Subtype.ext; rfl
      calc (if h : (if h : i = c then c else (σ ⟨i, h⟩).val) = c then c else
            (σ⁻¹ ⟨(if h : i = c then c else (σ ⟨i, h⟩).val), h⟩).val)
          = (if h : (σ ⟨i, hi⟩).val = c then c else (σ⁻¹ ⟨(σ ⟨i, hi⟩).val, h⟩).val) := by
            rw [h_toFun]
        _ = (σ⁻¹ ⟨(σ ⟨i, hi⟩).val, hk_ne⟩).val := by rw [dite_eq_right hk_ne]
        _ = (σ⁻¹ (σ ⟨i, hi⟩)).val := by rw [h_eq]
        _ = i := by simp
  right_inv := by
    intro i
    by_cases hc : i = c
    · subst hc
      simp
    · have hi : i ≠ c := hc
      have h_toInv : (if h : i = c then c else (σ⁻¹ ⟨i, h⟩).val) = (σ⁻¹ ⟨i, hi⟩).val := by
        simp [dite_eq_right hc]
      have hk_ne : (σ⁻¹ ⟨i, hi⟩).val ≠ c := (σ⁻¹ ⟨i, hi⟩).property
      have h_eq : (⟨(σ⁻¹ ⟨i, hi⟩).val, hk_ne⟩ : DeletedIndex ι c) = σ⁻¹ ⟨i, hi⟩ := by
        apply Subtype.ext; rfl
      calc (if h : (if h : i = c then c else (σ⁻¹ ⟨i, h⟩).val) = c then c else
            (σ ⟨(if h : i = c then c else (σ⁻¹ ⟨i, h⟩).val), h⟩).val)
          = (if h : (σ⁻¹ ⟨i, hi⟩).val = c then c else
            (σ ⟨(σ⁻¹ ⟨i, hi⟩).val, h⟩).val) := by rw [h_toInv]
        _ = (σ ⟨(σ⁻¹ ⟨i, hi⟩).val, hk_ne⟩).val := by rw [dite_eq_right hk_ne]
        _ = (σ (σ⁻¹ ⟨i, hi⟩)).val := by rw [h_eq]
        _ = i := by simp

@[simp]
theorem extendPerm_apply_c (σ : Equiv.Perm (DeletedIndex ι c)) :
    extendPerm c σ c = c := by
  simp [extendPerm]

theorem extendPerm_apply_of_ne {i : ι} (hi : i ≠ c) (σ : Equiv.Perm (DeletedIndex ι c)) :
    extendPerm c σ i = (σ ⟨i, hi⟩).val := by
  simp [extendPerm, dite_eq_right hi]

theorem extendPerm_apply_eq_c_iff (σ : Equiv.Perm (DeletedIndex ι c)) (i : ι) :
    extendPerm c σ i = c ↔ i = c := by
  constructor
  · intro h
    by_contra hne
    have hi : i ≠ c := hne
    rw [extendPerm_apply_of_ne c hi σ] at h
    exact (σ ⟨i, hi⟩).property h
  · intro h
    rw [h, extendPerm_apply_c]

theorem extendPerm_apply_ne_of_ne {i : ι} (hi : i ≠ c) (σ : Equiv.Perm (DeletedIndex ι c)) :
    extendPerm c σ i ≠ c := by
  rw [Ne, extendPerm_apply_eq_c_iff]
  exact hi

@[simp]
theorem extendPerm_symm_apply_c (σ : Equiv.Perm (DeletedIndex ι c)) :
    (extendPerm c σ)⁻¹ c = c := by
  calc (extendPerm c σ)⁻¹ c = (extendPerm c σ).symm c := rfl
    _ = (extendPerm c σ).invFun c := rfl
    _ = c := by simp [extendPerm]

theorem extendPerm_symm_apply_of_ne {i : ι} (hi : i ≠ c) (σ : Equiv.Perm (DeletedIndex ι c)) :
    (extendPerm c σ)⁻¹ i = (σ⁻¹ ⟨i, hi⟩).val := by
  calc (extendPerm c σ)⁻¹ i = (extendPerm c σ).symm i := rfl
    _ = (extendPerm c σ).invFun i := rfl
    _ = (σ⁻¹ ⟨i, hi⟩).val := by simp [extendPerm, dite_eq_right hi]

@[simp]
theorem extendPerm_one : extendPerm c (1 : Equiv.Perm (DeletedIndex ι c)) = 1 := by
  ext i
  by_cases hc : i = c
  · simp [hc]
  · simp [extendPerm_apply_of_ne c hc]

theorem extendPerm_mul (σ τ : Equiv.Perm (DeletedIndex ι c)) :
    extendPerm c (σ * τ) = extendPerm c σ * extendPerm c τ := by
  ext i
  by_cases hc : i = c
  · simp [hc, Equiv.Perm.mul_apply, extendPerm_apply_c]
  · have hi : i ≠ c := hc
    have h_tau : extendPerm c τ i = (τ ⟨i, hi⟩).val := extendPerm_apply_of_ne c hi τ
    have h_tau_ne : (τ ⟨i, hi⟩).val ≠ c := (τ ⟨i, hi⟩).property
    calc extendPerm c (σ * τ) i
        = ((σ * τ) ⟨i, hi⟩).val := extendPerm_apply_of_ne c hi _
      _ = (σ (τ ⟨i, hi⟩)).val := by simp [Equiv.Perm.mul_apply]
      _ = extendPerm c σ ((τ ⟨i, hi⟩).val) := by
          have : extendPerm c σ ((τ ⟨i, hi⟩).val) = (σ ⟨(τ ⟨i, hi⟩).val, h_tau_ne⟩).val :=
            extendPerm_apply_of_ne c h_tau_ne σ
          have h_eq : (⟨(τ ⟨i, hi⟩).val, h_tau_ne⟩ : DeletedIndex ι c) = τ ⟨i, hi⟩ := by
            apply Subtype.ext; rfl
          rw [this, h_eq]
      _ = extendPerm c σ (extendPerm c τ i) := by rw [h_tau]
      _ = (extendPerm c σ * extendPerm c τ) i := by simp [Equiv.Perm.mul_apply]

/-- Bundled group hom for permutation extension. -/
def extendPermHom : Equiv.Perm (DeletedIndex ι c) →* Equiv.Perm ι where
  toFun := extendPerm c
  map_one' := extendPerm_one c
  map_mul' := extendPerm_mul c

@[simp]
theorem extendPermHom_apply (σ : Equiv.Perm (DeletedIndex ι c)) :
    extendPermHom c σ = extendPerm c σ := rfl

theorem extendPerm_inv (σ : Equiv.Perm (DeletedIndex ι c)) :
    (extendPerm c σ)⁻¹ = extendPerm c σ⁻¹ := by
  calc (extendPerm c σ)⁻¹ = (extendPermHom c σ)⁻¹ := rfl
    _ = extendPermHom c σ⁻¹ := by rw [map_inv]
    _ = extendPerm c σ⁻¹ := rfl

end PermutationLayer

section TupleLayer

variable {ι : Type uι} [DecidableEq ι] {A : Type uA} [Group A] {c : ι}

/-- Insert a distinguished coefficient `a` into a tuple `u` indexed by `DeletedIndex ι c`. -/
def insertTuple (c : ι) (a : A) (u : DeletedIndex ι c → A) : ι → A :=
  fun i => if h : i = c then a else u ⟨i, h⟩

omit [Group A] in
@[simp]
theorem insertTuple_apply_c (a : A) (u : DeletedIndex ι c → A) :
    insertTuple c a u c = a := by
  simp [insertTuple]

omit [Group A] in
theorem insertTuple_apply_of_ne {i : ι} (hi : i ≠ c) (a : A) (u : DeletedIndex ι c → A) :
    insertTuple c a u i = u ⟨i, hi⟩ := by
  simp [insertTuple, dite_eq_right hi]

omit [Group A] in
theorem insertTuple_comp_val (a : A) (u : DeletedIndex ι c → A) (d : DeletedIndex ι c) :
    insertTuple c a u d.val = u d :=
  insertTuple_apply_of_ne d.property a u

theorem insertTuple_one : insertTuple (c := c) (1 : A) (1 : DeletedIndex ι c → A) = 1 := by
  funext i
  by_cases hc : i = c
  · simp [hc]
  · simp [insertTuple_apply_of_ne hc]

theorem insertTuple_mul (a₁ a₂ : A) (u₁ u₂ : DeletedIndex ι c → A) :
    insertTuple c (a₁ * a₂) (u₁ * u₂) = insertTuple c a₁ u₁ * insertTuple c a₂ u₂ := by
  funext i
  by_cases hc : i = c
  · simp [hc]
  · simp [insertTuple_apply_of_ne hc]

/-- Tuple insertion with fixed `1` at `c` as a group hom. -/
def insertTupleHomOne (c : ι) : (DeletedIndex ι c → A) →* (ι → A) where
  toFun u := insertTuple c (1 : A) u
  map_one' := insertTuple_one (c := c) (A := A)
  map_mul' := by
    intro u v
    have h := insertTuple_mul (c := c) (1 : A) (1 : A) u v
    simp only [mul_one] at h
    exact h

/-- Insertion from `A × (DeletedIndex → A)` to `ι → A`. -/
def insertTupleProdHom (c : ι) : A × (DeletedIndex ι c → A) →* (ι → A) where
  toFun p := insertTuple c p.1 p.2
  map_one' := by
    ext i
    by_cases hc : i = c
    · simp [hc]
    · simp [insertTuple_apply_of_ne hc]
  map_mul' := by
    intro p q
    simp only [Prod.mul_def]
    exact insertTuple_mul p.1 q.1 p.2 q.2

@[simp]
theorem insertTupleProdHom_apply (a : A) (u : DeletedIndex ι c → A) :
    insertTupleProdHom (A := A) c (a, u) = insertTuple c a u := rfl

theorem insertTuple_naturality {B : Type uB} [Group B] (f : A →* B)
    (a : A) (u : DeletedIndex ι c → A) (i : ι) :
    f (insertTuple c a u i) = insertTuple c (f a) (fun d => f (u d)) i := by
  by_cases hc : i = c
  · simp [hc]
  · simp [insertTuple_apply_of_ne hc]

theorem mapTuple_insertTuple {B : Type uB} [Group B] (f : A →* B)
    (a : A) (u : DeletedIndex ι c → A) :
    mapTupleHom (ι := ι) f (insertTuple c a u) =
      insertTuple c (f a) (fun d => f (u d)) := by
  funext i
  exact insertTuple_naturality f a u i

omit [Group A] in
theorem permute_insertTuple (σ : Equiv.Perm (DeletedIndex ι c))
    (a : A) (u : DeletedIndex ι c → A) :
    permute (extendPerm c σ) (insertTuple c a u) =
      insertTuple c a (permute σ u) := by
  funext i
  by_cases hc : i = c
  · have h_inv_c : (extendPerm c σ)⁻¹ i = c := by
      rw [hc, extendPerm_symm_apply_c]
    calc permute (extendPerm c σ) (insertTuple c a u) i
        = insertTuple c a u ((extendPerm c σ)⁻¹ i) := rfl
      _ = insertTuple c a u c := by rw [h_inv_c]
      _ = a := by simp
      _ = insertTuple c a (permute σ u) i := by simp [hc]
  · have hi : i ≠ c := hc
    have h_eq_inv : (extendPerm c σ)⁻¹ i = c ↔ i = c := by
      rw [extendPerm_inv]
      exact extendPerm_apply_eq_c_iff c σ⁻¹ i
    have h_perm_ne : (extendPerm c σ)⁻¹ i ≠ c := by
      intro heq
      have : i = c := h_eq_inv.mp heq
      exact hi this
    have h_symm : (extendPerm c σ)⁻¹ i = (σ⁻¹ ⟨i, hi⟩).val :=
      extendPerm_symm_apply_of_ne c hi σ
    calc permute (extendPerm c σ) (insertTuple c a u) i
        = insertTuple c a u ((extendPerm c σ)⁻¹ i) := rfl
      _ = u ⟨(extendPerm c σ)⁻¹ i, h_perm_ne⟩ := by
          rw [insertTuple_apply_of_ne h_perm_ne]
      _ = u (σ⁻¹ ⟨i, hi⟩) := by
          have h_eq : (⟨(extendPerm c σ)⁻¹ i, h_perm_ne⟩ : DeletedIndex ι c) =
              σ⁻¹ ⟨i, hi⟩ := by
            apply Subtype.ext
            exact h_symm
          rw [h_eq]
      _ = permute σ u ⟨i, hi⟩ := rfl
      _ = insertTuple c a (permute σ u) i := by
          rw [insertTuple_apply_of_ne hi]

end TupleLayer

section MonomialLayer

variable {ι : Type uι} [DecidableEq ι] {A : Type uA} [Group A] (c : ι)

/-- Insert a monomial over `DeletedIndex ι c` together with a pivot unit `a` into
`MonomialBase A ι`. -/
def monomialInsert (a : A) (x : MonomialBase A (DeletedIndex ι c)) : MonomialBase A ι :=
  ⟨insertTuple c a x.left, extendPerm c x.right⟩

@[simp]
theorem monomialInsert_left (a : A) (x : MonomialBase A (DeletedIndex ι c)) :
    (monomialInsert c a x).left = insertTuple c a x.left := rfl

@[simp]
theorem monomialInsert_right (a : A) (x : MonomialBase A (DeletedIndex ι c)) :
    (monomialInsert c a x).right = extendPerm c x.right := rfl

theorem monomialInsert_one :
    monomialInsert c (1 : A) (1 : MonomialBase A (DeletedIndex ι c)) = 1 := by
  apply SemidirectProduct.ext
  · simp [monomialInsert, insertTuple_one]
  · simp [monomialInsert, extendPerm_one]

/-- Bundled monoid hom `A × MonomialBase A (DeletedIndex ι c) →* MonomialBase A ι`. -/
def monomialInsertProdHom : A × MonomialBase A (DeletedIndex ι c) →* MonomialBase A ι where
  toFun p := monomialInsert c p.1 p.2
  map_one' := by
    simp [monomialInsert_one]
  map_mul' := by
    intro p q
    apply SemidirectProduct.ext
    · simp only [monomialInsert, SemidirectProduct.mul_left, tupleActionHom_apply]
      have h_perm : permute (extendPerm c p.2.right) (insertTuple c q.1 q.2.left) =
          insertTuple c q.1 (permute p.2.right q.2.left) :=
        permute_insertTuple p.2.right q.1 q.2.left
      calc insertTuple c (p.1 * q.1) ((p.2 * q.2).left)
          = insertTuple c (p.1 * q.1) (p.2.left * permute p.2.right q.2.left) := by
            simp [SemidirectProduct.mul_left, tupleActionHom_apply]
        _ = insertTuple c p.1 p.2.left * insertTuple c q.1 (permute p.2.right q.2.left) := by
            rw [insertTuple_mul]
        _ = insertTuple c p.1 p.2.left *
            permute (extendPerm c p.2.right) (insertTuple c q.1 q.2.left) := by
            rw [h_perm]
    · have h_right : (p * q).2.right = p.2.right * q.2.right := rfl
      calc extendPerm c (p * q).2.right
          = extendPerm c (p.2.right * q.2.right) := by rw [h_right]
        _ = extendPerm c p.2.right * extendPerm c q.2.right := extendPerm_mul c _ _

@[simp]
theorem monomialInsertProdHom_apply (a : A) (x : MonomialBase A (DeletedIndex ι c)) :
    monomialInsertProdHom c (a, x) = monomialInsert c a x := rfl

theorem monomialInsert_mul (a₁ a₂ : A)
    (x₁ x₂ : MonomialBase A (DeletedIndex ι c)) :
    monomialInsert c (a₁ * a₂) (x₁ * x₂) =
      monomialInsert c a₁ x₁ * monomialInsert c a₂ x₂ := by
  have h := (monomialInsertProdHom c).map_mul (a₁, x₁) (a₂, x₂)
  simpa [Prod.mul_def] using h

theorem monomialInsert_naturality {B : Type uB} [Group B] (f : A →* B)
    (a : A) (x : MonomialBase A (DeletedIndex ι c)) :
    monomialBaseHom f (monomialInsert c a x) =
      monomialInsert c (f a) (monomialBaseHom f x) := by
  apply SemidirectProduct.ext
  · funext i
    by_cases hc : i = c
    · simp [hc]
    · simp [insertTuple_apply_of_ne hc, mapTuple_apply]
  · rfl

end MonomialLayer

section MatrixRealization

variable {ι : Type uι} [DecidableEq ι] [Fintype ι] (c : ι)
variable {R : Type uR} [Semiring R]

private theorem monomial_entry (t : ι → Rˣ) (p : Equiv.Perm ι) (i j : ι) :
    (↑(monomialMatrixHom R ι ⟨t, p⟩) : Matrix ι ι R) i j =
      if (p⁻¹ i) = j then (t i : R) else 0 := by
  have h : (↑(monomialMatrixHom R ι ⟨t, p⟩) : Matrix ι ι R) =
      Matrix.diagonal (fun k => (t k : R)) * (p⁻¹).permMatrix R := by
    simp only [coe_monomialMatrixHom_mk]
  rw [h, diag_mul_perm_eq]

theorem monomialInsert_matrix_c_c (a : Rˣ)
    (x : MonomialBase Rˣ (DeletedIndex ι c)) :
    (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) c c = (a : R) := by
  have h_entry := monomial_entry (R := R) (fun i => insertTuple c a x.left i)
    (extendPerm c x.right) c c
  have h_perm : (extendPerm c x.right)⁻¹ c = c := extendPerm_symm_apply_c c x.right
  have h_t : insertTuple c a x.left c = a := insertTuple_apply_c a x.left
  calc (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) c c
      = (↑(monomialMatrixHom R ι ⟨fun i => insertTuple c a x.left i,
          extendPerm c x.right⟩) : Matrix ι ι R) c c := rfl
    _ = if (extendPerm c x.right)⁻¹ c = c then ((insertTuple c a x.left c : Rˣ) : R) else 0 := by
        rw [monomial_entry]
    _ = (a : R) := by
        have : ((insertTuple c a x.left c : Rˣ) : R) = (a : R) := by rw [h_t]
        rw [h_perm, ite_eq_left rfl, this]

theorem monomialInsert_matrix_row_c (a : Rˣ)
    (x : MonomialBase Rˣ (DeletedIndex ι c)) {j : ι} (hj : j ≠ c) :
    (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) c j = 0 := by
  have h_entry := monomial_entry (R := R) (fun i => insertTuple c a x.left i)
    (extendPerm c x.right) c j
  have h_perm : (extendPerm c x.right)⁻¹ c = c := extendPerm_symm_apply_c c x.right
  have h_ne : ¬ (c = j) := Ne.symm hj
  calc (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) c j
      = (↑(monomialMatrixHom R ι ⟨fun i => insertTuple c a x.left i,
          extendPerm c x.right⟩) : Matrix ι ι R) c j := rfl
    _ = if (extendPerm c x.right)⁻¹ c = j then ((insertTuple c a x.left c : Rˣ) : R) else 0 := by
        rw [monomial_entry]
    _ = if c = j then (a : R) else 0 := by
        have : ((insertTuple c a x.left c : Rˣ) : R) = (a : R) := by
          rw [insertTuple_apply_c]
        rw [h_perm, this]
    _ = 0 := by rw [ite_eq_right h_ne]

theorem monomialInsert_matrix_col_c (a : Rˣ)
    (x : MonomialBase Rˣ (DeletedIndex ι c)) {i : ι} (hi : i ≠ c) :
    (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) i c = 0 := by
  calc (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) i c
      = (↑(monomialMatrixHom R ι ⟨fun k => insertTuple c a x.left k,
          extendPerm c x.right⟩) : Matrix ι ι R) i c := rfl
    _ = if (extendPerm c x.right)⁻¹ i = c then ((insertTuple c a x.left i : Rˣ) : R) else 0 := by
        rw [monomial_entry]
    _ = 0 := by
        have h_eq : (extendPerm c x.right)⁻¹ i = c ↔ i = c := by
          rw [extendPerm_inv]
          exact extendPerm_apply_eq_c_iff c x.right⁻¹ i
        have h_ne : (extendPerm c x.right)⁻¹ i ≠ c := by
          intro heq
          exact hi (h_eq.mp heq)
        rw [ite_eq_right h_ne]

theorem monomialInsert_matrix_block (a : Rˣ)
    (x : MonomialBase Rˣ (DeletedIndex ι c)) {i j : ι} (hi : i ≠ c) (hj : j ≠ c) :
    (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) i j =
      (↑(monomialMatrixHom R (DeletedIndex ι c) x) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R)
        ⟨i, hi⟩ ⟨j, hj⟩ := by
  have h_entry_small : (↑(monomialMatrixHom R (DeletedIndex ι c) x) :
        Matrix (DeletedIndex ι c) (DeletedIndex ι c) R) ⟨i, hi⟩ ⟨j, hj⟩ =
      if (x.right⁻¹ ⟨i, hi⟩ = ⟨j, hj⟩) then (x.left ⟨i, hi⟩ : R) else 0 := by
    have h := monomial_entry (R := R) (ι := DeletedIndex ι c) (fun d => x.left d) x.right
      ⟨i, hi⟩ ⟨j, hj⟩
    exact h
  calc (↑(monomialMatrixHom R ι (monomialInsert c a x)) : Matrix ι ι R) i j
      = (↑(monomialMatrixHom R ι ⟨fun k => insertTuple c a x.left k,
          extendPerm c x.right⟩) : Matrix ι ι R) i j := rfl
    _ = if (extendPerm c x.right)⁻¹ i = j then ((insertTuple c a x.left i : Rˣ) : R) else 0 := by
        rw [monomial_entry]
    _ = if (extendPerm c x.right)⁻¹ i = j then (x.left ⟨i, hi⟩ : R) else 0 := by
        have h_t : insertTuple c a x.left i = x.left ⟨i, hi⟩ :=
          insertTuple_apply_of_ne hi _ _
        have h_tR : ((insertTuple c a x.left i : Rˣ) : R) = (x.left ⟨i, hi⟩ : R) := by
          rw [h_t]
        rw [h_tR]
    _ = if (x.right⁻¹ ⟨i, hi⟩ = ⟨j, hj⟩) then (x.left ⟨i, hi⟩ : R) else 0 := by
        have h_perm_eq : ((extendPerm c x.right)⁻¹ i = j) ↔
            (x.right⁻¹ ⟨i, hi⟩ = ⟨j, hj⟩) := by
          constructor
          · intro heq
            have h_symm : (extendPerm c x.right)⁻¹ i = (x.right⁻¹ ⟨i, hi⟩).val :=
              extendPerm_symm_apply_of_ne c hi x.right
            rw [h_symm] at heq
            apply Subtype.ext
            exact heq
          · intro heq
            have h_symm : (extendPerm c x.right)⁻¹ i = (x.right⁻¹ ⟨i, hi⟩).val :=
              extendPerm_symm_apply_of_ne c hi x.right
            have : (x.right⁻¹ ⟨i, hi⟩).val = j := congrArg Subtype.val heq
            rw [h_symm, this]
        by_cases hcond : (x.right⁻¹ ⟨i, hi⟩ = ⟨j, hj⟩)
        · have h_big : (extendPerm c x.right)⁻¹ i = j := h_perm_eq.mpr hcond
          rw [ite_eq_left h_big, ite_eq_left hcond]
        · have h_big : ¬ ((extendPerm c x.right)⁻¹ i = j) := by
            intro heq
            exact hcond (h_perm_eq.mp heq)
          rw [ite_eq_right h_big, ite_eq_right hcond]
    _ = (↑(monomialMatrixHom R (DeletedIndex ι c) x) :
        Matrix (DeletedIndex ι c) (DeletedIndex ι c) R) ⟨i, hi⟩ ⟨j, hj⟩ := by
        rw [h_entry_small]

theorem monomialInsert_isIsolated {R' : Type uR} [Ring R'] (a : R'ˣ)
    (x : MonomialBase R'ˣ (DeletedIndex ι c)) :
    IsolatedCoordinate (monomialMatrixHom R' ι (monomialInsert c a x)) c where
  col_zero _ hi := monomialInsert_matrix_col_c c a x hi
  row_zero _ hj := monomialInsert_matrix_row_c c a x hj

theorem monomialInsert_mapRingHom {S : Type vR} [Semiring S] (f : R →+* S)
    (a : Rˣ) (x : MonomialBase Rˣ (DeletedIndex ι c)) :
    mapRingHom (n := ι) f (monomialMatrixHom R ι (monomialInsert c a x)) =
      monomialMatrixHom S ι
        (monomialInsert c (Units.map f a) (monomialBaseHom (Units.map f) x)) := by
  let f' : Rˣ →* Sˣ := Units.map f
  have h1 : mapRingHom (n := ι) f (monomialMatrixHom R ι (monomialInsert c a x)) =
      monomialMatrixHom S ι (monomialBaseHom f' (monomialInsert c a x)) :=
    monomialMatrixHom_mapRingHom_apply f _
  have h2 : monomialBaseHom f' (monomialInsert c a x) =
      monomialInsert c (f' a) (monomialBaseHom f' x) :=
    monomialInsert_naturality c f' a x
  rw [h1, h2]

end MatrixRealization

section DivisionSpecialization

variable {ι : Type uι} [DecidableEq ι] (c : ι)
variable {K : Type uR} [DivisionRing K]

/-- Division helper inserting `Units.mk0 p hp`. This is the only division-specific portion. -/
def monomialInsertMk0 (p : K) (hp : p ≠ 0)
    (x : MonomialBase Kˣ (DeletedIndex ι c)) : MonomialBase Kˣ ι :=
  monomialInsert c (Units.mk0 p hp) x

@[simp]
theorem monomialInsertMk0_left (p : K) (hp : p ≠ 0)
    (x : MonomialBase Kˣ (DeletedIndex ι c)) :
    (monomialInsertMk0 c p hp x).left = insertTuple c (Units.mk0 p hp) x.left := rfl

@[simp]
theorem monomialInsertMk0_right (p : K) (hp : p ≠ 0)
    (x : MonomialBase Kˣ (DeletedIndex ι c)) :
    (monomialInsertMk0 c p hp x).right = extendPerm c x.right := rfl

theorem monomialInsertMk0_matrix_c_c [Fintype ι] (p : K) (hp : p ≠ 0)
    (x : MonomialBase Kˣ (DeletedIndex ι c)) :
    (↑(monomialMatrixHom K ι (monomialInsertMk0 c p hp x)) : Matrix ι ι K) c c = p :=
  monomialInsert_matrix_c_c (R := K) c (Units.mk0 p hp) x

end DivisionSpecialization

end Matrix.GeneralLinearGroup
