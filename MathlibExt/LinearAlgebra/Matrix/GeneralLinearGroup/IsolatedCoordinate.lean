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

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Map
public import Mathlib.Data.Fintype.BigOperators

/-!
# Isolated coordinate deletion for `GL`

For an invertible matrix with a row and column isolated at `c`
(zero off the pivot), delete the coordinate `c` to obtain an invertible
principal submatrix on the complementary indices.

This is the ring-generic recursive primitive for Bruhat-style extractions.
No order, division, `Fin`, field, or commutativity assumptions are used.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

universe uι uR vR wR

variable {ι : Type uι} [DecidableEq ι] [Fintype ι]
variable {R : Type uR} [Ring R]

/-- Indices distinct from `c`. -/
abbrev DeletedIndex (ι : Type uι) (c : ι) := { i : ι // i ≠ c }

/-- Row and column `c` are zero off the diagonal for `g`. -/
structure IsolatedCoordinate (g : GL ι R) (c : ι) : Prop where
  col_zero : ∀ i : ι, i ≠ c → (↑g : Matrix ι ι R) i c = 0
  row_zero : ∀ j : ι, j ≠ c → (↑g : Matrix ι ι R) c j = 0

namespace IsolatedCoordinate

variable {g : GL ι R} {c : ι}

theorem col_zero_of_ne (h : IsolatedCoordinate g c) {i : ι} (hi : i ≠ c) :
    (↑g : Matrix ι ι R) i c = 0 :=
  h.col_zero i hi

theorem row_zero_of_ne (h : IsolatedCoordinate g c) {j : ι} (hj : j ≠ c) :
    (↑g : Matrix ι ι R) c j = 0 :=
  h.row_zero j hj

/-- Constructor from exact `if` formulas for the isolated row and column. -/
theorem mk_of_if
    (hcol : ∀ i : ι, (↑g : Matrix ι ι R) i c = if i = c then (↑g : Matrix ι ι R) c c else 0)
    (hrow : ∀ j : ι, (↑g : Matrix ι ι R) c j = if j = c then (↑g : Matrix ι ι R) c c else 0) :
    IsolatedCoordinate g c where
  col_zero i hi := by
    simp [hcol i, hi]
  row_zero j hj := by
    simp [hrow j, hj]

/-- Preservation under arbitrary ring homomorphism. -/
theorem map {S : Type vR} [Ring S] (f : R →+* S) (h : IsolatedCoordinate g c) :
    IsolatedCoordinate (Matrix.GeneralLinearGroup.mapRingHom f g) c where
  col_zero i hi := by
    have : (↑(Matrix.GeneralLinearGroup.mapRingHom f g) : Matrix ι ι S) i c =
        f ((↑g : Matrix ι ι R) i c) := by
      simp [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply]
    rw [this, h.col_zero i hi, f.map_zero]
  row_zero j hj := by
    have : (↑(Matrix.GeneralLinearGroup.mapRingHom f g) : Matrix ι ι S) c j =
        f ((↑g : Matrix ι ι R) c j) := by
      simp [Matrix.GeneralLinearGroup.coe_mapRingHom, Matrix.map_apply]
    rw [this, h.row_zero j hj, f.map_zero]

end IsolatedCoordinate

/-- The `≠ c` principal submatrix of `g`. -/
def delVal (g : GL ι R) (c : ι) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R :=
  (↑g : Matrix ι ι R).submatrix Subtype.val Subtype.val

/-- The `≠ c` principal submatrix of `g⁻¹`. -/
def delInvVal (g : GL ι R) (c : ι) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R :=
  (↑(g⁻¹) : Matrix ι ι R).submatrix Subtype.val Subtype.val

private lemma sum_subtype_eq_of_zero_at_c
    {ι : Type uι} [DecidableEq ι] [Fintype ι] {R : Type uR} [AddCommMonoid R]
    (f : ι → R) (c : ι) (hf : f c = 0) :
    (∑ k : DeletedIndex ι c, f k.1) = ∑ k : ι, f k := by
  have h := Fintype.sum_eq_add_sum_subtype_ne (f := f) (a := c)
  rw [hf, zero_add] at h
  exact h.symm

private lemma val_inv_aux (g : GL ι R) (c : ι) (h : IsolatedCoordinate g c)
    (i j : DeletedIndex ι c) :
    ((delVal g c * delInvVal g c) i j) = ((1 : Matrix ι ι R) i.1 j.1) := by
  dsimp [delVal, delInvVal, Matrix.mul_apply, Matrix.submatrix_apply]
  set f : ι → R := fun k => (↑g : Matrix ι ι R) i.1 k * (↑(g⁻¹) : Matrix ι ι R) k j.1
  have hf : f c = 0 := by
    dsimp [f]
    rw [h.col_zero i.1 i.2, zero_mul]
  have hsum :
      (∑ k : DeletedIndex ι c,
          (↑g : Matrix ι ι R) i.1 k.1 * (↑(g⁻¹) : Matrix ι ι R) k.1 j.1) =
        ∑ k : ι, f k :=
    sum_subtype_eq_of_zero_at_c f c hf
  calc
    (∑ k : DeletedIndex ι c,
        (↑g : Matrix ι ι R) i.1 ↑k * (↑(g⁻¹) : Matrix ι ι R) ↑k j.1) =
        ∑ k : ι, f k := hsum
    _ = ((↑g : Matrix ι ι R) * (↑(g⁻¹) : Matrix ι ι R)) i.1 j.1 := by
        simp [f, Matrix.mul_apply]
    _ = ((1 : Matrix ι ι R) i.1 j.1) := by
        have h1 : (↑g : Matrix ι ι R) * (↑(g⁻¹) : Matrix ι ι R) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [h1]

private lemma inv_val_aux (g : GL ι R) (c : ι) (h : IsolatedCoordinate g c)
    (i j : DeletedIndex ι c) :
    ((delInvVal g c * delVal g c) i j) = ((1 : Matrix ι ι R) i.1 j.1) := by
  dsimp [delVal, delInvVal, Matrix.mul_apply, Matrix.submatrix_apply]
  set f : ι → R := fun k => (↑(g⁻¹) : Matrix ι ι R) i.1 k * (↑g : Matrix ι ι R) k j.1
  have hf : f c = 0 := by
    dsimp [f]
    rw [h.row_zero j.1 j.2, mul_zero]
  have hsum :
      (∑ k : DeletedIndex ι c,
          (↑(g⁻¹) : Matrix ι ι R) i.1 ↑k * (↑g : Matrix ι ι R) ↑k j.1) =
        ∑ k : ι, f k :=
    sum_subtype_eq_of_zero_at_c f c hf
  calc
    (∑ k : DeletedIndex ι c,
        (↑(g⁻¹) : Matrix ι ι R) i.1 ↑k * (↑g : Matrix ι ι R) ↑k j.1) =
        ∑ k : ι, f k := hsum
    _ = ((↑(g⁻¹) : Matrix ι ι R) * (↑g : Matrix ι ι R)) i.1 j.1 := by
        simp [f, Matrix.mul_apply]
    _ = ((1 : Matrix ι ι R) i.1 j.1) := by
        have h1 : (↑(g⁻¹) : Matrix ι ι R) * (↑g : Matrix ι ι R) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [h1]

/-- Deleting an isolated coordinate. The value is the principal submatrix
on indices `≠ c`; the inverse is the corresponding submatrix of `g⁻¹`. -/
def deleteCoordinate (g : GL ι R) (c : ι) (h : IsolatedCoordinate g c) :
    GL (DeletedIndex ι c) R where
  val := delVal g c
  inv := delInvVal g c
  val_inv := by
    ext i j
    have h1 := val_inv_aux g c h i j
    have h2 : ((1 : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R) i j) =
        ((1 : Matrix ι ι R) i.1 j.1) := by
      simp only [Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · have hij_val : i.1 ≠ j.1 := by
          intro heq
          apply hij
          exact Subtype.ext heq
        simp [hij, hij_val]
    rw [h2]
    exact h1
  inv_val := by
    ext i j
    have h1 := inv_val_aux g c h i j
    have h2 : ((1 : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R) i j) =
        ((1 : Matrix ι ι R) i.1 j.1) := by
      simp only [Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · have hij_val : i.1 ≠ j.1 := by
          intro heq
          apply hij
          exact Subtype.ext heq
        simp [hij, hij_val]
    rw [h2]
    exact h1

@[simp]
theorem coe_deleteCoordinate (g : GL ι R) (c : ι) (h : IsolatedCoordinate g c) :
    (↑(deleteCoordinate g c h) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R) =
      (↑g : Matrix ι ι R).submatrix Subtype.val Subtype.val :=
  rfl

@[simp]
theorem coe_inv_deleteCoordinate (g : GL ι R) (c : ι) (h : IsolatedCoordinate g c) :
    (↑(deleteCoordinate g c h)⁻¹ : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R) =
      (↑(g⁻¹) : Matrix ι ι R).submatrix Subtype.val Subtype.val :=
  rfl

section Naturality

variable {S : Type vR} [Ring S]
variable {T : Type wR} [Ring T]

/-- Mapping preserves isolatedness. -/
theorem isolatedCoordinate_map (f : R →+* S) (g : GL ι R) (c : ι)
    (h : IsolatedCoordinate g c) :
    IsolatedCoordinate (Matrix.GeneralLinearGroup.mapRingHom f g) c :=
  h.map f

/-- Naturality of `deleteCoordinate` for an arbitrary ring homomorphism. -/
theorem mapRingHom_deleteCoordinate (f : R →+* S) (g : GL ι R) (c : ι)
    (h : IsolatedCoordinate g c) :
    Matrix.GeneralLinearGroup.mapRingHom f (deleteCoordinate g c h) =
      deleteCoordinate (Matrix.GeneralLinearGroup.mapRingHom f g) c (h.map f) := by
  apply Units.ext
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mapRingHom, coe_deleteCoordinate,
    Matrix.submatrix_apply, Matrix.map_apply]

/-- Identity naturality for `deleteCoordinate`. -/
theorem deleteCoordinate_mapRingHom_id (g : GL ι R) (c : ι)
    (h : IsolatedCoordinate g c) :
    deleteCoordinate (Matrix.GeneralLinearGroup.mapRingHom (RingHom.id R) g) c
        (h.map (RingHom.id R)) =
      Matrix.GeneralLinearGroup.mapRingHom (RingHom.id R) (deleteCoordinate g c h) := by
  rw [← mapRingHom_deleteCoordinate (f := RingHom.id R)]

/-- Composition naturality for `deleteCoordinate`. -/
theorem deleteCoordinate_mapRingHom_comp (f : R →+* S) (f' : S →+* T)
    (g : GL ι R) (c : ι) (h : IsolatedCoordinate g c) :
    deleteCoordinate (Matrix.GeneralLinearGroup.mapRingHom (f'.comp f) g) c
        (h.map (f'.comp f)) =
      Matrix.GeneralLinearGroup.mapRingHom f'
        (deleteCoordinate (Matrix.GeneralLinearGroup.mapRingHom f g) c (h.map f)) := by
  calc
    deleteCoordinate (Matrix.GeneralLinearGroup.mapRingHom (f'.comp f) g) c
        (h.map (f'.comp f))
        = Matrix.GeneralLinearGroup.mapRingHom (f'.comp f) (deleteCoordinate g c h) := by
          rw [← mapRingHom_deleteCoordinate]
    _ = Matrix.GeneralLinearGroup.mapRingHom f'
          (Matrix.GeneralLinearGroup.mapRingHom f (deleteCoordinate g c h)) := by
          have hcomp :
              Matrix.GeneralLinearGroup.mapRingHom (f'.comp f) (deleteCoordinate g c h) =
                Matrix.GeneralLinearGroup.mapRingHom f'
                  (Matrix.GeneralLinearGroup.mapRingHom f (deleteCoordinate g c h)) := by
            exact DFunLike.congr_fun (Matrix.GeneralLinearGroup.mapRingHom_comp f f')
              (deleteCoordinate g c h)
          exact hcomp
    _ = Matrix.GeneralLinearGroup.mapRingHom f'
          (deleteCoordinate (Matrix.GeneralLinearGroup.mapRingHom f g) c (h.map f)) := by
          rw [mapRingHom_deleteCoordinate]

end Naturality

section Reconstruction

variable (g : GL ι R) (c : ι)

/-- Entry with both indices distinct from `c` comes from the deleted block. -/
theorem coe_of_ne_ne (h : IsolatedCoordinate g c) {i j : ι} (hi : i ≠ c) (hj : j ≠ c) :
    (↑g : Matrix ι ι R) i j =
      (↑(deleteCoordinate g c h) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R)
        ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp [coe_deleteCoordinate]

/-- Column isolation. -/
theorem coe_of_ne_eq (h : IsolatedCoordinate g c) {i : ι} (hi : i ≠ c) :
    (↑g : Matrix ι ι R) i c = 0 :=
  h.col_zero i hi

/-- Row isolation. -/
theorem coe_of_eq_ne (h : IsolatedCoordinate g c) {j : ι} (hj : j ≠ c) :
    (↑g : Matrix ι ι R) c j = 0 :=
  h.row_zero j hj

/-- Reconstruction with `dite`: the matrix is determined by its deleted block and pivot. -/
theorem coe_eq_block_of_isolated (h : IsolatedCoordinate g c) (i j : ι) :
    (↑g : Matrix ι ι R) i j =
      if hi : i = c then
        if j = c then (↑g : Matrix ι ι R) c c else 0
      else
        if hj : j = c then 0
        else
          (↑(deleteCoordinate g c h) : Matrix (DeletedIndex ι c) (DeletedIndex ι c) R)
            ⟨i, hi⟩ ⟨j, hj⟩ := by
  by_cases hi : i = c
  · by_cases hj : j = c
    · simp [hi, hj]
    · simp [hi, hj, h.row_zero j hj]
  · by_cases hj : j = c
    · simp [hi, hj, h.col_zero i hi]
    · simp [hi, hj, coe_deleteCoordinate]

end Reconstruction

end Matrix.GeneralLinearGroup
