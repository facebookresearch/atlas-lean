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

public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial

@[expose] public section

namespace Matrix

/-- Heterogeneous invertible matrix: an `m × n` matrix with a two-sided inverse `n × m`.

The existence of this structure already witnesses `Fintype.card m = Fintype.card n`,
without an extra cardinal assumption. -/
structure GeneralLinearEquiv (m n : Type*) (R : Type*) [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] [Semiring R] where
  /-- The forward matrix `m × n`. -/
  val : Matrix m n R
  /-- The backward matrix `n × m`, a two-sided inverse of `val`. -/
  inv : Matrix n m R
  /-- `val * inv = 1` in `Matrix m m R`. -/
  val_inv : val * inv = 1
  /-- `inv * val = 1` in `Matrix n n R`. -/
  inv_val : inv * val = 1

namespace GeneralLinearEquiv

variable {m n p q m' n' : Type*}
variable {R S T : Type*}
variable [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype m'] [Fintype n']
variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
variable [DecidableEq m'] [DecidableEq n']
variable [Semiring R] [Semiring S] [Semiring T]

@[simp]
theorem val_mul_inv (e : GeneralLinearEquiv m n R) : e.val * e.inv = 1 :=
  e.val_inv

@[simp]
theorem inv_mul_val (e : GeneralLinearEquiv m n R) : e.inv * e.val = 1 :=
  e.inv_val

/-- Extensionality by the value matrix: the inverse is uniquely determined. -/
theorem ext {e f : GeneralLinearEquiv m n R} (h : e.val = f.val) : e = f := by
  obtain ⟨v₁, i₁, hv₁, hv₂⟩ := e
  obtain ⟨v₂, i₂, hw₁, hw₂⟩ := f
  dsimp at h
  subst h
  have hInv : i₁ = i₂ := by
    calc i₁ = i₁ * (1 : Matrix m m R) := by simp
      _ = i₁ * (v₁ * i₂) := by rw [hw₁]
      _ = (i₁ * v₁) * i₂ := by rw [Matrix.mul_assoc]
      _ = (1 : Matrix n n R) * i₂ := by rw [hv₂]
      _ = i₂ := by simp
  subst hInv
  have h₁ : hv₁ = hw₁ := Subsingleton.elim _ _
  have h₂ : hv₂ = hw₂ := Subsingleton.elim _ _
  subst h₁
  subst h₂
  rfl

theorem ext_iff {e f : GeneralLinearEquiv m n R} : e = f ↔ e.val = f.val :=
  ⟨fun h => congrArg val h, ext⟩

instance : Coe (GeneralLinearEquiv m n R) (Matrix m n R) where
  coe e := e.val

@[simp]
theorem coe_val (e : GeneralLinearEquiv m n R) : (e.val : Matrix m n R) = e.val :=
  rfl

@[simp]
theorem coe_coe (e : GeneralLinearEquiv m n R) : (e : Matrix m n R) = e.val :=
  rfl

/-- Identity heterogeneous equivalence `m = m`, the `1` matrix in both directions. -/
def refl : GeneralLinearEquiv m m R where
  val := 1
  inv := 1
  val_inv := by simp
  inv_val := by simp

@[simp]
theorem val_refl : (refl : GeneralLinearEquiv m m R).val = 1 :=
  rfl

@[simp]
theorem inv_refl : (refl : GeneralLinearEquiv m m R).inv = 1 :=
  rfl

/-- Symmetry: swap `val` and `inv`. -/
def symm (e : GeneralLinearEquiv m n R) : GeneralLinearEquiv n m R where
  val := e.inv
  inv := e.val
  val_inv := e.inv_val
  inv_val := e.val_inv

@[simp]
theorem val_symm (e : GeneralLinearEquiv m n R) : e.symm.val = e.inv :=
  rfl

@[simp]
theorem inv_symm (e : GeneralLinearEquiv m n R) : e.symm.inv = e.val :=
  rfl

@[simp]
theorem symm_symm (e : GeneralLinearEquiv m n R) : e.symm.symm = e := by
  cases e
  rfl

@[simp]
theorem refl_symm : (refl : GeneralLinearEquiv m m R).symm = refl :=
  rfl

/-- Composition / transitivity: `val = e.val * f.val`, inverse in reverse order. -/
def trans (e : GeneralLinearEquiv m n R) (f : GeneralLinearEquiv n p R) :
    GeneralLinearEquiv m p R where
  val := e.val * f.val
  inv := f.inv * e.inv
  val_inv := by
    calc (e.val * f.val) * (f.inv * e.inv)
        = e.val * (f.val * (f.inv * e.inv)) := by
            rw [Matrix.mul_assoc e.val f.val (f.inv * e.inv)]
      _ = e.val * ((f.val * f.inv) * e.inv) := by
            rw [← Matrix.mul_assoc f.val f.inv e.inv]
      _ = e.val * ((1 : Matrix n n R) * e.inv) := by rw [f.val_inv]
      _ = e.val * e.inv := by simp
      _ = (1 : Matrix m m R) := by rw [e.val_inv]
  inv_val := by
    calc (f.inv * e.inv) * (e.val * f.val)
        = f.inv * (e.inv * (e.val * f.val)) := by
            rw [Matrix.mul_assoc f.inv e.inv (e.val * f.val)]
      _ = f.inv * ((e.inv * e.val) * f.val) := by
            rw [← Matrix.mul_assoc e.inv e.val f.val]
      _ = f.inv * ((1 : Matrix n n R) * f.val) := by rw [e.inv_val]
      _ = f.inv * f.val := by simp
      _ = (1 : Matrix p p R) := by rw [f.inv_val]

@[simp]
theorem val_trans (e : GeneralLinearEquiv m n R) (f : GeneralLinearEquiv n p R) :
    (e.trans f).val = e.val * f.val :=
  rfl

@[simp]
theorem inv_trans (e : GeneralLinearEquiv m n R) (f : GeneralLinearEquiv n p R) :
    (e.trans f).inv = f.inv * e.inv :=
  rfl

@[simp]
theorem refl_trans (e : GeneralLinearEquiv m n R) :
    (refl : GeneralLinearEquiv m m R).trans e = e := by
  apply ext
  simp

@[simp]
theorem trans_refl (e : GeneralLinearEquiv m n R) :
    e.trans (refl : GeneralLinearEquiv n n R) = e := by
  apply ext
  simp

theorem trans_assoc (e : GeneralLinearEquiv m n R) (f : GeneralLinearEquiv n p R)
    (g : GeneralLinearEquiv p q R) :
    (e.trans f).trans g = e.trans (f.trans g) := by
  apply ext
  simp [Matrix.mul_assoc]

@[simp]
theorem trans_symm (e : GeneralLinearEquiv m n R) :
    e.trans e.symm = (refl : GeneralLinearEquiv m m R) := by
  apply ext
  simp

@[simp]
theorem symm_trans (e : GeneralLinearEquiv m n R) :
    e.symm.trans e = (refl : GeneralLinearEquiv n n R) := by
  apply ext
  simp

/-- Embed a square `GL` element as a heterogeneous equivalence. -/
def ofGL (g : GL m R) : GeneralLinearEquiv m m R where
  val := (g : Matrix m m R)
  inv := ((g⁻¹ : GL m R) : Matrix m m R)
  val_inv := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

/-- Project a square heterogeneous equivalence to `GL`. -/
def toGL (e : GeneralLinearEquiv m m R) : GL m R where
  val := e.val
  inv := e.inv
  val_inv := e.val_inv
  inv_val := e.inv_val

@[simp]
theorem val_ofGL (g : GL m R) : (ofGL g).val = (g : Matrix m m R) :=
  rfl

@[simp]
theorem inv_ofGL (g : GL m R) :
    (ofGL g).inv = ((g⁻¹ : GL m R) : Matrix m m R) :=
  rfl

@[simp]
theorem val_toGL (e : GeneralLinearEquiv m m R) : (toGL e : Matrix m m R) = e.val :=
  rfl

@[simp]
theorem toGL_ofGL (g : GL m R) : toGL (ofGL g) = g := by
  apply Units.ext
  rfl

@[simp]
theorem ofGL_toGL (e : GeneralLinearEquiv m m R) : ofGL (toGL e) = e := by
  apply ext
  rfl

/-- Equivalence between square `GeneralLinearEquiv` and `GL`. -/
def equivGL : GeneralLinearEquiv m m R ≃ GL m R where
  toFun := toGL
  invFun := ofGL
  left_inv := ofGL_toGL
  right_inv := toGL_ofGL

/-! ### Coefficient functoriality -/

/-- Map coefficients along a semiring hom. -/
def map (f : R →+* S) (e : GeneralLinearEquiv m n R) : GeneralLinearEquiv m n S where
  val := e.val.map f
  inv := e.inv.map f
  val_inv := by
    calc e.val.map f * e.inv.map f
        = (e.val * e.inv).map f := by rw [Matrix.map_mul]
      _ = (1 : Matrix m m R).map f := by rw [e.val_inv]
      _ = 1 := by rw [Matrix.map_one f (map_zero f) (map_one f)]
  inv_val := by
    calc e.inv.map f * e.val.map f
        = (e.inv * e.val).map f := by rw [Matrix.map_mul]
      _ = (1 : Matrix n n R).map f := by rw [e.inv_val]
      _ = 1 := by rw [Matrix.map_one f (map_zero f) (map_one f)]

@[simp]
theorem val_map (f : R →+* S) (e : GeneralLinearEquiv m n R) :
    (e.map f).val = e.val.map f :=
  rfl

@[simp]
theorem inv_map (f : R →+* S) (e : GeneralLinearEquiv m n R) :
    (e.map f).inv = e.inv.map f :=
  rfl

@[simp]
theorem map_refl (f : R →+* S) :
    (refl : GeneralLinearEquiv m m R).map f = refl := by
  apply ext
  simp [Matrix.map_one f (map_zero f) (map_one f)]

@[simp]
theorem map_symm (f : R →+* S) (e : GeneralLinearEquiv m n R) :
    (e.map f).symm = e.symm.map f :=
  rfl

@[simp]
theorem map_trans (f : R →+* S) (e : GeneralLinearEquiv m n R)
    (g : GeneralLinearEquiv n p R) :
    (e.trans g).map f = (e.map f).trans (g.map f) := by
  apply ext
  simp [Matrix.map_mul]

theorem map_id (e : GeneralLinearEquiv m n R) :
    e.map (RingHom.id R) = e := by
  apply ext
  simp

theorem map_comp (f : R →+* S) (g : S →+* T) (e : GeneralLinearEquiv m n R) :
    e.map (g.comp f) = (e.map f).map g := by
  apply ext
  simp [Matrix.map_map]

theorem map_comp_assoc (f : R →+* S) (g : S →+* T) :
    (GeneralLinearEquiv.map (m := m) (n := n) (g.comp f)) =
      (GeneralLinearEquiv.map g).comp (GeneralLinearEquiv.map (m := m) (n := n) f) := by
  funext e
  exact map_comp f g e

/-! ### Index reindexing -/

/-- Reindex rows by `em : m' ≃ m` and columns by `en : n' ≃ n`.

The forward matrix is `val.submatrix em en` and the backward matrix is
`inv.submatrix en em`. -/
def reindex (em : m' ≃ m) (en : n' ≃ n) (e : GeneralLinearEquiv m n R) :
    GeneralLinearEquiv m' n' R where
  val := e.val.submatrix em en
  inv := e.inv.submatrix en em
  val_inv := by
    calc e.val.submatrix em en * e.inv.submatrix en em
        = (e.val * e.inv).submatrix em em := by rw [Matrix.submatrix_mul_equiv]
      _ = (1 : Matrix m m R).submatrix em em := by rw [e.val_inv]
      _ = 1 := by rw [Matrix.submatrix_one_equiv]
  inv_val := by
    calc e.inv.submatrix en em * e.val.submatrix em en
        = (e.inv * e.val).submatrix en en := by rw [Matrix.submatrix_mul_equiv]
      _ = (1 : Matrix n n R).submatrix en en := by rw [e.inv_val]
      _ = 1 := by rw [Matrix.submatrix_one_equiv]

@[simp]
theorem val_reindex (em : m' ≃ m) (en : n' ≃ n) (e : GeneralLinearEquiv m n R) :
    (e.reindex em en).val = e.val.submatrix em en :=
  rfl

@[simp]
theorem inv_reindex (em : m' ≃ m) (en : n' ≃ n) (e : GeneralLinearEquiv m n R) :
    (e.reindex em en).inv = e.inv.submatrix en em :=
  rfl

@[simp]
theorem reindex_refl (e : GeneralLinearEquiv m n R) :
    e.reindex (Equiv.refl m) (Equiv.refl n) = e := by
  apply ext
  simp [Matrix.submatrix_id_id]

theorem reindex_reindex (em₁ : m' ≃ m) (en₁ : n' ≃ n) (em₂ : q ≃ m') (en₂ : p ≃ n')
    (e : GeneralLinearEquiv m n R) :
    (e.reindex em₁ en₁).reindex em₂ en₂ =
      e.reindex (em₂.trans em₁) (en₂.trans en₁) := by
  apply ext
  simp [Matrix.submatrix_submatrix]

@[simp]
theorem reindex_symm_trans (em : m' ≃ m) (en : n' ≃ n) (e : GeneralLinearEquiv m n R) :
    (e.reindex em en).symm = (e.symm).reindex en em :=
  rfl

theorem reindex_map (em : m' ≃ m) (en : n' ≃ n) (f : R →+* S)
    (e : GeneralLinearEquiv m n R) :
    (e.reindex em en).map f = (e.map f).reindex em en := by
  apply ext
  simp [Matrix.submatrix_map]

theorem map_reindex (em : m' ≃ m) (en : n' ≃ n) (f : R →+* S)
    (e : GeneralLinearEquiv m n R) :
    (e.map f).reindex em en = (e.reindex em en).map f :=
  (reindex_map em en f e).symm

/-! ### Heterogeneous monomial equivalences -/

/-- Heterogeneous monomial equivalence: for `u : m → Rˣ` and `σ : n ≃ m`,
the matrix with entry `u i` at `(i, σ⁻¹ i)` and `0` elsewhere, i.e.
`val i j = if σ j = i then (u i : R) else 0`.

Its inverse has entry `(u j)⁻¹` at `(σ⁻¹ j, j)`. Implemented as
`diagonal u * (σ⁻¹).toPEquiv.toMatrix`. -/
def monomialEquiv (u : m → Rˣ) (σ : n ≃ m) : GeneralLinearEquiv m n R where
  val := Matrix.diagonal (fun i => (u i : R)) * σ.symm.toPEquiv.toMatrix
  inv := σ.toPEquiv.toMatrix * Matrix.diagonal (fun i => (↑((u i)⁻¹) : R))
  val_inv := by
    set d : m → R := fun i => (u i : R)
    set dInv : m → R := fun i => (↑((u i)⁻¹) : R)
    set Q : Matrix m n R := σ.symm.toPEquiv.toMatrix
    set QT : Matrix n m R := σ.toPEquiv.toMatrix
    have hQQT : Q * QT = 1 := by
      rw [← PEquiv.toMatrix_trans]
      have hTrans : σ.symm.toPEquiv.trans σ.toPEquiv = PEquiv.refl m := by
        rw [← Equiv.toPEquiv_trans, Equiv.symm_trans_self, Equiv.toPEquiv_refl]
      rw [hTrans, PEquiv.toMatrix_refl]
    have hDD : Matrix.diagonal d * Matrix.diagonal dInv = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have hEq : (fun i => d i * dInv i) = fun _ => (1 : R) := by
        funext i
        calc d i * dInv i
            = (u i : R) * (↑((u i)⁻¹) : R) := rfl
          _ = ((u i * (u i)⁻¹ : Rˣ) : R) := by rw [← Units.val_mul]
          _ = ((1 : Rˣ) : R) := by rw [mul_inv_cancel]
          _ = 1 := rfl
      rw [hEq, Matrix.diagonal_one]
    calc (Matrix.diagonal d * Q) * (QT * Matrix.diagonal dInv)
        = Matrix.diagonal d * (Q * (QT * Matrix.diagonal dInv)) := by
            rw [Matrix.mul_assoc (Matrix.diagonal d) Q (QT * Matrix.diagonal dInv)]
      _ = Matrix.diagonal d * ((Q * QT) * Matrix.diagonal dInv) := by
            rw [← Matrix.mul_assoc Q QT (Matrix.diagonal dInv)]
      _ = Matrix.diagonal d * ((1 : Matrix m m R) * Matrix.diagonal dInv) := by rw [hQQT]
      _ = Matrix.diagonal d * Matrix.diagonal dInv := by rw [Matrix.one_mul]
      _ = 1 := hDD
  inv_val := by
    set d : m → R := fun i => (u i : R)
    set dInv : m → R := fun i => (↑((u i)⁻¹) : R)
    set Q : Matrix m n R := σ.symm.toPEquiv.toMatrix
    set QT : Matrix n m R := σ.toPEquiv.toMatrix
    have hQTQ : QT * Q = 1 := by
      rw [← PEquiv.toMatrix_trans]
      have hTrans : σ.toPEquiv.trans σ.symm.toPEquiv = PEquiv.refl n := by
        rw [← Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl]
      rw [hTrans, PEquiv.toMatrix_refl]
    have hDInvD : Matrix.diagonal dInv * Matrix.diagonal d = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      have hEq : (fun i => dInv i * d i) = fun _ => (1 : R) := by
        funext i
        calc dInv i * d i
            = (↑((u i)⁻¹) : R) * (u i : R) := rfl
          _ = (((u i)⁻¹ * u i : Rˣ) : R) := by rw [← Units.val_mul]
          _ = ((1 : Rˣ) : R) := by rw [inv_mul_cancel]
          _ = 1 := rfl
      rw [hEq, Matrix.diagonal_one]
    calc (QT * Matrix.diagonal dInv) * (Matrix.diagonal d * Q)
        = QT * (Matrix.diagonal dInv * (Matrix.diagonal d * Q)) := by
            rw [Matrix.mul_assoc QT (Matrix.diagonal dInv) (Matrix.diagonal d * Q)]
      _ = QT * ((Matrix.diagonal dInv * Matrix.diagonal d) * Q) := by
            rw [← Matrix.mul_assoc (Matrix.diagonal dInv) (Matrix.diagonal d) Q]
      _ = QT * ((1 : Matrix m m R) * Q) := by rw [hDInvD]
      _ = QT * Q := by rw [Matrix.one_mul]
      _ = 1 := hQTQ

theorem val_monomialEquiv_entry (u : m → Rˣ) (σ : n ≃ m) (i : m) (j : n) :
    (monomialEquiv (R := R) u σ).val i j = if σ j = i then (u i : R) else 0 := by
  classical
  have hVal : (monomialEquiv (R := R) u σ).val =
      Matrix.diagonal (fun i => (u i : R)) * σ.symm.toPEquiv.toMatrix := rfl
  have hDiag :
      (Matrix.diagonal (fun i => (u i : R)) * σ.symm.toPEquiv.toMatrix :
        Matrix m n R) i j =
      (u i : R) * σ.symm.toPEquiv.toMatrix i j := by
    rw [Matrix.diagonal_mul]
  have hToMat :
      σ.symm.toPEquiv.toMatrix i j =
      if j ∈ σ.symm.toPEquiv i then (1 : R) else 0 := by
    rw [PEquiv.toMatrix_apply]
  have hMem : (j ∈ σ.symm.toPEquiv i) ↔ σ j = i := by
    rw [Equiv.toPEquiv_apply, Option.mem_def]
    constructor
    · intro h
      rw [Option.some.injEq] at h
      calc σ j = σ (σ.symm i) := by rw [h]
        _ = i := by simp
    · intro h
      rw [Option.some.injEq]
      rw [Equiv.symm_apply_eq]
      exact h.symm
  calc (monomialEquiv (R := R) u σ).val i j
      = (Matrix.diagonal (fun i => (u i : R)) * σ.symm.toPEquiv.toMatrix : Matrix m n R) i j := by
          rw [hVal]
    _ = (u i : R) * σ.symm.toPEquiv.toMatrix i j := by rw [hDiag]
    _ = (u i : R) * if j ∈ σ.symm.toPEquiv i then (1 : R) else 0 := by rw [hToMat]
    _ = if j ∈ σ.symm.toPEquiv i then (u i : R) else 0 := by
          simp [mul_ite, mul_one, mul_zero]
    _ = if σ j = i then (u i : R) else 0 := by rw [if_congr hMem rfl rfl]

theorem inv_monomialEquiv_entry (u : m → Rˣ) (σ : n ≃ m) (i : n) (j : m) :
    (monomialEquiv (R := R) u σ).inv i j =
      if σ i = j then (↑((u j)⁻¹) : R) else 0 := by
  classical
  have hInv : (monomialEquiv (R := R) u σ).inv =
      σ.toPEquiv.toMatrix * Matrix.diagonal (fun i => (↑((u i)⁻¹) : R)) := rfl
  have hMul :
      (σ.toPEquiv.toMatrix *
        Matrix.diagonal (fun i => (↑((u i)⁻¹) : R)) : Matrix n m R) i j =
      σ.toPEquiv.toMatrix i j * (↑((u j)⁻¹) : R) := by
    rw [Matrix.mul_diagonal]
  have hToMat :
      σ.toPEquiv.toMatrix i j =
      if j ∈ σ.toPEquiv i then (1 : R) else 0 := by
    rw [PEquiv.toMatrix_apply]
  have hMem : (j ∈ σ.toPEquiv i) ↔ σ i = j := by
    rw [Equiv.toPEquiv_apply, Option.mem_def]
    simp
  calc (monomialEquiv (R := R) u σ).inv i j
      = (σ.toPEquiv.toMatrix * Matrix.diagonal (fun i => (↑((u i)⁻¹) : R)) : Matrix n m R) i j := by
          rw [hInv]
    _ = σ.toPEquiv.toMatrix i j * (↑((u j)⁻¹) : R) := by rw [hMul]
    _ = (if j ∈ σ.toPEquiv i then (1 : R) else 0) * (↑((u j)⁻¹) : R) := by rw [hToMat]
    _ = if j ∈ σ.toPEquiv i then (↑((u j)⁻¹) : R) else 0 := by
          simp [ite_mul, one_mul, zero_mul]
    _ = if σ i = j then (↑((u j)⁻¹) : R) else 0 := by rw [if_congr hMem rfl rfl]

theorem val_monomialEquiv (u : m → Rˣ) (σ : n ≃ m) :
    (monomialEquiv (R := R) u σ).val =
      Matrix.of fun i j => if σ j = i then (u i : R) else 0 := by
  ext i j
  rw [val_monomialEquiv_entry]
  rfl

theorem inv_monomialEquiv (u : m → Rˣ) (σ : n ≃ m) :
    (monomialEquiv (R := R) u σ).inv =
      Matrix.of fun i j => if σ i = j then (↑((u j)⁻¹) : R) else 0 := by
  ext i j
  rw [inv_monomialEquiv_entry]
  rfl

@[simp]
theorem val_monomialEquiv_apply (u : m → Rˣ) (σ : n ≃ m) (i : m) (j : n) :
    (monomialEquiv (R := R) u σ).val i j = if σ j = i then (u i : R) else 0 :=
  val_monomialEquiv_entry u σ i j

@[simp]
theorem inv_monomialEquiv_apply (u : m → Rˣ) (σ : n ≃ m) (i : n) (j : m) :
    (monomialEquiv (R := R) u σ).inv i j =
      if σ i = j then (↑((u j)⁻¹) : R) else 0 :=
  inv_monomialEquiv_entry u σ i j

/-- Symmetry of a monomial equivalence: swaps `u` via `σ` and inverts units. -/
theorem symm_monomialEquiv (u : m → Rˣ) (σ : n ≃ m) :
    (monomialEquiv (R := R) u σ).symm =
      monomialEquiv (fun i : n => (u (σ i))⁻¹) σ.symm := by
  apply ext
  ext i j
  simp only [val_symm, inv_monomialEquiv_entry, val_monomialEquiv_entry]
  by_cases h : σ i = j
  · rw [ite_eq_left h]
    have h2 : σ.symm j = i := by
      rw [Equiv.symm_apply_eq]
      exact h.symm
    rw [ite_eq_left h2, h]
  · rw [ite_eq_right h]
    have h2 : ¬ σ.symm j = i := by
      intro heq
      have : σ i = j := by
        calc σ i = σ (σ.symm j) := by rw [heq]
          _ = j := by simp
      exact h this
    rw [ite_eq_right h2]

/-- Coefficient naturality under `Units.map`. -/
theorem map_monomialEquiv (f : R →+* S) (u : m → Rˣ) (σ : n ≃ m) :
    (monomialEquiv (R := R) u σ).map f =
      monomialEquiv (fun i => Units.map f (u i)) σ := by
  apply ext
  ext i j
  simp only [val_map, val_monomialEquiv_entry, Matrix.map_apply]
  by_cases h : σ j = i <;> simp [h, Units.coe_map]

/-- Reindexing a monomial equivalence composes the underlying equivalence. -/
theorem reindex_monomialEquiv (em : m' ≃ m) (en : n' ≃ n) (u : m → Rˣ) (σ : n ≃ m) :
    (monomialEquiv (R := R) u σ).reindex em en =
      monomialEquiv (fun i' => u (em i')) (en.trans (σ.trans em.symm)) := by
  apply ext
  ext i' j'
  simp only [val_reindex, Matrix.submatrix_apply, val_monomialEquiv_entry]
  by_cases h : σ (en j') = em i'
  · have h' : (en.trans (σ.trans em.symm)) j' = i' := by
      simp [Equiv.trans_apply, h]
    rw [ite_eq_left h, ite_eq_left h']
  · have h' : (en.trans (σ.trans em.symm)) j' ≠ i' := by
      intro heq
      have h1 : em.symm (σ (en j')) = (en.trans (σ.trans em.symm)) j' := by
        simp [Equiv.trans_apply]
      rw [heq] at h1
      have h2 : σ (en j') = em i' := by
        calc σ (en j') = em (em.symm (σ (en j'))) := by simp
          _ = em i' := by rw [h1]
      exact h h2
    rw [ite_eq_right h, ite_eq_right h']

/-! ### Square bridges and monomial comparison -/

/-- Square bridge: `monomialEquiv` corresponds to `monomialMatrixHom` via `toGL`. -/
theorem toGL_monomialEquiv (u : m → Rˣ) (σ : Equiv.Perm m) :
    toGL (monomialEquiv (R := R) u σ) =
      GeneralLinearGroup.monomialMatrixHom R m ⟨u, σ⟩ := by
  apply Units.ext
  rfl

/-- The heterogeneous monomial equivalence agrees with the existing
`monomialMatrixHom` under the square bridge. -/
theorem monomialEquiv_eq_monomialMatrixHom (u : m → Rˣ) (σ : Equiv.Perm m) :
    (monomialEquiv (R := R) u σ).val =
      (GeneralLinearGroup.monomialMatrixHom R m ⟨u, σ⟩ : Matrix m m R) := by
  have h := toGL_monomialEquiv (R := R) u σ
  have hVal : (toGL (monomialEquiv (R := R) u σ) : Matrix m m R) =
      (GeneralLinearGroup.monomialMatrixHom R m ⟨u, σ⟩ : Matrix m m R) :=
    congrArg Units.val h
  simp only [val_toGL] at hVal
  exact hVal

end GeneralLinearEquiv

end Matrix
