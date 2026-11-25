/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Rectangular row-and-column finite matrices

The coefficients of a locally finite matrix are its original matrix entries.
Every row and every column has finite support; neither a uniform support bound
nor a finite coefficient range is required. Products use the ordinary ordered
matrix formula over arbitrary noncommutative semirings.

The original row action on finitely supported free left modules is faithful.
It sends a row vector `x` to `xA`, so the action of `AB` is the action of `A`
followed by the action of `B`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe um un up uq uR uS

namespace Matrix

/-- A matrix whose every original row and column has finite support. -/
structure LocallyFinite (m : Type um) (n : Type un) (R : Type uR) [Zero R] where
  /-- The original coefficient matrix. -/
  toMatrix : Matrix m n R
  /-- Each original row is finitely supported. -/
  row_finite : ∀ i, (Function.support (toMatrix i)).Finite
  /-- Each original column is finitely supported. -/
  column_finite : ∀ j, (Function.support (fun i => toMatrix i j)).Finite

namespace LocallyFinite

variable {m : Type um} {n : Type un} {p : Type up} {q : Type uq}
  {R : Type uR} {S : Type uS}

instance [Zero R] : CoeFun (LocallyFinite m n R) (fun _ => m → n → R) :=
  ⟨LocallyFinite.toMatrix⟩

/-- Equality of the original coefficient matrices determines the bundled matrix. -/
theorem toMatrix_injective [Zero R] :
    Function.Injective (toMatrix : LocallyFinite m n R → Matrix m n R) := by
  intro A B h
  cases A
  cases B
  cases h
  rfl

/-- Locally finite matrices are equal when all original entries are equal. -/
@[ext]
theorem ext [Zero R] {A B : LocallyFinite m n R}
    (h : ∀ i j, A i j = B i j) : A = B :=
  toMatrix_injective (funext fun i => funext (h i))

/-- The exact finitely supported vector carried by an original row. -/
def row [Zero R] (A : LocallyFinite m n R) (i : m) : n →₀ R :=
  Finsupp.ofSupportFinite (A i) (A.row_finite i)

/-- The exact finitely supported vector carried by an original column. -/
def column [Zero R] (A : LocallyFinite m n R) (j : n) : m →₀ R :=
  Finsupp.ofSupportFinite (fun i => A i j) (A.column_finite j)

/-- Reading an exact row retains the original coefficient. -/
@[simp]
theorem row_apply [Zero R] (A : LocallyFinite m n R) (i : m) (j : n) :
    A.row i j = A i j := rfl

/-- Reading an exact column retains the original coefficient. -/
@[simp]
theorem column_apply [Zero R] (A : LocallyFinite m n R) (i : m) (j : n) :
    A.column j i = A i j := rfl

/-- Construct the original matrix from exact finite rows and earned finite columns. -/
def ofRows [Zero R] (v : m → n →₀ R)
    (hv : ∀ j, (Function.support (fun i => v i j)).Finite) : LocallyFinite m n R where
  toMatrix i j := v i j
  row_finite i := (v i).hasFiniteSupport
  column_finite := hv

/-- The row constructor retains every supplied coefficient. -/
@[simp]
theorem ofRows_apply [Zero R] (v : m → n →₀ R)
    (hv : ∀ j, (Function.support (fun i => v i j)).Finite) (i : m) (j : n) :
    ofRows v hv i j = v i j := rfl

/-- The exact row of a row-constructed matrix is the original supplied vector. -/
@[simp]
theorem row_ofRows [Zero R] (v : m → n →₀ R)
    (hv : ∀ j, (Function.support (fun i => v i j)).Finite) (i : m) :
    (ofRows v hv).row i = v i := by
  ext j
  rfl

/-- Reassembling the original exact rows returns the same matrix. -/
@[simp]
theorem ofRows_row [Zero R] (A : LocallyFinite m n R) :
    ofRows A.row (fun j => A.column_finite j) = A := by
  ext i j
  rfl

/-- A zero-preserving coefficient map preserves both local finiteness conditions. -/
def map [Zero R] [Zero S] (f : ZeroHom R S) (A : LocallyFinite m n R) :
    LocallyFinite m n S where
  toMatrix i j := f (A i j)
  row_finite i := (A.row_finite i).subset <| by
    intro j hj
    change f (A i j) ≠ 0 at hj
    change A i j ≠ 0
    intro h
    exact hj (h ▸ f.map_zero)
  column_finite j := (A.column_finite j).subset <| by
    intro i hi
    change f (A i j) ≠ 0 at hi
    change A i j ≠ 0
    intro h
    exact hi (h ▸ f.map_zero)

/-- Entrywise maps act on the original coefficient. -/
@[simp]
theorem map_apply [Zero R] [Zero S] (f : ZeroHom R S) (A : LocallyFinite m n R)
    (i : m) (j : n) : map f A i j = f (A i j) := rfl

/-- Entrywise identity is the identity on the original matrix. -/
@[simp]
theorem map_id [Zero R] (A : LocallyFinite m n R) : map (ZeroHom.id R) A = A := by
  ext i j
  rfl

/-- Entrywise composition retains the actual order of coefficient maps. -/
theorem map_comp [Zero R] [Zero S] {T : Type*} [Zero T]
    (g : ZeroHom S T) (f : ZeroHom R S) (A : LocallyFinite m n R) :
    map (g.comp f) A = map g (map f A) := by
  ext i j
  rfl

instance [Zero R] : Zero (LocallyFinite m n R) where
  zero :=
    { toMatrix := (0 : Matrix m n R)
      row_finite := fun _ => by
        change (Function.support (fun _ : n => (0 : R))).Finite
        simp
      column_finite := fun _ => by
        change (Function.support (fun _ : m => (0 : R))).Finite
        simp }

/-- The original zero matrix has zero entries. -/
@[simp]
theorem zero_apply [Zero R] (i : m) (j : n) : (0 : LocallyFinite m n R) i j = 0 := rfl

instance [AddZeroClass R] : Add (LocallyFinite m n R) where
  add A B :=
    { toMatrix := A.toMatrix + B.toMatrix
      row_finite := fun i => ((A.row_finite i).union (B.row_finite i)).subset <| by
        intro j hj
        by_contra h
        simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
        exact hj (by simp [h.1, h.2])
      column_finite := fun j => ((A.column_finite j).union (B.column_finite j)).subset <| by
        intro i hi
        by_contra h
        simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
        exact hi (by simp [h.1, h.2]) }

/-- Addition is pointwise on the original coefficients. -/
@[simp]
theorem add_apply [AddZeroClass R] (A B : LocallyFinite m n R) (i : m) (j : n) :
    (A + B) i j = A i j + B i j := rfl

instance [AddMonoid R] : SMul ℕ (LocallyFinite m n R) where
  smul k A := map ⟨fun r => k • r, nsmul_zero k⟩ A

/-- Natural repeated addition acts on each original coefficient. -/
@[simp]
theorem nsmul_apply [AddMonoid R] (k : ℕ) (A : LocallyFinite m n R) (i : m) (j : n) :
    (k • A) i j = k • A i j := rfl

instance [AddCommMonoid R] : AddCommMonoid (LocallyFinite m n R) :=
  toMatrix_injective.addCommMonoid toMatrix rfl (fun _ _ => rfl) (fun _ _ => rfl)

instance [AddGroup R] : Neg (LocallyFinite m n R) where
  neg A := map ⟨fun r => -r, neg_zero⟩ A

/-- Negation is pointwise on the original coefficients. -/
@[simp]
theorem neg_apply [AddGroup R] (A : LocallyFinite m n R) (i : m) (j : n) :
    (-A) i j = -A i j := rfl

instance [AddGroup R] : Sub (LocallyFinite m n R) where
  sub A B := A + -B

/-- Subtraction is pointwise on the original coefficients. -/
@[simp]
theorem sub_apply [AddGroup R] (A B : LocallyFinite m n R) (i : m) (j : n) :
    (A - B) i j = A i j - B i j := by
  change A i j + -(B i j) = A i j - B i j
  exact (sub_eq_add_neg (A i j) (B i j)).symm

instance [AddGroup R] : SMul ℤ (LocallyFinite m n R) where
  smul k A := map ⟨fun r => k • r, zsmul_zero k⟩ A

/-- Integral repeated addition acts on each original coefficient. -/
@[simp]
theorem zsmul_apply [AddGroup R] (k : ℤ) (A : LocallyFinite m n R) (i : m) (j : n) :
    (k • A) i j = k • A i j := rfl

instance [AddCommGroup R] : AddCommGroup (LocallyFinite m n R) :=
  toMatrix_injective.addCommGroup toMatrix rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => by ext i j; exact sub_apply _ _ i j) (fun _ _ => rfl) (fun _ _ => rfl)

/-- The original exact row action sends the finitely supported row vector `x` to `xA`. -/
def rowAction [Semiring R] (A : LocallyFinite m n R) :
    (m →₀ R) →ₗ[R] (n →₀ R) := Finsupp.linearCombination R A.row

/-- A basis row is sent to its original row with the scalar on the left. -/
@[simp]
theorem rowAction_single [Semiring R] (A : LocallyFinite m n R) (i : m) (r : R) :
    A.rowAction (Finsupp.single i r) = r • A.row i :=
  Finsupp.linearCombination_single R r i

/-- The original row action evaluates by the ordered finite coefficient sum. -/
theorem rowAction_apply [Semiring R] (A : LocallyFinite m n R) (x : m →₀ R) (j : n) :
    A.rowAction x j = ∑ i ∈ x.support, x i * A i j := by
  classical
  change (Finsupp.linearCombination R A.row x) j = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, row_apply, Finsupp.sum]

/-- The original free-left-module row action determines every coefficient matrix. -/
theorem rowAction_injective [Semiring R] :
    Function.Injective (rowAction : LocallyFinite m n R → (m →₀ R) →ₗ[R] (n →₀ R)) := by
  intro A B h
  ext i j
  have hi := congrArg (fun f : (m →₀ R) →ₗ[R] (n →₀ R) =>
    f (Finsupp.single i 1) j) h
  simpa using hi

/-- The column support of an original product lies in a finite union of original columns. -/
theorem rowAction_rows_column_finite [Semiring R]
    (A : LocallyFinite m n R) (B : LocallyFinite n p R) (j : p) :
    (Function.support (fun i => B.rowAction (A.row i) j)).Finite := by
  classical
  refine ((B.column j).support.finite_toSet.biUnion
    (fun k _ => A.column_finite k)).subset ?_
  intro i hi
  rw [Function.mem_support, rowAction_apply] at hi
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  have hA : A i k ≠ 0 := by simpa using hk
  have hB : B k j ≠ 0 := by
    intro hB
    exact hne (by simp [hB])
  exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨by simpa using hB, hA⟩⟩

/-- The original rectangular product, with its finite rows and earned finite columns. -/
def comp [Semiring R] (A : LocallyFinite m n R) (B : LocallyFinite n p R) :
    LocallyFinite m p R :=
  ofRows (fun i => B.rowAction (A.row i)) (rowAction_rows_column_finite A B)

/-- Every product coefficient is the ordinary ordered finite matrix sum. -/
theorem comp_apply [Semiring R] (A : LocallyFinite m n R) (B : LocallyFinite n p R)
    (i : m) (j : p) :
    A.comp B i j = ∑ k ∈ (A.row i).support, A i k * B k j := by
  exact B.rowAction_apply (A.row i) j

/-- A nonzero original product entry has an actual contributing intermediate index. -/
theorem exists_comp_term [Semiring R] (A : LocallyFinite m n R)
    (B : LocallyFinite n p R) (i : m) (j : p) (h : A.comp B i j ≠ 0) :
    ∃ k, A i k ≠ 0 ∧ B k j ≠ 0 := by
  classical
  rw [comp_apply] at h
  obtain ⟨k, hk, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨k, by simpa using hk, ?_⟩
  intro hB
  exact hne (by simp [hB])

/-- A product row is the actual action of the second matrix on the first original row. -/
@[simp]
theorem row_comp [Semiring R] (A : LocallyFinite m n R) (B : LocallyFinite n p R) (i : m) :
    (A.comp B).row i = B.rowAction (A.row i) := row_ofRows _ _ i

/-- Multiplication acts by the original composite, retaining the noncommutative order. -/
theorem rowAction_comp [Semiring R] (A : LocallyFinite m n R) (B : LocallyFinite n p R) :
    (A.comp B).rowAction = B.rowAction.comp A.rowAction := by
  change Finsupp.linearCombination R (A.comp B).row = _
  rw [show (A.comp B).row = fun i => B.rowAction (A.row i) from funext (row_comp A B)]
  exact Finsupp.linearCombination_linear_comp R B.rowAction (v := A.row)

/-- Associativity holds for the original rectangular matrix multiplication. -/
theorem comp_assoc [Semiring R] (A : LocallyFinite m n R)
    (B : LocallyFinite n p R) (C : LocallyFinite p q R) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  apply rowAction_injective
  simp only [rowAction_comp, LinearMap.comp_assoc]

end LocallyFinite

end Matrix

end
