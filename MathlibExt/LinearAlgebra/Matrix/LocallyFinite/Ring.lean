/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.Basic
public import Mathlib.Algebra.Ring.InjSurj

/-!
# The ring of row-and-column finite matrices

Square locally finite matrices carry their ordinary ordered multiplication.
The identity and scalar casts are the original diagonal matrices. The ring
structure retains arbitrary index types and noncommutative coefficient rings.
Finite-index matrices agree with Mathlib's ordinary matrix ring, and entrywise
ring maps preserve the same product.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

universe um un up uR uS

namespace Matrix.LocallyFinite

variable {m : Type um} {n : Type un} {p : Type up}
  {R : Type uR} {S : Type uS}

/-- The original diagonal matrix has at most one nonzero entry in each row and column. -/
def diagonal [Zero R] (d : n → R) : Matrix.LocallyFinite n n R := by
  classical
  exact
    { toMatrix := Matrix.diagonal d
      row_finite := fun i => (Set.finite_singleton i).subset <| by
        intro j hj
        by_cases h : i = j
        · simp [h]
        · exact False.elim (hj (by simp [h]))
      column_finite := fun j => (Set.finite_singleton j).subset <| by
        intro i hi
        by_cases h : i = j
        · simp [h]
        · exact False.elim (hi (by simp [h])) }

/-- Diagonal entries have the literal Kronecker formula. -/
theorem diagonal_apply [Zero R] (d : n → R) (i j : n) :
    diagonal d i j = if i = j then d i else 0 := by
  classical
  rfl

/-- The original diagonal row is its exact singleton vector. -/
@[simp]
theorem row_diagonal [Zero R] (d : n → R) (i : n) :
    (diagonal d).row i = Finsupp.single i (d i) := by
  classical
  ext j
  simp only [row_apply, diagonal_apply, Finsupp.single_apply]

/-- Finite index types turn every original matrix into a locally finite matrix. -/
def ofMatrix [Zero R] [Finite m] [Finite n] (A : Matrix m n R) :
    Matrix.LocallyFinite m n R where
  toMatrix := A
  row_finite _ := Set.toFinite _
  column_finite _ := Set.toFinite _

/-- Finite-matrix inclusion retains every original coefficient. -/
@[simp]
theorem ofMatrix_apply [Zero R] [Finite m] [Finite n]
    (A : Matrix m n R) (i : m) (j : n) : ofMatrix A i j = A i j := rfl

/-- Every locally finite matrix with finite indices returns its original matrix. -/
@[simp]
theorem ofMatrix_toMatrix [Zero R] [Finite m] [Finite n]
    (A : Matrix.LocallyFinite m n R) : ofMatrix A.toMatrix = A := by
  ext i j
  rfl

/-- The original row action of the zero matrix is the zero linear map. -/
@[simp]
theorem rowAction_zero [Semiring R] :
    (0 : Matrix.LocallyFinite m n R).rowAction = 0 := by
  refine Finsupp.lhom_ext fun i r => ?_
  ext j
  simp only [rowAction_single, Finsupp.smul_apply, row_apply, zero_apply,
    smul_zero, LinearMap.zero_apply, Finsupp.zero_apply]

/-- Pointwise matrix addition gives addition of the original row actions. -/
theorem rowAction_add [Semiring R] (A B : Matrix.LocallyFinite m n R) :
    (A + B).rowAction = A.rowAction + B.rowAction := by
  refine Finsupp.lhom_ext fun i r => ?_
  ext j
  simp only [LinearMap.add_apply, rowAction_single, Finsupp.smul_apply,
    Finsupp.add_apply, row_apply, add_apply, smul_eq_mul, mul_add]

/-- Original rectangular products distribute over the second factor. -/
theorem comp_add [Semiring R] (A : Matrix.LocallyFinite m n R)
    (B C : Matrix.LocallyFinite n p R) : A.comp (B + C) = A.comp B + A.comp C := by
  apply rowAction_injective
  simp only [rowAction_comp, rowAction_add, LinearMap.add_comp]

/-- Original rectangular products distribute over the first factor. -/
theorem add_comp [Semiring R] (A B : Matrix.LocallyFinite m n R)
    (C : Matrix.LocallyFinite n p R) : (A + B).comp C = A.comp C + B.comp C := by
  apply rowAction_injective
  simp only [rowAction_comp, rowAction_add, LinearMap.comp_add]

/-- Multiplication by the original zero matrix on the right vanishes. -/
@[simp]
theorem comp_zero [Semiring R] (A : Matrix.LocallyFinite m n R) :
    A.comp (0 : Matrix.LocallyFinite n p R) = 0 := by
  apply rowAction_injective
  simp only [rowAction_comp, rowAction_zero, LinearMap.zero_comp]

/-- Multiplication by the original zero matrix on the left vanishes. -/
@[simp]
theorem zero_comp [Semiring R] (A : Matrix.LocallyFinite n p R) :
    (0 : Matrix.LocallyFinite m n R).comp A = 0 := by
  apply rowAction_injective
  simp only [rowAction_comp, rowAction_zero, LinearMap.comp_zero]

/-- The diagonal action multiplies each original coordinate on the right. -/
theorem rowAction_diagonal_apply [Semiring R] (d : n → R) (x : n →₀ R) (j : n) :
    (diagonal d).rowAction x j = x j * d j := by
  classical
  calc
    (diagonal d).rowAction x j = x j * diagonal d j j := by
      rw [rowAction_apply]
      refine Finset.sum_eq_single j ?_ ?_
      · intro k _ hk
        simp only [diagonal_apply, ite_eq_right hk, mul_zero]
      · intro hj
        rw [Finsupp.notMem_support_iff.mp hj, zero_mul]
    _ = x j * d j := by simp [diagonal_apply]

/-- Left diagonal multiplication scales the original row coefficient on the left. -/
theorem diagonal_comp_apply [Semiring R] (d : m → R)
    (A : Matrix.LocallyFinite m n R) (i : m) (j : n) :
    (diagonal d).comp A i j = d i * A i j := by
  change A.rowAction ((diagonal d).row i) j = _
  rw [row_diagonal, rowAction_single, Finsupp.smul_apply, row_apply, smul_eq_mul]

/-- Right diagonal multiplication scales the original column coefficient on the right. -/
theorem comp_diagonal_apply [Semiring R] (A : Matrix.LocallyFinite m n R)
    (d : n → R) (i : m) (j : n) :
    A.comp (diagonal d) i j = A i j * d j :=
  rowAction_diagonal_apply d (A.row i) j

instance [Zero R] [One R] : One (Matrix.LocallyFinite n n R) :=
  ⟨diagonal fun _ => 1⟩

/-- The original identity matrix has one exactly on the diagonal. -/
theorem one_apply [Zero R] [One R] (i j : n) :
    (1 : Matrix.LocallyFinite n n R) i j = if i = j then 1 else 0 :=
  diagonal_apply _ i j

/-- The original identity acts as the identity on finite row vectors. -/
@[simp]
theorem rowAction_one [Semiring R] :
    (1 : Matrix.LocallyFinite n n R).rowAction = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext j
  exact (rowAction_diagonal_apply (fun _ => 1) x j).trans (mul_one _)

/-- The original identity matrix is a left unit for every rectangular product. -/
@[simp]
theorem one_comp [Semiring R] (A : Matrix.LocallyFinite m n R) :
    (1 : Matrix.LocallyFinite m m R).comp A = A := by
  apply rowAction_injective
  simp only [rowAction_comp, rowAction_one, LinearMap.comp_id]

/-- The original identity matrix is a right unit for every rectangular product. -/
@[simp]
theorem comp_one [Semiring R] (A : Matrix.LocallyFinite m n R) :
    A.comp (1 : Matrix.LocallyFinite n n R) = A := by
  apply rowAction_injective
  simp only [rowAction_comp, rowAction_one, LinearMap.id_comp]

instance [Zero R] [NatCast R] : NatCast (Matrix.LocallyFinite n n R) :=
  ⟨fun k => diagonal fun _ => k⟩

instance [Zero R] [IntCast R] : IntCast (Matrix.LocallyFinite n n R) :=
  ⟨fun k => diagonal fun _ => k⟩

instance [AddCommMonoidWithOne R] : AddCommMonoidWithOne (Matrix.LocallyFinite n n R) := by
  classical
  exact toMatrix_injective.addCommMonoidWithOne toMatrix rfl rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)

instance [AddCommGroupWithOne R] : AddCommGroupWithOne (Matrix.LocallyFinite n n R) := by
  classical
  exact toMatrix_injective.addCommGroupWithOne toMatrix rfl rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => by ext i j; exact sub_apply _ _ i j)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)

instance [Semiring R] : Mul (Matrix.LocallyFinite n n R) := ⟨comp⟩

/-- Square-ring multiplication is the same original rectangular product. -/
theorem mul_eq_comp [Semiring R] (A B : Matrix.LocallyFinite n n R) : A * B = A.comp B := rfl

instance [Semiring R] : Semiring (Matrix.LocallyFinite n n R) :=
  { (inferInstance : AddCommMonoidWithOne (Matrix.LocallyFinite n n R)) with
    mul := comp
    mul_zero := comp_zero
    zero_mul := zero_comp
    left_distrib := comp_add
    right_distrib := add_comp
    mul_assoc := comp_assoc
    one_mul := one_comp
    mul_one := comp_one }

instance [Ring R] : Ring (Matrix.LocallyFinite n n R) :=
  { (inferInstance : Semiring (Matrix.LocallyFinite n n R)),
    (inferInstance : AddCommGroupWithOne (Matrix.LocallyFinite n n R)) with }

/-- The original ordered multiplication formula remains the square-ring formula. -/
theorem mul_apply [Semiring R] (A B : Matrix.LocallyFinite n n R) (i j : n) :
    (A * B) i j = ∑ k ∈ (A.row i).support, A i k * B k j := comp_apply A B i j

/-- The Finsupp form of the original product does not introduce an artificial support bound. -/
theorem comp_apply_sum [Semiring R] (A : Matrix.LocallyFinite m n R)
    (B : Matrix.LocallyFinite n p R) (i : m) (j : p) :
    A.comp B i j = (A.row i).sum (fun k r => r * B k j) := comp_apply A B i j

/-- An entrywise coefficient map takes the exact original row to its actual mapped Finsupp. -/
@[simp]
theorem row_map [Zero R] [Zero S] (f : ZeroHom R S)
    (A : Matrix.LocallyFinite m n R) (i : m) :
    (map f A).row i = Finsupp.mapRange f f.map_zero (A.row i) := by
  ext j
  rfl

/-- The entrywise image of an actual rectangular product is the product of the actual images. -/
theorem map_comp_product [Semiring R] [Semiring S] (f : R →+* S)
    (A : Matrix.LocallyFinite m n R) (B : Matrix.LocallyFinite n p R) :
    (map ⟨f, f.map_zero⟩ A).comp (map ⟨f, f.map_zero⟩ B) =
      map ⟨f, f.map_zero⟩ (A.comp B) := by
  ext i j
  rw [comp_apply_sum, row_map, Finsupp.sum_mapRange_index (fun _ => zero_mul _)]
  change (A.row i).sum (fun k r => f r * f (B k j)) = f (A.comp B i j)
  rw [comp_apply_sum, Finsupp.sum, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun k _ => (f.map_mul _ _).symm

/-- The actual entrywise map is a unital homomorphism of the original matrix rings. -/
def mapRingHom [Semiring R] [Semiring S] (f : R →+* S) :
    Matrix.LocallyFinite n n R →+* Matrix.LocallyFinite n n S where
  toFun := map ⟨f, f.map_zero⟩
  map_zero' := by
    ext i j
    change f 0 = 0
    exact f.map_zero
  map_one' := by
    classical
    ext i j
    change f ((1 : Matrix.LocallyFinite n n R) i j) = (1 : Matrix.LocallyFinite n n S) i j
    by_cases h : i = j <;> simp [one_apply, h]
  map_add' A B := by
    ext i j
    change f (A i j + B i j) = f (A i j) + f (B i j)
    exact f.map_add _ _
  map_mul' A B := (map_comp_product f A B).symm

/-- The matrix-ring homomorphism acts on the original coefficient. -/
@[simp]
theorem mapRingHom_apply [Semiring R] [Semiring S] (f : R →+* S)
    (A : Matrix.LocallyFinite n n R) (i j : n) :
    mapRingHom f A i j = f (A i j) := rfl

/-- Identity of coefficient rings gives the actual identity matrix-ring homomorphism. -/
@[simp]
theorem mapRingHom_id [Semiring R] :
    mapRingHom (n := n) (RingHom.id R) = RingHom.id (Matrix.LocallyFinite n n R) := by
  ext A i j
  rfl

/-- Coefficient composition gives strict composition of the original matrix-ring maps. -/
theorem mapRingHom_comp [Semiring R] [Semiring S] {T : Type*} [Semiring T]
    (g : S →+* T) (f : R →+* S) :
    mapRingHom (n := n) (g.comp f) = (mapRingHom g).comp (mapRingHom f) := by
  ext A i j
  rfl

/-- With finite inner index, the original product is the ordinary finite matrix product. -/
theorem ofMatrix_comp [Semiring R] [Finite m] [Fintype n] [Finite p]
    (A : Matrix m n R) (B : Matrix n p R) :
    (ofMatrix A).comp (ofMatrix B) = ofMatrix (A * B) := by
  ext i j
  rw [comp_apply_sum, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  rfl

/-- Finite-index inclusion is an equivalence of the original coefficient matrix rings. -/
def ofMatrixRingEquiv [Semiring R] [Fintype n] :
    Matrix n n R ≃+* Matrix.LocallyFinite n n R where
  toFun := ofMatrix
  invFun := toMatrix
  left_inv _ := rfl
  right_inv := ofMatrix_toMatrix
  map_add' _ _ := rfl
  map_mul' A B := (ofMatrix_comp A B).symm

end Matrix.LocallyFinite

end
