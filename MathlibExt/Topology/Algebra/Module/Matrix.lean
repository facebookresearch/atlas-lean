/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Data.Matrix.Mul

/-!
# Rectangular matrices of continuous linear maps on PiLp

An operator-valued matrix acts by finite column summation on the existing
product-topological `PiLp 2` carrier. The row index may be arbitrary.
Coordinate recovery uses the existing single-coordinate injections and
projections; it requires neither finite indices nor continuity of addition.

The action and recovery are inverse when the column index is finite and
addition is continuous in the target. They give a bare equivalence, without
a commutative-scalar, norm, completeness or separation hypothesis.
For arbitrary row indices, the topology here is still the product topology,
not the topology of an infinite square-summable space.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe uR uM uN uE uF uK uG

variable {R : Type uR} [Semiring R]
variable {m : Type uM} {n : Type uN}
variable {E : Type uE} {F : Type uF}
variable [AddCommGroup E] [TopologicalSpace E] [Module R E]
variable [AddCommGroup F] [TopologicalSpace F] [Module R F]

namespace Matrix

/-- A rectangular matrix of continuous linear maps acts by finite column
summation on the existing PiLp product topology. Rows need not be finite. -/
def toPiLpContinuousLinearMap [Fintype n] [ContinuousAdd F]
    (M : Matrix m n (E →L[R] F)) :
    PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F) :=
  (PiLp.continuousLinearEquiv 2 R (fun _ : m => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : m =>
      ∑ j : n, (M i j).comp
        ((ContinuousLinearMap.proj j : (n → E) →L[R] E).comp
          (PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).toContinuousLinearMap))

/-- Evaluation of the column action at a target row. -/
@[simp]
theorem toPiLpContinuousLinearMap_apply [Fintype n] [ContinuousAdd F]
    (M : Matrix m n (E →L[R] F)) (v : PiLp 2 (fun _ : n => E)) (i : m) :
    toPiLpContinuousLinearMap M v i = ∑ j : n, M i j (v j) := by
  change (∑ j : n, (M i j).comp
    ((ContinuousLinearMap.proj j : (n → E) →L[R] E).comp
      (PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).toContinuousLinearMap)) v = _
  simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, ContinuousLinearEquiv.coe_coe,
    PiLp.continuousLinearEquiv_apply]

end Matrix

namespace ContinuousLinearMap

/-- Recover a rectangular operator matrix by injecting a source coordinate,
applying the map and projecting a target coordinate. No finiteness or
continuity of addition is required. -/
def toPiLpMatrix [DecidableEq n]
    (T : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F)) :
    Matrix m n (E →L[R] F) :=
  Matrix.of fun i j =>
    ((ContinuousLinearMap.proj i : (m → F) →L[R] F).comp
      (PiLp.continuousLinearEquiv 2 R (fun _ : m => F)).toContinuousLinearMap).comp
      (T.comp
        ((PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single R (fun _ : n => E) j)))

/-- Evaluation of a recovered coefficient on a source vector. -/
@[simp]
theorem toPiLpMatrix_apply [DecidableEq n]
    (T : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F))
    (i : m) (j : n) (x : E) :
    toPiLpMatrix T i j x = T (PiLp.single 2 j x) i :=
  rfl

/-- Recovering the coefficients of the finite-column action returns the
original operator-valued matrix. -/
@[simp]
theorem toPiLpMatrix_toPiLpContinuousLinearMap [Fintype n] [DecidableEq n]
    [ContinuousAdd F] (M : Matrix m n (E →L[R] F)) :
    toPiLpMatrix (Matrix.toPiLpContinuousLinearMap M) = M := by
  apply Matrix.ext
  intro i j
  apply ContinuousLinearMap.ext
  intro x
  rw [toPiLpMatrix_apply, Matrix.toPiLpContinuousLinearMap_apply,
    Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro k _ hk
    rw [PiLp.single_eq_of_ne 2 hk, map_zero]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

end ContinuousLinearMap

namespace Matrix

/-- Finite source-coordinate reconstruction recovers the original map from
its operator-valued matrix. -/
@[simp]
theorem toPiLpContinuousLinearMap_toPiLpMatrix [Fintype n] [DecidableEq n]
    [ContinuousAdd F]
    (T : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F)) :
    toPiLpContinuousLinearMap (ContinuousLinearMap.toPiLpMatrix T) = T := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rw [toPiLpContinuousLinearMap_apply]
  let U : (n → E) →L[R] F :=
    ((ContinuousLinearMap.proj i : (m → F) →L[R] F).comp
      (PiLp.continuousLinearEquiv 2 R (fun _ : m => F)).toContinuousLinearMap).comp
      (T.comp
        (PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).symm.toContinuousLinearMap)
  change (∑ j : n,
    (U.comp (ContinuousLinearMap.single R (fun _ : n => E) j)) (v j)) =
      U (WithLp.ofLp v)
  exact ContinuousLinearMap.sum_comp_single R (fun _ : n => E) U (WithLp.ofLp v)

/-- Rectangular operator matrices and continuous linear maps on the actual
PiLp products are equivalent when source coordinates are finite. -/
def piLpContinuousLinearMapEquiv [Fintype n] [DecidableEq n] [ContinuousAdd F] :
    Matrix m n (E →L[R] F) ≃
      (PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F)) where
  toFun := toPiLpContinuousLinearMap
  invFun := ContinuousLinearMap.toPiLpMatrix
  left_inv := ContinuousLinearMap.toPiLpMatrix_toPiLpContinuousLinearMap
  right_inv := toPiLpContinuousLinearMap_toPiLpMatrix

section Composition

variable {k : Type uK}
variable {G : Type uG} [AddCommGroup G] [TopologicalSpace G] [Module R G]

/-- Rectangular composition acts in the same order as the corresponding
continuous linear maps: the right matrix acts first. -/
theorem toPiLpContinuousLinearMap_comp [Fintype n] [Fintype k]
    [ContinuousAdd F] [ContinuousAdd G]
    (M : Matrix m n (F →L[R] G)) (N : Matrix n k (E →L[R] F)) :
    toPiLpContinuousLinearMap (of fun i l => ∑ j : n, (M i j).comp (N j l)) =
      (toPiLpContinuousLinearMap M).comp (toPiLpContinuousLinearMap N) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change
    toPiLpContinuousLinearMap (of fun i l => ∑ j : n, (M i j).comp (N j l)) v i =
      toPiLpContinuousLinearMap M (toPiLpContinuousLinearMap N v) i
  simp only [toPiLpContinuousLinearMap_apply, of_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, map_sum]
  exact Finset.sum_comm

end Composition

section Square

open scoped Matrix

/-- The square operator-matrix action preserves actual ordered matrix
multiplication, where operator multiplication is composition. -/
theorem toPiLpContinuousLinearMap_mul [Fintype n] [ContinuousAdd E]
    (M N : Matrix n n (E →L[R] E)) :
    toPiLpContinuousLinearMap (M * N) =
      toPiLpContinuousLinearMap M * toPiLpContinuousLinearMap N := by
  have hMul : (of fun i j : n => ∑ l : n, (M i l).comp (N l j)) = M * N := by
    ext i j
    simp only [of_apply, Matrix.mul_apply, ContinuousLinearMap.mul_def]
  rw [← hMul, ContinuousLinearMap.mul_def]
  exact toPiLpContinuousLinearMap_comp M N

/-- The action of the identity matrix is the actual identity map, including
an empty index type. -/
theorem toPiLpContinuousLinearMap_one [Fintype n] [DecidableEq n] [ContinuousAdd E] :
    toPiLpContinuousLinearMap (1 : Matrix n n (E →L[R] E)) =
      (1 : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : n => E)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rw [toPiLpContinuousLinearMap_apply]
  change (∑ j : n, (1 : Matrix n n (E →L[R] E)) i j (v j)) = v i
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq]
    rfl
  · intro j _ hji
    rw [Matrix.one_apply_ne (Ne.symm hji)]
    rfl
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end Square

end Matrix

end
