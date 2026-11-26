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
# Rectangular continuous operator matrices on product spaces

Let R be a semiring and E,F additive groups with topologies and R-module structures. For
arbitrary row type m and finite column type n, A_ij:E→F continuous linear and continuous
addition on F, let T_A:E^n→F^m be (T_A v)_i=∑jA_ij(v_j), on the product topology of PiLp 2.
For any row and column index types, a continuous linear T:E^n→F^m has recovered coefficients
A_ij(x)=proj_i(T(single_j x)). Recovery needs no continuous-addition or finite-index premise.
When columns are finite and addition on F continuous, action and recovery are inverse. For
arbitrary rows the topology is the product topology, not an infinite square-summable norm.
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

/-- **Finite-column continuous matrix action.**

Let R be a semiring and E,F additive groups with topologies and R-module structures. For
arbitrary row type m and finite column type n, A_ij:E→F continuous linear and continuous
addition on F, let T_A:E^n→F^m be (T_A v)_i=∑jA_ij(v_j), on the product topology of PiLp 2.
The map toPiLpContinuousLinearMap A is T_A.
-/
def toPiLpContinuousLinearMap [Fintype n] [ContinuousAdd F]
    (M : Matrix m n (E →L[R] F)) :
    PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F) :=
  (PiLp.continuousLinearEquiv 2 R (fun _ : m => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : m =>
      ∑ j : n, (M i j).comp
        ((ContinuousLinearMap.proj j : (n → E) →L[R] E).comp
          (PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).toContinuousLinearMap))

/-- **Row value of a continuous column action.**

Let R be a semiring and E,F additive groups with topologies and R-module structures. For
arbitrary row type m and finite column type n, A_ij:E→F continuous linear and continuous
addition on F, let T_A:E^n→F^m be (T_A v)_i=∑jA_ij(v_j), on the product topology of PiLp 2.
For v∈E^n and i∈m, toPiLpContinuousLinearMap A v i=∑jA_ij(v_j).
-/
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

/-- **Coordinate recovery of a continuous rectangular operator.**

Let R be a semiring,E,F topological R-module additive groups and m,n arbitrary index types.
For any row and column index types, a continuous linear T:E^n→F^m has recovered coefficients
A_ij(x)=proj_i(T(single_j x)). Recovery needs no continuous-addition or finite-index premise.
The map toPiLpMatrix T gives these coefficients.
-/
def toPiLpMatrix [DecidableEq n]
    (T : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F)) :
    Matrix m n (E →L[R] F) :=
  Matrix.of fun i j =>
    ((ContinuousLinearMap.proj i : (m → F) →L[R] F).comp
      (PiLp.continuousLinearEquiv 2 R (fun _ : m => F)).toContinuousLinearMap).comp
      (T.comp
        ((PiLp.continuousLinearEquiv 2 R (fun _ : n => E)).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.single R (fun _ : n => E) j)))

/-- **Value of a recovered operator coefficient.**

Let R be a semiring,E,F topological R-module additive groups,m,n arbitrary,T:E^n→F^m
continuous linear,i∈m,j∈n,x∈E. Then toPiLpMatrix T i j x=T(single_j x)_i.
-/
@[simp]
theorem toPiLpMatrix_apply [DecidableEq n]
    (T : PiLp 2 (fun _ : n => E) →L[R] PiLp 2 (fun _ : m => F))
    (i : m) (j : n) (x : E) :
    toPiLpMatrix T i j x = T (PiLp.single 2 j x) i :=
  rfl

/-- **Recovering the finite-column action gives its coefficients.**

Let R be a semiring and E,F additive groups with topologies and R-module structures. For
arbitrary row type m and finite column type n, A_ij:E→F continuous linear and continuous
addition on F, let T_A:E^n→F^m be (T_A v)_i=∑jA_ij(v_j), on the product topology of PiLp 2.
The equality toPiLpMatrix(T_A)=A holds.
-/
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

/-- **Reconstructing a continuous map from finitely many columns.**

Let R be a semiring and E,F additive groups with topologies and R-module structures. For
arbitrary row type m and finite column type n, A_ij:E→F continuous linear and continuous
addition on F, let T_A:E^n→F^m be (T_A v)_i=∑jA_ij(v_j), on the product topology of PiLp 2.
For any continuous linear T:E^n→F^m, the column action of toPiLpMatrix T equals T.
-/
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

/-- **Equivalence of rectangular operator matrices and continuous product maps.**

Let R be a semiring and E,F additive groups with topologies and R-module structures. For
arbitrary row type m and finite column type n, A_ij:E→F continuous linear and continuous
addition on F, let T_A:E^n→F^m be (T_A v)_i=∑jA_ij(v_j), on the product topology of PiLp 2.
The equivalence piLpContinuousLinearMapEquiv identifies Matrix m n(E→L[R]F) with E^n→L[R]F^m
by action and recovery.
-/
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

/-- **Composition of rectangular continuous column actions.**

Let R be a semiring,E,F,G topological module additive groups, m arbitrary and n,k finite.
Assume addition continuous on F,G. For A_ij:F→LG and B_jl:E→LF, the matrix C_il=∑j A_ij∘B_jl
satisfies T_C=T_A∘T_B.
-/
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

/-- **Multiplication of square continuous operator matrices.**

Let R be a semiring,E a topological module additive group with continuous addition and n
finite. For matrices A,B of continuous linear endomorphisms, T_(AB)=T_A∘T_B.
-/
theorem toPiLpContinuousLinearMap_mul [Fintype n] [ContinuousAdd E]
    (M N : Matrix n n (E →L[R] E)) :
    toPiLpContinuousLinearMap (M * N) =
      toPiLpContinuousLinearMap M * toPiLpContinuousLinearMap N := by
  have hMul : (of fun i j : n => ∑ l : n, (M i l).comp (N l j)) = M * N := by
    ext i j
    simp only [of_apply, Matrix.mul_apply, ContinuousLinearMap.mul_def]
  rw [← hMul, ContinuousLinearMap.mul_def]
  exact toPiLpContinuousLinearMap_comp M N

/-- **Identity matrix acts as the identity on a finite product.**

Let R be a semiring,E a topological R-module additive group with continuous addition and n
finite. The identity operator matrix acts as id on PiLp 2(E^n), including empty n.
-/
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
