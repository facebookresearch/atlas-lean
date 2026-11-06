/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Real symmetric Jordan matrices and orthogonal-conjugation recognition. -/
module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual 24-dimensional symmetric-matrix constituent. -/
def Sym24 : Submodule ℝ (Matrix (Fin 24) (Fin 24) ℝ) where
  carrier := {A | A.transpose = A}
  zero_mem' := by simp
  add_mem' := by
    intro A B hA hB
    change A.transpose = A at hA
    change B.transpose = B at hB
    change (A + B).transpose = A + B
    rw [Matrix.transpose_add, hA, hB]
  smul_mem' := by
    intro c A hA
    change A.transpose = A at hA
    change (c • A).transpose = c • A
    rw [Matrix.transpose_smul, hA]

@[simp] theorem mem_Sym24 (A : Matrix (Fin 24) (Fin 24) ℝ) :
    A ∈ Sym24 ↔ A.transpose = A := Iff.rfl

/-- The unnormalized real Jordan product on the symmetric constituent. -/
def sym24Jordan (A B : Sym24) : Sym24 :=
  ⟨A.val * B.val + B.val * A.val, by
    change (A.val * B.val + B.val * A.val).transpose = A.val * B.val + B.val * A.val
    have hA : A.val.transpose = A.val := A.property
    have hB : B.val.transpose = B.val := B.property
    rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, hA, hB, add_comm]⟩

/-- The identity matrix in the symmetric constituent. -/
def sym24One : Sym24 := ⟨1, by simp⟩

/-- A symmetric idempotent's diagonal is the square norm of its corresponding column. -/
theorem symmetric_idempotent_diagonal (P : Matrix (Fin 24) (Fin 24) ℝ)
    (hSym : P.transpose = P) (hId : P * P = P) (j : Fin 24) :
    ∑ i, P i j ^ 2 = P j j := by
  have hj := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A j j) hId
  have hs (i : Fin 24) : P j i = P i j := by
    exact congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A i j) hSym
  simpa only [Matrix.mul_apply, hs, pow_two] using hj

/-- A symmetric idempotent with zero trace is zero. -/
theorem symmetric_idempotent_eq_zero_of_trace_zero (P : Matrix (Fin 24) (Fin 24) ℝ)
    (hSym : P.transpose = P) (hId : P * P = P) (hTr : Matrix.trace P = 0) : P = 0 := by
  have hnon (j : Fin 24) : 0 ≤ P j j := by
    rw [← symmetric_idempotent_diagonal P hSym hId j]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : ∀ j : Fin 24, P j j = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnon j)).mp hTr j (Finset.mem_univ j)
  ext i j
  have hh := symmetric_idempotent_diagonal P hSym hId j
  rw [hd] at hh
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (P k j))).mp hh i
    (Finset.mem_univ i)
  exact (sq_eq_zero_iff).mp hz

/-- Trace one supplies a column of strictly positive square norm. -/
theorem symmetric_idempotent_trace_one_positive_diagonal
    (P : Matrix (Fin 24) (Fin 24) ℝ) (hTr : Matrix.trace P = 1) :
    ∃ j : Fin 24, 0 < P j j := by
  by_contra he
  push Not at he
  have hs : (∑ j, P j j) ≤ 0 := Finset.sum_nonpos fun j _ => he j
  change (∑ j, P j j) = 1 at hTr
  linarith

/-- A normalized nonzero projector column is a unit fixed vector. -/
theorem symmetric_idempotent_trace_one_unit_eigenvector
    (P : Matrix (Fin 24) (Fin 24) ℝ) (hSym : P.transpose = P)
    (hId : P * P = P) (hTr : Matrix.trace P = 1) :
    ∃ v : Fin 24 → ℝ, (∑ i, v i ^ 2 = 1) ∧ P *ᵥ v = v := by
  obtain ⟨j, hj⟩ := symmetric_idempotent_trace_one_positive_diagonal P hTr
  let a : ℝ := Real.sqrt (P j j)
  have ha2 : a ^ 2 = P j j := Real.sq_sqrt (le_of_lt hj)
  let v : Fin 24 → ℝ := fun i => P i j / a
  refine ⟨v, ?_, ?_⟩
  · change (∑ i, (P i j / a) ^ 2) = 1
    simp only [div_pow, ← Finset.sum_div]
    rw [symmetric_idempotent_diagonal P hSym hId j, ha2, div_self (ne_of_gt hj)]
  · ext i
    change (∑ k, P i k * (P k j / a)) = P i j / a
    have hh := congrArg (fun A : Matrix (Fin 24) (Fin 24) ℝ => A i j) hId
    calc
      _ = ∑ k, (P i k * P k j) / a :=
        Finset.sum_congr rfl (fun k _ => (mul_div_assoc _ _ _).symm)
      _ = (∑ k, P i k * P k j) / a := (Finset.sum_div _ _ _).symm
      _ = P i j / a := congrArg (fun r : ℝ => r / a) hh

/-- Every trace-one symmetric idempotent is a rank-one unit-vector projector. -/
theorem symmetric_idempotent_trace_one_eq_vecMulVec
    (P : Matrix (Fin 24) (Fin 24) ℝ) (hSym : P.transpose = P)
    (hId : P * P = P) (hTr : Matrix.trace P = 1) :
    ∃ v : Fin 24 → ℝ, (∑ i, v i ^ 2 = 1) ∧ P = Matrix.vecMulVec v v := by
  obtain ⟨v, hv, hPv⟩ := symmetric_idempotent_trace_one_unit_eigenvector P hSym hId hTr
  have hd : v ⬝ᵥ v = 1 := by simpa only [dotProduct, pow_two] using hv
  let W := Matrix.vecMulVec v v
  have hW : W.transpose = W := Matrix.transpose_vecMulVec v v
  have hWW : W * W = W := by
    change Matrix.vecMulVec v v * Matrix.vecMulVec v v = Matrix.vecMulVec v v
    rw [Matrix.vecMulVec_mul_vecMulVec, hd, one_smul]
  have hPW : P * W = W := by
    change P * Matrix.vecMulVec v v = Matrix.vecMulVec v v
    rw [Matrix.mul_vecMulVec, hPv]
  have hWP : W * P = W := by
    have hh := congrArg Matrix.transpose hPW
    rwa [Matrix.transpose_mul, hW, hSym] at hh
  have hQSym : (P - W).transpose = P - W := by
    rw [Matrix.transpose_sub, hSym, hW]
  have hQId : (P - W) * (P - W) = P - W := by
    rw [sub_mul, mul_sub, mul_sub, hId, hPW, hWP, hWW]
    abel
  have hQTr : Matrix.trace (P - W) = 0 := by
    rw [Matrix.trace_sub, hTr]
    change 1 - Matrix.trace (Matrix.vecMulVec v v) = 0
    rw [Matrix.trace_vecMulVec, hd, sub_self]
  have hQ := symmetric_idempotent_eq_zero_of_trace_zero (P - W) hQSym hQId hQTr
  exact ⟨v, hv, sub_eq_zero.mp hQ⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
