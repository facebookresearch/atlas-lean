/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rouché–Capelli theorem

This file proves that a linear system over a field is solvable exactly when its coefficient matrix
and augmented matrix have equal rank.
-/

namespace MetaMathlibExt

open scoped Matrix

private theorem roucheCapelli_mulVec_mem_span_cols {m n K : Type*} [Fintype n] [Field K]
    (A : Matrix m n K) (x : n → K) :
    A *ᵥ x ∈ Submodule.span K (Set.range A.col) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨x, ?_⟩
  simp only [Matrix.mulVec_eq_sum, Matrix.col, IsCentralScalar.op_smul_eq_smul]

private theorem roucheCapelli_solvable_iff_mem_span_cols {m n K : Type*} [Fintype n]
    [Field K] (A : Matrix m n K) (b : m → K) :
    (∃ x : n → K, A *ᵥ x = b) ↔ b ∈ Submodule.span K (Set.range A.col) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact roucheCapelli_mulVec_mem_span_cols A x
  · intro hb
    rw [Submodule.mem_span_range_iff_exists_fun] at hb
    obtain ⟨x, hx⟩ := hb
    refine ⟨x, ?_⟩
    simpa only [Matrix.mulVec_eq_sum, Matrix.col, IsCentralScalar.op_smul_eq_smul] using hx

private theorem roucheCapelli_range_augmented_cols {m n K : Type*}
    (A : Matrix m n K) (b : m → K) :
    Set.range
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K).col =
      insert b (Set.range A.col) := by
  have hcol :
      (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K).col =
        Sum.elim A.col (fun _ : Fin 1 => b) := by
    funext j i
    cases j <;> rfl
  rw [hcol, Set.Sum.elim_range, Set.range_const, Set.union_singleton]

private theorem roucheCapelli_span_cols_le_augmented {m n K : Type*} [Field K]
    (A : Matrix m n K) (b : m → K) :
    Submodule.span K (Set.range A.col) ≤
      Submodule.span K
        (Set.range
          (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
            Matrix m (n ⊕ Fin 1) K).col) := by
  rw [roucheCapelli_range_augmented_cols A b]
  exact Submodule.span_mono (Set.subset_insert b (Set.range A.col))

private theorem roucheCapelli_span_augmented_eq_of_mem {m n K : Type*} [Field K]
    (A : Matrix m n K) (b : m → K) (hb : b ∈ Submodule.span K (Set.range A.col)) :
    Submodule.span K
        (Set.range
          (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
            Matrix m (n ⊕ Fin 1) K).col) =
      Submodule.span K (Set.range A.col) := by
  rw [roucheCapelli_range_augmented_cols A b]
  exact Submodule.span_insert_eq_span hb

private theorem roucheCapelli_span_cols_eq_of_rank_eq {m n K : Type*} [Fintype n]
    [Field K] (A : Matrix m n K) (b : m → K)
    (hrank :
      A.rank =
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K).rank) :
    Submodule.span K (Set.range A.col) =
      Submodule.span K
        (Set.range
          (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
            Matrix m (n ⊕ Fin 1) K).col) := by
  let :
      FiniteDimensional K
        (Submodule.span K
          (Set.range
            (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
              Matrix m (n ⊕ Fin 1) K).col)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  apply Submodule.eq_of_le_of_finrank_eq (roucheCapelli_span_cols_le_augmented A b)
  rw [← Matrix.rank_eq_finrank_span_cols A,
    ← Matrix.rank_eq_finrank_span_cols
      (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
        Matrix m (n ⊕ Fin 1) K)]
  exact hrank

@[expose]
public section

/-- **Rouché–Capelli theorem.** Let $K$ be a field, let $m$ be a set and $n$ a finite set, let $A$
be an $m \times n$ matrix over $K$, and let $b \in K^m$. Then the linear system $Ax = b$ has a
solution $x \in K^n$ if and only if the rank of $A$ equals the rank of the augmented matrix
$(A \mid b)$, whose columns are the columns of $A$ followed by the single column $b$.

Proves `Wanted` entry `rouche_capelli` (statement `rouche-capelli-s1`).

Proof: Following the column-space argument in [Wikipedia, *Rouché–Capelli theorem*,
"Proof"](https://en.wikipedia.org/wiki/Rouch%C3%A9%E2%80%93Capelli_theorem#Proof), solvability is
membership of $b$ in the column span, which we compare before and after adjoining $b$.

Source: https://en.wikipedia.org/wiki/Rouch%C3%A9%E2%80%93Capelli_theorem.
-/
theorem rouche_capelli {m n : Type*} [Fintype n] {K : Type*} [Field K]
    (A : Matrix m n K) (b : m → K) :
    (∃ x : n → K, A *ᵥ x = b) ↔
      A.rank =
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K).rank := by
  rw [roucheCapelli_solvable_iff_mem_span_cols A b]
  constructor
  · intro hb
    rw [Matrix.rank_eq_finrank_span_cols A,
      Matrix.rank_eq_finrank_span_cols
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K),
      roucheCapelli_span_augmented_eq_of_mem A b hb]
  · intro hrank
    rw [roucheCapelli_span_cols_eq_of_rank_eq A b hrank,
      roucheCapelli_range_augmented_cols A b]
    exact Submodule.subset_span (Set.mem_insert b _)

end

end MetaMathlibExt
