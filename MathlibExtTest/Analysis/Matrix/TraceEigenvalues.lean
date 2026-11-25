/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Matrix.TraceEigenvalues

open MetaMathlibExt Matrix

-- The overlap matrix of a basis with itself is doubly stochastic.
example (u : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    (Matrix.of fun i j => inner ℝ (u j) (u i) ^ 2) ∈ doublyStochastic ℝ (Fin 3) :=
  overlap_mem_doublyStochastic u u

-- Birkhoff's bound for the doubly stochastic matrix with all entries `1 / 2` on two indices.
example (c : Fin 2 → Fin 2 → ℝ) : ∃ σ : Equiv.Perm (Fin 2), ∑ i, c i (σ i) ≤
    ∑ i, ∑ j, c i j * (Matrix.of fun _ _ => (1 / 2 : ℝ)) i j := by
  refine exists_perm_sum_le_of_mem_doublyStochastic ?_ c
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun _ _ => by norm_num, fun _ => ?_, fun _ => ?_⟩ <;> norm_num [Fin.sum_univ_two]

-- von Neumann's trace inequality, both forms, for symmetric `3 × 3` matrices.
example {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∃ σ : Equiv.Perm (Fin 3), ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) ≤ (A * B).trace) ∧
      ∃ τ : Equiv.Perm (Fin 3), (A * B).trace ≤ ∑ i, hA.eigenvalues i * hB.eigenvalues (τ i) :=
  ⟨exists_perm_sum_mul_eigenvalues_le_trace_mul hA hB,
    exists_perm_trace_mul_le_sum_mul_eigenvalues hA hB⟩

-- von Neumann's trace inequality, sorted forms: `∑ α↓ β↑ ≤ tr (A B) ≤ ∑ α↓ β↓`.
example {A B : Matrix (Fin 3) (Fin 3) ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ k, hA.eigenvalues₀ k * hB.eigenvalues₀ (Fin.rev k) ≤ (A * B).trace ∧
      (A * B).trace ≤ ∑ k, hA.eigenvalues₀ k * hB.eigenvalues₀ k :=
  ⟨sum_eigenvalues₀_mul_rev_le_trace_mul hA hB, trace_mul_le_sum_eigenvalues₀_mul hA hB⟩

-- With `B = A` the upper form reads `tr (A²) ≤ ∑ λₖ²` (an equality, so the bound is sharp).
example {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.IsHermitian) :
    (A * A).trace ≤ ∑ k, hA.eigenvalues₀ k ^ 2 := by
  simpa [sq] using trace_mul_le_sum_eigenvalues₀_mul hA hA

#print axioms exists_perm_sum_mul_eigenvalues_le_trace_mul
#print axioms trace_mul_le_sum_eigenvalues₀_mul
#print axioms sum_eigenvalues₀_mul_rev_le_trace_mul
