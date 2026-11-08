/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Convex.Birkhoff

/-!
# The trace of a product of symmetric matrices and their eigenvalues

For real symmetric `A` and `B` with eigenvalues `α`, `β` and orthonormal eigenbases `u`, `v`
(Mathlib's `IsHermitian.eigenvalues` and `IsHermitian.eigenvectorBasis`):

* `trace_mul_eq_sum_eigenvalues`: `tr (A B) = ∑ᵢ ∑ⱼ αᵢ βⱼ ⟪vⱼ, uᵢ⟫²`;
* `overlap_mem_doublyStochastic`: the overlap matrix `⟪vⱼ, uᵢ⟫²` of two orthonormal bases is
  doubly stochastic;
* `exists_perm_sum_le_of_mem_doublyStochastic`: a linear functional of a doubly stochastic matrix
  is bounded below by its value at a permutation matrix (from Mathlib's Birkhoff theorem
  `exists_eq_sum_perm_of_mem_doublyStochastic`);
* `exists_perm_sum_mul_eigenvalues_le_trace_mul`, `exists_perm_trace_mul_le_sum_mul_eigenvalues`:
  **von Neumann's trace inequality** in pairing form. For some permutations `σ` and `τ`,
  `∑ᵢ αᵢ β_{σ i} ≤ tr (A B) ≤ ∑ᵢ αᵢ β_{τ i}`. The sorted forms `∑ α↓ β↑ ≤ tr (A B) ≤ ∑ α↓ β↓`
  follow by the rearrangement inequality; they are not stated here.

This is the spectral step in maximum-likelihood problems over constrained covariances, such as
Tipping and Bishop's principal-subspace theorem for probabilistic PCA.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open Matrix WithLp
open scoped RealInnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem trace_eq_sum_inner_toEuclideanLin (M : Matrix n n ℝ)
    (b : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) :
    M.trace = ∑ i, ⟪b i, toEuclideanLin M (b i)⟫ := by
  rw [← LinearMap.trace_eq_sum_inner, toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

/-- `⟪x, B x⟫ = ∑ⱼ βⱼ ⟪vⱼ, x⟫²` in an eigenbasis `v` of a symmetric `B`. -/
theorem inner_toEuclideanLin_self_eq_sum {B : Matrix n n ℝ} (hB : B.IsHermitian)
    (x : EuclideanSpace ℝ n) :
    ⟪x, toEuclideanLin B x⟫ = ∑ j, hB.eigenvalues j * ⟪hB.eigenvectorBasis j, x⟫ ^ 2 := by
  have hsym := (isSymmetric_toEuclideanLin_iff.mpr hB)
  rw [← (hB.eigenvectorBasis).sum_inner_mul_inner x (toEuclideanLin B x)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hv : toEuclideanLin B (hB.eigenvectorBasis j) =
      hB.eigenvalues j • hB.eigenvectorBasis j := by
    apply WithLp.ofLp_injective
    simpa using hB.mulVec_eigenvectorBasis j
  rw [← hsym, hv, inner_smul_left, real_inner_comm x]
  simp only [conj_trivial]
  ring

/-- `tr (A B) = ∑ᵢ ∑ⱼ αᵢ βⱼ ⟪uᵢ, vⱼ⟫²` for symmetric `A`, `B` with eigenbases `u`, `v`. -/
theorem trace_mul_eq_sum_eigenvalues {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    (A * B).trace = ∑ i, ∑ j, hA.eigenvalues i * hB.eigenvalues j *
      ⟪hB.eigenvectorBasis j, hA.eigenvectorBasis i⟫ ^ 2 := by
  rw [trace_eq_sum_inner_toEuclideanLin _ hA.eigenvectorBasis]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsym := (isSymmetric_toEuclideanLin_iff.mpr hA)
  have hu : toEuclideanLin A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    simpa using hA.mulVec_eigenvectorBasis i
  have hmul : toEuclideanLin (A * B) (hA.eigenvectorBasis i) =
      toEuclideanLin A (toEuclideanLin B (hA.eigenvectorBasis i)) := by
    apply WithLp.ofLp_injective
    simp [mulVec_mulVec]
  rw [hmul, ← hsym, hu, inner_smul_left, conj_trivial,
    inner_toEuclideanLin_self_eq_sum hB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The overlap matrix `⟪vⱼ, uᵢ⟫²` of two orthonormal bases is doubly stochastic. -/
theorem overlap_mem_doublyStochastic (u v : OrthonormalBasis n ℝ (EuclideanSpace ℝ n)) :
    (Matrix.of fun i j => ⟪v j, u i⟫ ^ 2) ∈ doublyStochastic ℝ n := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · simp only [of_apply]
    rw [v.sum_sq_inner_right, u.orthonormal.1 i, one_pow]
  · simp only [of_apply]
    rw [u.sum_sq_inner_left, v.orthonormal.1 j, one_pow]

/-- A linear functional of a doubly stochastic matrix is bounded below by its value at some
permutation matrix (Birkhoff's theorem). -/
theorem exists_perm_sum_le_of_mem_doublyStochastic {P : Matrix n n ℝ}
    (hP : P ∈ doublyStochastic ℝ n) (c : n → n → ℝ) :
    ∃ σ : Equiv.Perm n, ∑ i, c i (σ i) ≤ ∑ i, ∑ j, c i j * P i j := by
  obtain ⟨w, hw0, hw1, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hP
  obtain ⟨σ₀, -, hσ₀⟩ := Finset.exists_min_image Finset.univ (fun σ : Equiv.Perm n =>
    ∑ i, c i (σ i)) Finset.univ_nonempty
  refine ⟨σ₀, ?_⟩
  have hperm : ∀ σ : Equiv.Perm n, ∑ i, ∑ j, c i j * σ.permMatrix ℝ i j = ∑ i, c i (σ i) := by
    intro σ
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]
  have hexp : ∑ i, ∑ j, c i j * P i j = ∑ σ, w σ * ∑ i, c i (σ i) := by
    rw [← hwP]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, ← hperm]
    rw [Finset.sum_comm (γ := Equiv.Perm n)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm (γ := Equiv.Perm n)]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun σ _ => by ring
  rw [hexp]
  calc ∑ i, c i (σ₀ i) = ∑ σ, w σ * ∑ i, c i (σ₀ i) := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ ∑ σ, w σ * ∑ i, c i (σ i) :=
      Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hσ₀ σ (Finset.mem_univ _)) (hw0 σ)

/-- **A trace inequality for eigenvalues**: for symmetric `A` and `B` with eigenvalues `α`
and `β`, some pairing of the eigenvalues bounds `tr (A B)` from below: `∑ᵢ αᵢ β_{σ i} ≤ tr (A B)`
for some permutation `σ` (von Neumann's trace inequality, lower form). -/
theorem exists_perm_sum_mul_eigenvalues_le_trace_mul {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ∃ σ : Equiv.Perm n, ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) ≤ (A * B).trace := by
  obtain ⟨σ, hσ⟩ := exists_perm_sum_le_of_mem_doublyStochastic
    (overlap_mem_doublyStochastic hA.eigenvectorBasis hB.eigenvectorBasis)
    (fun i j => hA.eigenvalues i * hB.eigenvalues j)
  refine ⟨σ, hσ.trans_eq ?_⟩
  rw [trace_mul_eq_sum_eigenvalues hA hB]
  simp only [of_apply]

/-- **A trace inequality for eigenvalues**, upper form: `tr (A B) ≤ ∑ᵢ αᵢ β_{σ i}` for some
permutation `σ`. -/
theorem exists_perm_trace_mul_le_sum_mul_eigenvalues {A B : Matrix n n ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    ∃ σ : Equiv.Perm n, (A * B).trace ≤ ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) := by
  obtain ⟨σ, hσ⟩ := exists_perm_sum_le_of_mem_doublyStochastic
    (overlap_mem_doublyStochastic hA.eigenvectorBasis hB.eigenvectorBasis)
    (fun i j => -(hA.eigenvalues i * hB.eigenvalues j))
  refine ⟨σ, ?_⟩
  rw [trace_mul_eq_sum_eigenvalues hA hB]
  simp only [of_apply, neg_mul, Finset.sum_neg_distrib, neg_le_neg_iff] at hσ
  exact hσ

end MetaMathlibExt
