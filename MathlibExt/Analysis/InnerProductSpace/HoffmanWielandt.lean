/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Hoffman-Wielandt inequality for Hermitian matrices
-/

section

open scoped BigOperators

namespace MathlibExt.Analysis.InnerProductSpace.HoffmanWielandtWanted

/-- Two antitone real functions on `Fin n` monovary. -/
private lemma monovary_of_antitone_antitone {n : ℕ} {f g : Fin n → ℝ}
    (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  hf.monovary hg

/-- Rearrangement: permuting one side of a monovarying pair can only decrease the sum. -/
private lemma sum_mul_comp_perm_le {n : ℕ} {f g : Fin n → ℝ}
    (hfg : Monovary f g) (σ : Equiv.Perm (Fin n)) :
    ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
  Monovary.sum_mul_comp_perm_le_sum_mul hfg

/-- A permutation matrix picks out the permuted entry under summation. -/
private lemma sum_permMatrix_mul {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) (f : Fin n → ℝ) :
    ∑ j, (σ.permMatrix ℝ) i j * f j = f (σ i) := by
  simp [Equiv.Perm.permMatrix]

/-- Birkhoff consequence: for `S` doubly stochastic and `f g` monovarying,
`∑ i j, S i j * (f i * g j) ≤ ∑ i, f i * g i`. -/
private lemma sum_doublyStochastic_mul_le {n : ℕ} {f g : Fin n → ℝ}
    (hfg : Monovary f g) {S : Matrix (Fin n) (Fin n) ℝ}
    (hS : S ∈ doublyStochastic ℝ (Fin n)) :
    ∑ i, ∑ j, S i j * (f i * g j) ≤ ∑ i, f i * g i := by
  obtain ⟨w, hw_nonneg, hw_sum, hw_eq⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hS
  have hentry : ∀ i j, S i j = ∑ σ, w σ * (σ.permMatrix ℝ) i j := by
    intro i j
    have h := congrFun (congrFun hw_eq.symm i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
    exact h
  have hperm : ∀ (σ : Equiv.Perm (Fin n)) (i : Fin n),
      ∑ j, (w σ * (σ.permMatrix ℝ) i j) * (f i * g j) = w σ * (f i * g (σ i)) := by
    intro σ i
    have hrw : ∀ j, (w σ * (σ.permMatrix ℝ) i j) * (f i * g j)
        = w σ * ((σ.permMatrix ℝ) i j * (f i * g j)) := fun j => by ring
    simp_rw [hrw, ← Finset.mul_sum]
    congr 1
    exact sum_permMatrix_mul σ i (fun j => f i * g j)
  calc ∑ i, ∑ j, S i j * (f i * g j)
      = ∑ i, ∑ j, ∑ σ : Equiv.Perm (Fin n), (w σ * (σ.permMatrix ℝ) i j) * (f i * g j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hentry i j, Finset.sum_mul]
    _ = ∑ σ : Equiv.Perm (Fin n), ∑ i, ∑ j, (w σ * (σ.permMatrix ℝ) i j) * (f i * g j) := by
        trans ∑ i, ∑ σ : Equiv.Perm (Fin n), ∑ j,
          (w σ * (σ.permMatrix ℝ) i j) * (f i * g j)
        · apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        · rw [Finset.sum_comm]
    _ = ∑ σ : Equiv.Perm (Fin n), w σ * (∑ i, f i * g (σ i)) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact hperm σ i
    _ ≤ ∑ σ : Equiv.Perm (Fin n), w σ * (∑ i, f i * g i) := by
        apply Finset.sum_le_sum
        intro σ _
        apply mul_le_mul_of_nonneg_left (sum_mul_comp_perm_le hfg σ) (hw_nonneg σ)
    _ = ∑ i, f i * g i := by
        rw [← Finset.sum_mul, hw_sum, one_mul]


/-- The eigenvector equation for the goal's eigenvalue functions, in matrix form. -/
private lemma mulVec_eigenvectorBasis_aux {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) (j : Fin n) :
    Matrix.mulVec A ⇑(((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
      finrank_euclideanSpace_fin) j)
      = (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
        finrank_euclideanSpace_fin j)) •
        ⇑(((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
        finrank_euclideanSpace_fin) j) := by
  have h := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
    finrank_euclideanSpace_fin j
  have h2 := congrArg (fun x : EuclideanSpace ℂ (Fin n) => (x : Fin n → ℂ)) h
  simpa only [Matrix.toLpLin_apply, WithLp.ofLp_smul,
    RCLike.real_smul_eq_coe_smul (K := ℂ)] using h2

/-- Diagonalization with the goal's eigenvalue functions:
`star U * A * U = diagonal (ofReal ∘ λ)`. -/
private lemma star_mul_diagonal_aux {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      star U * A * U = Matrix.diagonal (fun a =>
        (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin a) : ℂ)) := by
  set ba := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis
    finrank_euclideanSpace_fin with hba
  set U : Matrix (Fin n) (Fin n) ℂ :=
    ((EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix ba.toBasis) with hU
  have hUmem : U ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary ba
  refine ⟨U, hUmem, ?_⟩
  have hcol : ∀ k j, U k j = ⇑(ba j) k := fun k j => rfl
  have hAU : A * U = U * Matrix.diagonal (fun a =>
      (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
        finrank_euclideanSpace_fin a) : ℂ)) := by
    ext i j
    simp only [Matrix.mul_apply, hcol]
    have h := mulVec_eigenvectorBasis_aux hA j
    have h2 := congrFun h i
    simpa [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, mul_comm] using h2
  have hstarU : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hUmem
  calc star U * A * U = star U * (A * U) := by rw [Matrix.mul_assoc]
    _ = star U * (U * Matrix.diagonal _) := by rw [hAU]
    _ = (star U * U) * Matrix.diagonal _ := by rw [← Matrix.mul_assoc]
    _ = Matrix.diagonal _ := by rw [hstarU, Matrix.one_mul]


/-- Frobenius sum as a trace: `↑(∑ i j, normSq (M i j)) = trace (star M * M)`. -/
private lemma ofReal_frob_eq_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (M i j) : ℝ) : ℂ) = Matrix.trace (star M * M) := by
  have e : ∀ a b : Fin n, star (M b a) * M b a = ((Complex.normSq (M b a) : ℝ) : ℂ) := by
    intro a b
    rw [← starRingEnd_apply (M b a), ← Complex.normSq_eq_conj_mul_self]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply, e,
    ← Complex.ofReal_sum]
  rw [Finset.sum_comm]

/-- The star of a unitary matrix is unitary. -/
private lemma star_mem_unitary {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    star U ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_star]
  exact Matrix.mem_unitaryGroup_iff'.mp hU

/-- Left unitary invariance of `star M * M`. -/
private lemma star_mul_self_left_unitary {n : ℕ} {M P : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    star (P * M) * (P * M) = star M * M := by
  have hPs1 : star P * P = 1 := Matrix.mem_unitaryGroup_iff'.mp hP
  calc star (P * M) * (P * M) = star M * ((star P * P) * M) := by
        rw [StarMul.star_mul]; simp only [Matrix.mul_assoc]
    _ = star M * M := by rw [hPs1, Matrix.one_mul]

/-- Right unitary invariance of the trace of `star M * M`. -/
private lemma trace_star_mul_self_right_unitary {n : ℕ} {M Q : Matrix (Fin n) (Fin n) ℂ}
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.trace (star (M * Q) * (M * Q)) = Matrix.trace (star M * M) := by
  have hQ1 : Q * star Q = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  have e : star (M * Q) * (M * Q) = star Q * (star M * M) * Q := by
    rw [StarMul.star_mul]; simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, ← Matrix.mul_assoc Q (star Q) _, hQ1, Matrix.one_mul]

/-- Row sums of `normSq` entries of a unitary matrix are 1. -/
private lemma sum_normSq_row_of_unitary {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.mp hW) i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have e : ∀ j, W i j * star (W i j) = ((Complex.normSq (W i j) : ℝ) : ℂ) := by
    intro j
    rw [← starRingEnd_apply (W i j), ← Complex.mul_conj]
  simp only [e, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Column sums of `normSq` entries of a unitary matrix are 1. -/
private lemma sum_normSq_col_of_unitary {n : ℕ} {W : Matrix (Fin n) (Fin n) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin n) ℂ) (j : Fin n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hW) j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at h
  have e : ∀ i, star (W i j) * W i j = ((Complex.normSq (W i j) : ℝ) : ℂ) := by
    intro i
    rw [← starRingEnd_apply (W i j), ← Complex.normSq_eq_conj_mul_self]
  simp only [e, ← Complex.ofReal_sum] at h
  exact_mod_cast h

/-- Entries of `D_λ * W - W * D_μ`. -/
private lemma entry_diag_mul_sub {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ)
    (lam mu : Fin n → ℝ) (k i : Fin n) :
    (Matrix.diagonal (fun a => ((lam a : ℝ) : ℂ)) * W -
      W * Matrix.diagonal (fun a => ((mu a : ℝ) : ℂ))) k i
    = W k i * (((lam k - mu i : ℝ)) : ℂ) := by
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [Complex.ofReal_sub]
  ring

/--
**Hoffman–Wielandt inequality for Hermitian matrices.** Let $A$ and $B$ be Hermitian
$n \times n$ complex matrices with eigenvalues $\lambda_1 \ge \dots \ge \lambda_n$ and
$\mu_1 \ge \dots \ge \mu_n$ respectively, counted with multiplicity. Then
$\sum_{i=1}^n (\lambda_i - \mu_i)^2 \le \sum_{i=1}^n \sum_{j=1}^n |A_{ij} - B_{ij}|^2$, that is,
the left side is at most the squared Frobenius norm of $A - B$.

Proves `Wanted` entry `hoffman_wielandt_hermitian`.

Source: A. J. Hoffman and H. W. Wielandt, Duke Math. J. 20 (1953), DOI
10.1215/S0012-7094-53-02004-3.
-/
theorem hoffman_wielandt_hermitian
    {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    let hA_sym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
    let hB_sym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB)
    ∑ i : Fin n, (hA_sym.eigenvalues finrank_euclideanSpace_fin i -
        hB_sym.eigenvalues finrank_euclideanSpace_fin i) ^ 2 ≤
      ∑ i : Fin n, ∑ j : Fin n, Complex.normSq (A i j - B i j) := by
  have hlam_anti : Antitone ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace_fin) :=
    LinearMap.IsSymmetric.eigenvalues_antitone _ _
  have hmu_anti : Antitone ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
      finrank_euclideanSpace_fin) :=
    LinearMap.IsSymmetric.eigenvalues_antitone _ _
  have hmono : Monovary ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
      finrank_euclideanSpace_fin)
      ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
      finrank_euclideanSpace_fin) :=
    hlam_anti.monovary hmu_anti
  obtain ⟨U, hUmem, hUA⟩ := star_mul_diagonal_aux hA
  obtain ⟨V, hVmem, hVB⟩ := star_mul_diagonal_aux hB
  have hU1 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hUmem
  have hV1 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hVmem
  have hWmem : star U * V ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff]
    have eW : (star U * V) * star (star U * V) = star U * ((V * star V) * U) := by
      rw [StarMul.star_mul, star_star]
      simp only [Matrix.mul_assoc]
    rw [eW, hV1, Matrix.one_mul]
    exact Matrix.mem_unitaryGroup_iff'.mp hUmem
  set S : Matrix (Fin n) (Fin n) ℝ := fun i j => Complex.normSq ((star U * V) i j) with hSdef
  have hSmem : S ∈ doublyStochastic ℝ (Fin n) := by
    rw [mem_doublyStochastic_iff_sum]
    refine ⟨fun i j => Complex.normSq_nonneg _, ?_, ?_⟩
    · intro i
      have h := sum_normSq_row_of_unitary hWmem i
      simpa only [hSdef] using h
    · intro j
      have h := sum_normSq_col_of_unitary hWmem j
      simpa only [hSdef] using h
  have hN : star U * (A - B) * V
      = Matrix.diagonal (fun a => (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin a) : ℂ)) * (star U * V) -
        (star U * V) * Matrix.diagonal
          (fun a => (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin a) : ℂ)) := by
    have hsub : star U * (A - B) * V = star U * A * V - star U * B * V := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
    have eA : (star U * A * U) * (star U * V) = star U * A * V := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U (star U) V, hU1, Matrix.one_mul]
    have eB : (star U * V) * (star V * B * V) = star U * B * V := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc V (star V) (B * V), hV1, Matrix.one_mul]
    rw [hsub, ← eA, ← eB, hUA, hVB]
  have htrace_eq : Matrix.trace (star (A - B) * (A - B))
      = Matrix.trace (star (star U * (A - B) * V) * (star U * (A - B) * V)) := by
    have e1 := trace_star_mul_self_right_unitary (M := star U * (A - B)) (Q := V) hVmem
    have e2 := star_mul_self_left_unitary (M := (A - B)) (P := star U) (star_mem_unitary hUmem)
    rw [e1, e2]
  have hNentries : ∀ k i : Fin n,
      star ((star U * (A - B) * V) k i) * (star U * (A - B) * V) k i
      = ((S k i * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin k -
          (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin i)) ^ 2 : ℝ) : ℂ) := by
    intro k i
    have h2 := congrFun (congrFun hN k) i
    rw [entry_diag_mul_sub (star U * V) _ _ k i] at h2
    have hoR : star (((((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin k -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i) : ℝ)) : ℂ)
        = (((((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin k -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i) : ℝ)) : ℂ) := by
      rw [← starRingEnd_apply]
      exact Complex.conj_ofReal _
    have hw2 : star ((star U * V) k i) * (star U * V) k i
        = ((Complex.normSq ((star U * V) k i) : ℝ) : ℂ) := by
      rw [← starRingEnd_apply ((star U * V) k i), ← Complex.normSq_eq_conj_mul_self]
    have eS : S k i = Complex.normSq ((star U * V) k i) := rfl
    have efin : ∀ c w : ℂ, (c * star w) * (w * c) = (star w * w) * (c * c) := by
      intro c w; ring
    rw [h2, StarMul.star_mul, hoR, efin, hw2, eS, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      pow_two]
  have htrace_expand : Matrix.trace (star (star U * (A - B) * V) * (star U * (A - B) * V))
      = ∑ i, ∑ k, star ((star U * (A - B) * V) k i) * (star U * (A - B) * V) k i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply]
  have hNsum : (∑ i, ∑ k, star ((star U * (A - B) * V) k i) * (star U * (A - B) * V) k i)
      = ((∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j)) ^ 2 : ℝ) : ℂ) := by
    calc (∑ i, ∑ k, star ((star U * (A - B) * V) k i) * (star U * (A - B) * V) k i)
        = ∑ i, ∑ k, ((S k i * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin k -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i)) ^ 2 : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro k _
          exact hNentries k i
      _ = ((∑ i, ∑ k, S k i * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin k -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i)) ^ 2 : ℝ) : ℂ) := by
          simp only [← Complex.ofReal_sum]
      _ = ((∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j)) ^ 2 : ℝ) : ℂ) := by
          rw [Finset.sum_comm]
  have hbridge : ((∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j)) ^ 2 : ℝ) : ℂ)
      = ((∑ i, ∑ j, Complex.normSq ((A - B) i j) : ℝ) : ℂ) := by
    rw [ofReal_frob_eq_trace, htrace_eq, htrace_expand, hNsum]
  have hFreal : (∑ i, ∑ j, Complex.normSq (A i j - B i j))
      = (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin i -
          (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin j)) ^ 2) := by
    have h := Complex.ofReal_inj.mp hbridge.symm
    simpa only [Matrix.sub_apply] using h
  have hrow : ∀ i, ∑ j, S i j = 1 := by
    intro i
    have h := sum_normSq_row_of_unitary hWmem i
    simpa only [hSdef] using h
  have hcol : ∀ j, ∑ i, S i j = 1 := by
    intro j
    have h := sum_normSq_col_of_unitary hWmem j
    simpa only [hSdef] using h
  have hFexpand : (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j)) ^ 2)
      = (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin i) ^ 2)
        + (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin i) ^ 2)
        - 2 * (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin i) *
          ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin j))) := by
    have step : ∀ i j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j)) ^ 2
        = S i j * ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2
          - 2 * (S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) *
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j)))
          + S i j * ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j) ^ 2 := by
      intro i j; ring
    have hstep : (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i -
              (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin j)) ^ 2)
        = (∑ i, ∑ j, S i j * ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
          - (∑ i, ∑ j, 2 * (S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) *
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j))))
          + (∑ i, ∑ j, S i j * ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j) ^ 2) := by
      simp_rw [step, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have eLam : (∑ i, ∑ j, S i j * ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
        = ∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin i) ^ 2 := by
      apply Finset.sum_congr rfl; intro i _
      rw [← Finset.sum_mul, hrow i, one_mul]
    have eMu : (∑ i, ∑ j, S i j * ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j) ^ 2)
        = ∑ j, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin j) ^ 2 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [← Finset.sum_mul, hcol j, one_mul]
    have emid : (∑ i, ∑ j, 2 * (S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) *
              ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin j))))
        = 2 * (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) *
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j))) := by
      simp_rw [← Finset.mul_sum]
    rw [hstep, eLam, emid, eMu]
    ring
  have hLHS : (∑ i, (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) -
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i)) ^ 2)
      = (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin i) ^ 2)
        + (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin i) ^ 2)
        - 2 * (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
          finrank_euclideanSpace_fin i) *
          ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
          finrank_euclideanSpace_fin i)) := by
    have step : ∀ i, (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) -
              ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin i)) ^ 2
        = ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2
          + ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2
          - 2 * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) *
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i)) := by
      intro i; ring
    calc (∑ i, (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) -
              ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin i)) ^ 2)
          = ∑ i, (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) ^ 2
            + ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin i) ^ 2
            - 2 * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) *
              ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin i))) := by
            apply Finset.sum_congr rfl; intro i _
            exact step i
        _ = (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
          + (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
          - 2 * (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) *
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcross := sum_doublyStochastic_mul_le hmono hSmem
  have hfin : (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
          + (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
          - 2 * (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) *
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i))
        ≤ (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
          + (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin i) ^ 2)
          - 2 * (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i) *
            ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j))) := by
    have h2CG : 2 * (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) *
              ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin j)))
        ≤ 2 * (∑ i, ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) *
              ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin i)) :=
      mul_le_mul_of_nonneg_left hcross (by norm_num)
    exact sub_le_sub_left h2CG _
  have hfinal : (∑ i, (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
              finrank_euclideanSpace_fin i) -
              ((Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
              finrank_euclideanSpace_fin i)) ^ 2)
        ≤ (∑ i, ∑ j, S i j * (((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues
            finrank_euclideanSpace_fin i -
            (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues
            finrank_euclideanSpace_fin j)) ^ 2) := by
    rw [hLHS, hFexpand]
    exact hfin
  rw [hFreal]
  exact hfinal

end MathlibExt.Analysis.InnerProductSpace.HoffmanWielandtWanted
