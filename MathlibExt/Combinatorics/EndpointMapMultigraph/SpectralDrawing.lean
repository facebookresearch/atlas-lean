/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.EndpointMapMultigraph.AlgebraicConnectivity

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Optimality of spectral graph drawings

Hall's spectral drawing of a graph in `k` dimensions, by Laplacian eigenvectors of
`λ₂, …, λ_{k+1}`, minimises the total squared edge length `∑ᵢ xᵢᵀ L xᵢ` among orthonormal
coordinate vectors `x₁, …, x_k` orthogonal to the constants (D. A. Spielman, *Spectral and
Algebraic Graph Theory*, draft of 2 April 2025, Theorem 3.2.1, a variant of K. Fan, PNAS 35 (1949),
Theorem 1). The same optimisation underlies Laplacian eigenmaps and spectral clustering in machine
learning.

The proof expands each Rayleigh form in the eigenbasis (Spielman, Lemma 2.1.1), adds the unit
constant vector to the family, and bounds `∑_j λ_j c_j` from below for weights `0 ≤ c_j ≤ 1`
summing to `k + 1`.
-/

@[expose] public section

namespace EndpointMapMultigraph

open Matrix MathlibExt.Analysis.InnerProductSpace.CourantFischer Finset
open scoped InnerProductSpace

/-- For antitone `μ` and weights `0 ≤ c ≤ 1` summing to `m`, `∑_j μ_j c_j` is at least the sum
of the `m` smallest values of `μ`. -/
private theorem sum_antitone_tail_le_sum_mul {n m : ℕ} (hm : m ≤ n) (μ : Fin n → ℝ)
    (hμ : Antitone μ) (c : Fin n → ℝ)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (hsum : ∑ j, c j = m) :
    ∑ t : Fin m, μ ⟨n - 1 - t, by omega⟩ ≤ ∑ j, μ j * c j := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have hc : ∀ j, c j = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hc0 j)).1 (by simpa using hsum) j
        (Finset.mem_univ _)
      exact this
    simp [hc]
  set S : Finset (Fin n) := univ.filter fun j => n - m ≤ (j : ℕ)
  have hbij : ∀ f : Fin n → ℝ, ∑ t : Fin m, f ⟨n - 1 - t, by omega⟩ = ∑ j ∈ S, f j := by
    intro f
    refine Finset.sum_bij' (fun t _ => (⟨n - 1 - t, by omega⟩ : Fin n))
      (fun j _ => (⟨n - 1 - j, by
        have := (Finset.mem_filter.1 ‹j ∈ S›).2; have := j.isLt; omega⟩ : Fin m)) ?_ ?_ ?_ ?_ ?_
    · intro t _
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      have := t.isLt; omega
    · intro j _; exact Finset.mem_univ _
    · intro t _; ext; simp; have := t.isLt; omega
    · intro j hj; ext; simp; have := (Finset.mem_filter.1 hj).2; have := j.isLt; omega
    · intro t _; rfl
  have hcard : (S.card : ℝ) = m := by
    have := hbij (fun _ => 1)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at this
    linarith
  rw [hbij μ]
  set θ := μ ⟨n - m, by omega⟩
  have hin : ∀ j ∈ S, μ j ≤ θ := by
    intro j hj
    exact hμ (Fin.mk_le_mk.2 (Finset.mem_filter.1 hj).2)
  have hout : ∀ j ∈ univ.filter (fun j : Fin n => ¬ n - m ≤ (j : ℕ)), θ ≤ μ j := by
    intro j hj
    have := (Finset.mem_filter.1 hj).2
    exact hμ (show j ≤ ⟨n - m, by omega⟩ from Fin.mk_le_mk.2 (by omega) |>.trans le_rfl)
  have hsplit : ∀ f : Fin n → ℝ, ∑ j, f j = ∑ j ∈ S, f j +
      ∑ j ∈ univ.filter (fun j : Fin n => ¬ n - m ≤ (j : ℕ)), f j := fun f =>
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h1 : ∑ j ∈ univ.filter (fun j : Fin n => ¬ n - m ≤ (j : ℕ)), θ * c j ≤
      ∑ j ∈ univ.filter (fun j : Fin n => ¬ n - m ≤ (j : ℕ)), μ j * c j :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hout j hj) (hc0 j)
  have h2 : ∑ j ∈ S, μ j * (1 - c j) ≤ ∑ j ∈ S, θ * (1 - c j) :=
    Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hin j hj) (by linarith [hc1 j])
  have hcs := hsplit c
  rw [hsum] at hcs
  rw [hsplit (fun j => μ j * c j)]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul] at h1 h2
  rw [hcard] at h2
  have h3 : (m : ℝ) * θ = θ * ∑ j ∈ S, c j +
      θ * ∑ j ∈ univ.filter (fun j : Fin n => ¬ n - m ≤ (j : ℕ)), c j := by
    rw [hcs]; ring
  linarith


variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
  (end₁ end₂ : E → V)

omit [DecidableEq E] [Fintype E] in
private theorem rayleighForm_toLp' (M : Matrix V V ℝ) (v : V → ℝ) :
    rayleighForm (toEuclideanLin M) (WithLp.toLp 2 v) = v ⬝ᵥ (M *ᵥ v) := by
  simp [rayleighForm, Matrix.toLpLin_toLp, EuclideanSpace.inner_toLp_toLp]

/-- **Hall's spectral drawing is optimal.** Let `L` be the Laplacian of a weighted multigraph with
nonnegative weights and `0 = λ₁ ≤ λ₂ ≤ ⋯ ≤ λₙ` its eigenvalues. For orthonormal vectors
`x₁, …, x_k`, all orthogonal to the constant vector, `∑ᵢ xᵢᵀ L xᵢ ≥ λ₂ + ⋯ + λ_{k+1}`; here
`λ_{j+2}` is the eigenvalue of index `n - 2 - j` in the decreasing enumeration
`LinearMap.IsSymmetric.eigenvalues` (D. A. Spielman, *Spectral and Algebraic Graph Theory*, draft of
2 April 2025, Theorem 3.2.1, which assumes `λ₁ < λ₂`, i.e. a connected graph; the inequality does
not need it, and the equality clause is not stated here). Since
`∑ᵢ xᵢᵀ L xᵢ = ∑_e w_e ‖X(a) - X(b)‖²` for the drawing `X(a) = (x₁(a), …, x_k(a))`, the bottom
nontrivial eigenvectors give a drawing of least total squared edge length. -/
theorem sum_eigenvalues_le_sum_quadratic_form {w : E → ℝ} (hw : 0 ≤ w) {k : ℕ}
    (hk : k + 1 ≤ Fintype.card V) (x : Fin k → V → ℝ)
    (horth : ∀ i j, x i ⬝ᵥ x j = if i = j then 1 else 0) (hperp : ∀ i, x i ⬝ᵥ 1 = 0) :
    ∑ j : Fin k, (isSymmetric_toEuclideanLin_laplacian end₁ end₂ w).eigenvalues
        finrank_euclideanSpace ⟨Fintype.card V - 2 - j, by have := j.isLt; omega⟩ ≤
      ∑ i, x i ⬝ᵥ (laplacian end₁ end₂ w *ᵥ x i) := by
  classical
  set n := Fintype.card V with hn_def
  set L := laplacian end₁ end₂ w
  set hT := isSymmetric_toEuclideanLin_laplacian end₁ end₂ w
  set b := hT.eigenvectorBasis (finrank_euclideanSpace (𝕜 := ℝ) (ι := V))
  set μ := hT.eigenvalues (finrank_euclideanSpace (𝕜 := ℝ) (ι := V))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set s : ℝ := (Real.sqrt n)⁻¹
  have hs2 : s ^ 2 * n = 1 := by
    rw [inv_pow, Real.sq_sqrt hn0.le, inv_mul_cancel₀ hn0.ne']
  set u : EuclideanSpace ℝ V := WithLp.toLp 2 (s • (1 : V → ℝ))
  set y : Option (Fin k) → EuclideanSpace ℝ V := fun o => o.elim u fun i => WithLp.toLp 2 (x i)
  have hone : (1 : V → ℝ) ⬝ᵥ (1 : V → ℝ) = n := by simp [dotProduct, n]
  have hy : Orthonormal ℝ y := by
    rw [orthonormal_iff_ite]
    intro o o'
    cases o with
    | none =>
      cases o' with
      | none =>
        simp only [y, Option.elim, u, EuclideanSpace.inner_toLp_toLp, star_trivial, ite_true]
        rw [smul_dotProduct, dotProduct_smul, hone, smul_eq_mul, smul_eq_mul, ← hs2]
        ring
      | some j =>
        simp only [y, Option.elim, u, EuclideanSpace.inner_toLp_toLp, star_trivial,
          reduceCtorEq, ite_false]
        rw [dotProduct_smul, hperp, smul_zero]
    | some i =>
      cases o' with
      | none =>
        simp only [y, Option.elim, u, EuclideanSpace.inner_toLp_toLp, star_trivial,
          reduceCtorEq, ite_false]
        rw [smul_dotProduct, dotProduct_comm, hperp, smul_zero]
      | some j =>
        simp only [y, Option.elim, EuclideanSpace.inner_toLp_toLp, star_trivial, Option.some.injEq]
        rw [horth j i]
        by_cases hij : i = j
        · simp [hij]
        · simp [hij, Ne.symm hij]
  -- weights of the eigenvectors
  set c : Fin n → ℝ := fun j => ∑ o, ‖⟪b j, y o⟫_ℝ‖ ^ 2
  have hc0 : ∀ j, 0 ≤ c j := fun j => Finset.sum_nonneg fun o _ => by positivity
  have hc1 : ∀ j, c j ≤ 1 := by
    intro j
    have h := hy.sum_inner_products_le (s := Finset.univ) (x := b j)
    rw [b.orthonormal.1 j, one_pow] at h
    simpa [c, real_inner_comm] using h
  have hcsum : ∑ j, c j = ((k + 1 : ℕ) : ℝ) := by
    have : ∀ o, ∑ j, ‖⟪b j, y o⟫_ℝ‖ ^ 2 = 1 := fun o => by
      rw [b.sum_sq_norm_inner_right, hy.1 o, one_pow]
    simp only [c]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun o _ => this o]
    simp
  have hexp : ∑ o, rayleighForm (toEuclideanLin L) (y o) = ∑ j, μ j * c j := by
    rw [Finset.sum_congr rfl fun o _ =>
      rayleighForm_eq_expansion hT (finrank_euclideanSpace (𝕜 := ℝ) (ι := V)) (y o)]
    simp only [c, Finset.mul_sum]
    exact Finset.sum_comm
  have hRu : rayleighForm (toEuclideanLin L) u = 0 := by
    rw [rayleighForm_toLp', Matrix.mulVec_smul, laplacian_mulVec_one, smul_zero, dotProduct_zero]
  have hsplit : ∑ o, rayleighForm (toEuclideanLin L) (y o) =
      ∑ i, x i ⬝ᵥ (L *ᵥ x i) := by
    rw [Fintype.sum_option]
    simp only [y, Option.elim, hRu, zero_add, rayleighForm_toLp']
  have key := sum_antitone_tail_le_sum_mul hk μ (hT.eigenvalues_antitone _) c hc0 hc1
    (by rw [hcsum])
  rw [← hexp, hsplit, Fin.sum_univ_succ] at key
  -- the smallest eigenvalue is nonnegative
  have hlast : 0 ≤ μ ⟨n - 1 - ((0 : Fin (k + 1)) : ℕ), by omega⟩ := by
    obtain ⟨-, -, -, z, -, -, hz⟩ := exists_tail_submodule hT
      (finrank_euclideanSpace (𝕜 := ℝ) (ι := V)) (k := n - 1 - ((0 : Fin (k + 1)) : ℕ))
      (by omega)
    refine le_of_le_of_eq ?_ hz
    rw [show z = WithLp.toLp 2 (WithLp.ofLp z) from rfl, rayleighForm_toLp',
      dotProduct_mulVec_laplacian]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (sq_nonneg _)
  have hidx : ∑ t : Fin k, μ ⟨n - 1 - ((Fin.succ t : Fin (k + 1)) : ℕ), by omega⟩ =
      ∑ j : Fin k, μ ⟨n - 2 - j, by have := j.isLt; omega⟩ := by
    refine Finset.sum_congr rfl fun t _ => ?_
    congr 1
    ext
    simp only [Fin.val_succ]
    omega
  rw [hidx] at key
  linarith

end EndpointMapMultigraph
