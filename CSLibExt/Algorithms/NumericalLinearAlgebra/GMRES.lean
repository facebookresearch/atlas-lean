/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.ConjugateGradient
public import CSLibExt.MachineLearning.Regression.LeastSquares
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# GMRES: residual minimization over Krylov spaces and its polynomial characterization

For a real square system `A x = b` with initial guess `x₀` and initial residual
`r₀ = b - A x₀`, the `k`-th GMRES iterate (Saad and Schultz, 1986) is a point
`x ∈ x₀ + 𝒦_k(A, r₀)` minimizing the residual norm `‖b - A x‖₂` over that affine Krylov space
(`IsGMRESIterate`). In practice it is computed through the Arnoldi iteration and a small
`(k + 1) × k` Hessenberg least-squares problem (Trefethen and Bau, *Numerical Linear Algebra*,
Lecture 35); here the iterate is characterized by its optimality, which is what the theory uses.

* **Existence** (`exists_isGMRESIterate`): a GMRES iterate always exists. It is a least-squares
  problem with the matrix `A K_k`, `K_k` the Krylov matrix `[r₀ | A r₀ | … | A^{k-1} r₀]`,
  solved by `Cslib.MachineLearning.LeastSquares.exists_rss_le` (least-squares solutions exist
  for every matrix).
* **Polynomial characterization** (`rss_le_of_isGMRESIterate`): the GMRES residual is at
  most `‖p(A) r₀‖` for every polynomial `p` of degree `≤ k` with `p(0) = 1`. Since the residual
  is itself of this form (not formalized here), GMRES solves the "GMRES approximation problem"
  of Trefethen–Bau, Lecture 35, `minimize ‖p(A) r₀‖` over such `p`, so its convergence is a
  question of polynomial approximation on the spectrum (Driscoll, Toh and Trefethen 1998).
* **Finite termination** (`mulVec_eq_of_isGMRESIterate_dim`): for invertible `A`, GMRES solves
  the system exactly in at most `n` steps (Trefethen–Bau, Lecture 35), here by the
  Cayley–Hamilton theorem applied to the normalized characteristic polynomial.

The squared residual `‖b - A x‖²` is `Cslib.MachineLearning.LeastSquares.rss A b x`, the
residual sum of squares of linear regression. All statements are in exact arithmetic.

## References

* Y. Saad, M. H. Schultz, *GMRES: a generalized minimal residual algorithm for solving
  nonsymmetric linear systems*, SIAM J. Sci. Stat. Comput. 7 (1986), 856–869.
* L. N. Trefethen, D. Bau III, *Numerical Linear Algebra*, SIAM, 1997, Lecture 35
  (GMRES and its polynomial approximation problem).
* T. A. Driscoll, K.-C. Toh, L. N. Trefethen, *From potential theory to matrix iterations in
  six steps*, SIAM Rev. 40 (1998), 547–578.
-/

@[expose] public section

open Matrix Polynomial
open MathlibExt.LinearAlgebra.Matrix.ConjugateGradient Cslib.MachineLearning.LeastSquares

namespace Cslib.Algorithms.NumericalLinearAlgebra.GMRES

variable {n : ℕ}

private lemma dotProduct_self_nonneg' {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- `x` is a `k`-th GMRES iterate for `A x = b` from `x₀`: it lies in `x₀ + 𝒦_k(A, r₀)` with
`r₀ = b - A x₀` and minimizes the squared residual `‖b - A y‖²` over that affine space. -/
def IsGMRESIterate (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ)
    (x : Fin n → ℝ) : Prop :=
  x - x₀ ∈ krylov A (b - A *ᵥ x₀) k ∧
    ∀ y, y - x₀ ∈ krylov A (b - A *ᵥ x₀) k → rss A b x ≤ rss A b y

/-- The Krylov matrix `[r | A r | … | A^{k-1} r]`. -/
noncomputable def krylovMatrix (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (k : ℕ) :
    Matrix (Fin n) (Fin k) ℝ :=
  Matrix.of fun i j => ((A ^ (j : ℕ)) *ᵥ r) i

lemma krylovMatrix_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) {k : ℕ}
    (c : Fin k → ℝ) : krylovMatrix A r k *ᵥ c = ∑ j, c j • ((A ^ (j : ℕ)) *ᵥ r) := by
  ext i
  simp [krylovMatrix, mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- The Krylov space is the column space of the Krylov matrix. -/
lemma mem_krylov_iff (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (k : ℕ)
    (v : Fin n → ℝ) : v ∈ krylov A r k ↔ ∃ c, krylovMatrix A r k *ᵥ c = v := by
  simp only [krylov, krylovMatrix_mulVec]
  exact Submodule.mem_span_range_iff_exists_fun ℝ

lemma aeval_mulVec_mem_krylov (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) {k : ℕ}
    (q : ℝ[X]) (hq : q.natDegree < k) : aeval A q *ᵥ r ∈ krylov A r k := by
  rw [aeval_eq_sum_range' hq, sum_mulVec]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [smul_mulVec]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩)

/-- **Existence of GMRES iterates.** For every `k` there is a point of `x₀ + 𝒦_k(A, r₀)`
minimizing the residual over it. -/
theorem exists_isGMRESIterate (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    ∃ x, IsGMRESIterate A b x₀ k x := by
  set r₀ := b - A *ᵥ x₀
  set V := krylovMatrix A r₀ k
  obtain ⟨c, hc⟩ := exists_rss_le (A * V) r₀
  have hres : ∀ d, rss A b (x₀ + V *ᵥ d) = rss (A * V) r₀ d := by
    intro d
    simp only [rss, mulVec_add, ← mulVec_mulVec, r₀]
    congr 1 <;> abel
  refine ⟨x₀ + V *ᵥ c, ?_, ?_⟩
  · rw [add_sub_cancel_left]
    exact (mem_krylov_iff A r₀ k _).2 ⟨c, rfl⟩
  · intro y hy
    obtain ⟨d, hd⟩ := (mem_krylov_iff A r₀ k _).1 hy
    have hy' : y = x₀ + V *ᵥ d := by rw [hd]; abel
    rw [hy', hres, hres]
    exact hc d

/-- **The GMRES polynomial bound** (Trefethen–Bau, Lecture 35): if `x` is a `k`-th GMRES
iterate, then `‖b - A x‖² ≤ ‖p(A) r₀‖²` for every real polynomial `p` of degree at most `k`
with `p(0) = 1`. -/
theorem rss_le_of_isGMRESIterate {A : Matrix (Fin n) (Fin n) ℝ} {b x₀ x : Fin n → ℝ}
    {k : ℕ} (hx : IsGMRESIterate A b x₀ k x) (p : ℝ[X]) (hp : p.natDegree ≤ k)
    (hp0 : p.eval 0 = 1) :
    rss A b x ≤
      (aeval A p *ᵥ (b - A *ᵥ x₀)) ⬝ᵥ (aeval A p *ᵥ (b - A *ᵥ x₀)) := by
  set r₀ := b - A *ᵥ x₀
  have hdvd : X ∣ 1 - p := by
    rw [X_dvd_iff, coeff_sub, AddMonoidAlgebra.coeff_one_zero, coeff_zero_eq_eval_zero, hp0,
      sub_self]
  obtain ⟨q, hq⟩ := hdvd
  have hpq : p = 1 - X * q := by rw [← hq]; ring
  have hmem : aeval A q *ᵥ r₀ ∈ krylov A r₀ k := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · apply aeval_mulVec_mem_krylov
      have h1 : (1 - p).natDegree ≤ k :=
        (natDegree_sub_le _ _).trans (max_le (by simp) hp)
      rw [hq, natDegree_mul X_ne_zero hq0, natDegree_X] at h1
      omega
  have key := hx.2 (x₀ + aeval A q *ᵥ r₀) (by rwa [add_sub_cancel_left])
  have hres : b - A *ᵥ (x₀ + aeval A q *ᵥ r₀) = aeval A p *ᵥ r₀ := by
    rw [hpq, map_sub, map_one, map_mul, aeval_X, sub_mulVec, one_mulVec, ← mulVec_mulVec,
      mulVec_add]
    simp only [r₀]
    abel
  unfold rss at key ⊢
  rwa [hres] at key

/-- **Finite termination of GMRES.** If `A` is invertible, every `n`-th GMRES iterate solves
`A x = b` exactly. -/
theorem mulVec_eq_of_isGMRESIterate_dim {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A.det)
    {b x₀ x : Fin n → ℝ} (hx : IsGMRESIterate A b x₀ n x) : A *ᵥ x = b := by
  have hc0 : A.charpoly.eval 0 ≠ 0 := by
    intro h
    have := det_eq_sign_charpoly_coeff A
    rw [coeff_zero_eq_eval_zero, h, mul_zero] at this
    exact hA.ne_zero this
  set p : ℝ[X] := C (A.charpoly.eval 0)⁻¹ * A.charpoly
  have hpdeg : p.natDegree ≤ n := by
    refine (natDegree_C_mul_le _ _).trans ?_
    simp
  have hp0 : p.eval 0 = 1 := by
    simp only [p, eval_mul, eval_C]
    exact inv_mul_cancel₀ hc0
  have hpA : aeval A p = 0 := by
    simp only [p, map_mul, aeval_C, aeval_self_charpoly, mul_zero]
  have hle := rss_le_of_isGMRESIterate hx p hpdeg hp0
  rw [hpA, zero_mulVec, dotProduct_zero] at hle
  have h0 : rss A b x = 0 := le_antisymm hle (dotProduct_self_nonneg' _)
  have := dotProduct_self_eq_zero.1 h0
  rw [sub_eq_zero] at this
  exact this.symm

end Cslib.Algorithms.NumericalLinearAlgebra.GMRES
