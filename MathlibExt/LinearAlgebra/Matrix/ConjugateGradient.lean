/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema

/-!
# The conjugate gradient method: Krylov optimality and the condition-number bound

For a symmetric positive definite `A : Matrix (Fin n) (Fin n) ℝ`, a right-hand side `b` with
solution `x⋆` (`A x⋆ = b`) and a starting point `x₀`, the conjugate gradient method of Hestenes
and Stiefel (1952) iterates

  `α_k = r_kᵀ r_k / d_kᵀ A d_k`, `x_{k+1} = x_k + α_k d_k`, `r_{k+1} = r_k - α_k A d_k`,
  `β_k = r_{k+1}ᵀ r_{k+1} / r_kᵀ r_k`, `d_{k+1} = r_{k+1} + β_k d_k`,

from `r₀ = d₀ = b - A x₀` (`step`, `iterate`). Once a residual vanishes every later step is the
identity on `x` (the quotients are `0 / 0 = 0`), so no junk value enters at termination.

* **Krylov optimality.** `x_k - x₀` lies in the Krylov space
  `𝒦_k = span {r₀, A r₀, …, A^{k-1} r₀}` (`iterate_x_sub_mem_krylov`), and `x_k` minimizes the
  energy norm of the error `‖x - x⋆‖_A = √((x - x⋆)ᵀ A (x - x⋆))` over `x₀ + 𝒦_k`
  (`energyNorm_iterate_le`).
* **Condition-number bound.** If the eigenvalues of `A` lie in `[a, c]` with `0 < a`, every
  energy minimizer over `x₀ + 𝒦_k` satisfies
  `‖x - x⋆‖_A ≤ 2 ((√κ - 1) / (√κ + 1))^k ‖x₀ - x⋆‖_A` with `κ = c / a`
  (`energyNorm_le_of_isMin_krylov`), via the shifted and scaled Chebyshev polynomial (the
  classical estimate of Kaniel and Daniel, as presented by Golub and Van Loan). Taking
  `a` and `c` to be the extreme eigenvalues, `κ` is the spectral condition number of `A`
  (`energyNorm_iterate_sub_le_condNum`).

BOLT-LMM uses this method to apply `V⁻¹` without forming it; the bound is in exact arithmetic.

## Main results

* `iterate_x_sub_mem_krylov`, `energyNorm_iterate_le`: CG minimizes the energy norm of the
  error over the Krylov space.
* `energyNorm_le_of_isMin_krylov`: the Chebyshev bound for any Krylov energy minimizer.
* `energyNorm_iterate_sub_le`, `energyNorm_iterate_sub_le_condNum`: the CG error bound
  `‖e_k‖_A ≤ 2 ((√κ - 1) / (√κ + 1))^k ‖e_0‖_A`.

## References

* M. R. Hestenes, E. Stiefel, *Methods of conjugate gradients for solving linear systems*,
  J. Res. Nat. Bur. Standards 49 (1952), 409–436.
* G. H. Golub, C. F. Van Loan, *Matrix Computations*, 4th ed., Johns Hopkins, 2013,
  Section 11.3 (the conjugate gradient method and its convergence).
* S. Kaniel, *Estimates for some computational techniques in linear algebra*, Math. Comp. 20
  (1966), 369–378.
* J. W. Daniel, *The conjugate gradient method for linear and nonlinear operator equations*,
  SIAM J. Numer. Anal. 4 (1967), 10–26.
-/

@[expose] public section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.ConjugateGradient

/-- The energy norm `‖v‖_A = √(vᵀ A v)`; a norm when `A` is positive definite. -/
noncomputable def energyNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  √(v ⬝ᵥ (A *ᵥ v))

/-- The Krylov space `𝒦_k(A, r) = span {r, A r, …, A^{k-1} r}`. -/
noncomputable def krylov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (k : ℕ) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range fun i : Fin k => (A ^ (i : ℕ)) *ᵥ r)

/-- The state of the conjugate gradient method: iterate `x`, residual `r = b - A x` and search
direction `d`. -/
structure State (n : ℕ) where
  /-- The current iterate. -/
  x : Fin n → ℝ
  /-- The current residual `b - A x`. -/
  r : Fin n → ℝ
  /-- The current search direction. -/
  d : Fin n → ℝ

/-- One Hestenes–Stiefel conjugate gradient step. -/
noncomputable def step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (s : State n) : State n :=
  let α := (s.r ⬝ᵥ s.r) / (s.d ⬝ᵥ (A *ᵥ s.d))
  let r' := s.r - α • (A *ᵥ s.d)
  { x := s.x + α • s.d
    r := r'
    d := r' + ((r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)) • s.d }

/-- The initial state `x₀`, `r₀ = d₀ = b - A x₀`. -/
def init {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) : State n :=
  ⟨x₀, b - A *ᵥ x₀, b - A *ᵥ x₀⟩

/-- The `k`-th conjugate gradient state from `x₀` for the system `A x = b`. -/
noncomputable def iterate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    State n :=
  (step A)^[k] (init A b x₀)

/-! ### Krylov spaces -/

private lemma krylov_mono_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ) (k : ℕ) :
    krylov A r k ≤ krylov A r (k + 1) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, by omega⟩, rfl⟩

private lemma pow_mulVec_mem_krylov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ)
    (k : ℕ) : (A ^ k) *ᵥ r ∈ krylov A r (k + 1) :=
  Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩

private lemma mulVec_mem_krylov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (r : Fin n → ℝ)
    {k : ℕ} {v : Fin n → ℝ} (hv : v ∈ krylov A r k) : A *ᵥ v ∈ krylov A r (k + 1) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine Submodule.subset_span ⟨⟨i + 1, by omega⟩, ?_⟩
    simp only [mulVec_mulVec, pow_succ']
  | zero => simp
  | add x y _ _ hx hy => rw [mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mulVec_smul]; exact Submodule.smul_mem _ a hx

private lemma mem_krylov_succ {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {r : Fin n → ℝ} {k : ℕ}
    {v : Fin n → ℝ} (hv : v ∈ krylov A r (k + 1)) :
    ∃ u ∈ krylov A r k, ∃ c : ℝ, v = u + c • ((A ^ k) *ᵥ r) := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨i, hi⟩, rfl⟩ := hx
    by_cases hik : i < k
    · exact ⟨_, Submodule.subset_span ⟨⟨i, hik⟩, rfl⟩, 0, by simp⟩
    · obtain rfl : i = k := by omega
      exact ⟨0, Submodule.zero_mem _, 1, by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, c, rfl⟩ := hx
    obtain ⟨u', hu', c', rfl⟩ := hy
    exact ⟨u + u', Submodule.add_mem _ hu hu', c + c', by rw [add_smul]; abel⟩
  | smul a x _ hx =>
    obtain ⟨u, hu, c, rfl⟩ := hx
    exact ⟨a • u, Submodule.smul_mem _ a hu, a * c, by rw [smul_add, smul_smul]⟩

private lemma eq_zero_of_mem_krylov_zero {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {r v : Fin n → ℝ} (hv : v ∈ krylov A r 0) : v = 0 := by
  have h : krylov A r 0 = ⊥ := by
    rw [krylov, Set.range_eq_empty, Submodule.span_empty]
  rw [h] at hv
  exact (Submodule.mem_bot ℝ).mp hv

private lemma iterate_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    iterate A b x₀ (k + 1) = step A (iterate A b x₀ k) :=
  Function.iterate_succ_apply' _ _ _

/-- The membership invariant: `x_k - x₀ ∈ 𝒦_k`, `r_k, d_k ∈ 𝒦_{k+1}` and `r_k = b - A x_k`. -/
private lemma mem_invariant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b x₀ : Fin n → ℝ) (k : ℕ) :
    (iterate A b x₀ k).x - x₀ ∈ krylov A (b - A *ᵥ x₀) k ∧
      (iterate A b x₀ k).r ∈ krylov A (b - A *ᵥ x₀) (k + 1) ∧
      (iterate A b x₀ k).d ∈ krylov A (b - A *ᵥ x₀) (k + 1) ∧
      (iterate A b x₀ k).r = b - A *ᵥ (iterate A b x₀ k).x := by
  induction k with
  | zero =>
    have h := pow_mulVec_mem_krylov A (b - A *ᵥ x₀) 0
    rw [pow_zero, one_mulVec] at h
    exact ⟨by simp [iterate, init], h, h, rfl⟩
  | succ k ih =>
    obtain ⟨hx, hr, hd, hres⟩ := ih
    have hmono := krylov_mono_succ A (b - A *ᵥ x₀) (k + 1)
    rw [iterate_succ]
    simp only [step]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [add_sub_right_comm]
      exact Submodule.add_mem _ (krylov_mono_succ A _ k hx) (Submodule.smul_mem _ _ hd)
    · exact Submodule.sub_mem _ (hmono hr) (Submodule.smul_mem _ _ (mulVec_mem_krylov A _ hd))
    · exact Submodule.add_mem _
        (Submodule.sub_mem _ (hmono hr) (Submodule.smul_mem _ _ (mulVec_mem_krylov A _ hd)))
        (Submodule.smul_mem _ _ (hmono hd))
    · rw [hres, mulVec_add, mulVec_smul]
      abel

private lemma transpose_eq_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    Aᵀ = A := by
  have h := hA.isHermitian
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h

private lemma dotProduct_mulVec_symm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hAt : Aᵀ = A)
    (v w : Fin n → ℝ) : v ⬝ᵥ (A *ᵥ w) = w ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hAt, dotProduct_comm]

/-- The orthogonality invariant of CG: `r_k ⊥ 𝒦_k`, `A d_k ⊥ 𝒦_k` and `r_kᵀ d_k = r_kᵀ r_k`. -/
private lemma orth_invariant {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (b x₀ : Fin n → ℝ) (k : ℕ) :
    (∀ v ∈ krylov A (b - A *ᵥ x₀) k, v ⬝ᵥ (iterate A b x₀ k).r = 0) ∧
      (∀ v ∈ krylov A (b - A *ᵥ x₀) k, v ⬝ᵥ (A *ᵥ (iterate A b x₀ k).d) = 0) ∧
      (iterate A b x₀ k).r ⬝ᵥ (iterate A b x₀ k).d =
        (iterate A b x₀ k).r ⬝ᵥ (iterate A b x₀ k).r := by
  have hAt := transpose_eq_of_posDef hA
  induction k with
  | zero =>
    exact ⟨fun v hv => by rw [eq_zero_of_mem_krylov_zero hv, zero_dotProduct],
      fun v hv => by rw [eq_zero_of_mem_krylov_zero hv, zero_dotProduct], rfl⟩
  | succ k ih =>
    obtain ⟨ha, hb, hc⟩ := ih
    obtain ⟨-, hr, hd, -⟩ := mem_invariant A b x₀ k
    rw [iterate_succ]
    generalize iterate A b x₀ k = s at ha hb hc hr hd
    obtain ⟨x, r, d⟩ := s
    simp only at ha hb hc hr hd
    simp only [step]
    set K := krylov A (b - A *ᵥ x₀)
    set α := (r ⬝ᵥ r) / (d ⬝ᵥ (A *ᵥ d)) with hα
    set r' := r - α • (A *ᵥ d) with hr'
    set β := (r' ⬝ᵥ r') / (r ⬝ᵥ r) with hβ
    by_cases hr0 : r = 0
    · have hα0 : α = 0 := by simp [hα, hr0]
      have hr'0 : r' = 0 := by simp [hr', hα0, hr0]
      have hβ0 : β = 0 := by simp [hβ, hr'0]
      simp [hr'0, hβ0]
    have hrr : 0 < r ⬝ᵥ r := by
      rcases (dotProduct_self_star_nonneg r).lt_or_eq with h | h
      · simpa using h
      · exact absurd (dotProduct_star_self_eq_zero.mp (by simpa using h.symm)) hr0
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [dotProduct_zero] at hc
      linarith
    have hdAd : 0 < d ⬝ᵥ (A *ᵥ d) := by simpa using hA.dotProduct_mulVec_pos hd0
    have hαd : α * (d ⬝ᵥ (A *ᵥ d)) = r ⬝ᵥ r := by rw [hα]; field_simp
    have hi : ∀ v ∈ K k, v ⬝ᵥ r' = 0 := fun v hv => by
      rw [hr', dotProduct_sub, dotProduct_smul, ha v hv, hb v hv, smul_zero, sub_zero]
    have hdr' : d ⬝ᵥ r' = 0 := by
      rw [hr', dotProduct_sub, dotProduct_smul, smul_eq_mul, dotProduct_comm d r, hc, hαd,
        sub_self]
    have hsplit : ∀ v ∈ K (k + 1), ∃ u ∈ K k, ∃ c : ℝ, v = u + c • d := by
      obtain ⟨u', hu', c', hd'⟩ := mem_krylov_succ hd
      have hc' : c' ≠ 0 := by
        rintro rfl
        rw [zero_smul, add_zero] at hd'
        have h := ha d (hd' ▸ hu')
        rw [dotProduct_comm, hc] at h
        linarith
      intro v hv
      obtain ⟨u, hu, c, rfl⟩ := mem_krylov_succ hv
      refine ⟨u - (c / c') • u', Submodule.sub_mem _ hu (Submodule.smul_mem _ _ hu'), c / c', ?_⟩
      rw [hd', smul_add, smul_smul, div_mul_cancel₀ c hc']
      abel
    have ha' : ∀ v ∈ K (k + 1), v ⬝ᵥ r' = 0 := fun v hv => by
      obtain ⟨u, hu, c, rfl⟩ := hsplit v hv
      rw [add_dotProduct, smul_dotProduct, hi u hu, hdr', smul_zero, add_zero]
    have hrr' : r' ⬝ᵥ r = 0 := by rw [dotProduct_comm]; exact ha' r hr
    have h1 : r' ⬝ᵥ r' = -(α * (r' ⬝ᵥ (A *ᵥ d))) := by
      have h : r' ⬝ᵥ (r - α • (A *ᵥ d)) = r' ⬝ᵥ r - α * (r' ⬝ᵥ (A *ᵥ d)) := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
      rw [← hr', hrr'] at h
      rw [h]; ring
    refine ⟨ha', fun v hv => ?_, ?_⟩
    · obtain ⟨u, hu, c, rfl⟩ := hsplit v hv
      have hu' : u ⬝ᵥ (A *ᵥ (r' + β • d)) = 0 := by
        rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hb u hu, smul_zero,
          add_zero, dotProduct_mulVec_symm hAt u r', dotProduct_comm]
        exact ha' _ (mulVec_mem_krylov A _ hu)
      have hdd : d ⬝ᵥ (A *ᵥ (r' + β • d)) = 0 := by
        rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, smul_eq_mul,
          dotProduct_mulVec_symm hAt d r', hβ, h1]
        calc r' ⬝ᵥ (A *ᵥ d) + -(α * (r' ⬝ᵥ (A *ᵥ d))) / (r ⬝ᵥ r) * (d ⬝ᵥ (A *ᵥ d))
            = r' ⬝ᵥ (A *ᵥ d) - r' ⬝ᵥ (A *ᵥ d) * (α * (d ⬝ᵥ (A *ᵥ d))) / (r ⬝ᵥ r) := by ring
          _ = 0 := by rw [hαd, mul_div_assoc, div_self hrr.ne', mul_one, sub_self]
      rw [add_dotProduct, smul_dotProduct, hu', hdd, smul_zero, add_zero]
    · rw [dotProduct_add, dotProduct_smul, dotProduct_comm r' d, hdr', smul_zero, add_zero]

/-- **CG stays in the Krylov space**: `x_k - x₀ ∈ 𝒦_k(A, r₀)`. -/
theorem iterate_x_sub_mem_krylov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (b x₀ : Fin n → ℝ) (k : ℕ) :
    (iterate A b x₀ k).x - x₀ ∈ krylov A (b - A *ᵥ x₀) k :=
  (mem_invariant A b x₀ k).1

/-- **CG minimizes the energy norm of the error over the Krylov space**: for the solution `x⋆`
of `A x⋆ = b`, `‖x_k - x⋆‖_A ≤ ‖x₀ + z - x⋆‖_A` for every `z ∈ 𝒦_k(A, r₀)`. -/
theorem energyNorm_iterate_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {b xs : Fin n → ℝ} (hxs : A *ᵥ xs = b)
    (x₀ : Fin n → ℝ) (k : ℕ) {z : Fin n → ℝ} (hz : z ∈ krylov A (b - A *ᵥ x₀) k) :
    energyNorm A ((iterate A b x₀ k).x - xs) ≤ energyNorm A (x₀ + z - xs) := by
  have hAt := transpose_eq_of_posDef hA
  obtain ⟨hx, -, -, hres⟩ := mem_invariant A b x₀ k
  have horth := (orth_invariant hA b x₀ k).1
  generalize iterate A b x₀ k = s at hx hres horth
  set e := s.x - xs
  set w := z - (s.x - x₀)
  have hw : w ∈ krylov A (b - A *ᵥ x₀) k := Submodule.sub_mem _ hz hx
  have hAe : A *ᵥ e = -s.r := by
    rw [hres, mulVec_sub, hxs]; abel
  have hew : x₀ + z - xs = e + w := by simp only [e, w]; abel
  have hcross : w ⬝ᵥ (A *ᵥ e) = 0 := by rw [hAe, dotProduct_neg, horth w hw, neg_zero]
  have hww : 0 ≤ w ⬝ᵥ (A *ᵥ w) := by simpa using hA.posSemidef.dotProduct_mulVec_nonneg w
  unfold energyNorm
  refine Real.sqrt_le_sqrt ?_
  rw [hew, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct,
    dotProduct_mulVec_symm hAt e w, hcross]
  linarith

/-! ### The Chebyshev bound -/

open Polynomial

private lemma energy_spectral {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (v : Fin n → ℝ) :
    v ⬝ᵥ (A *ᵥ v) =
      ∑ i, hA.eigenvalues i * ((star hA.eigenvectorUnitary *ᵥ v) i) ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp only [← mulVec_mulVec]
  rw [← dotProduct_transpose_mulVec]
  simp only [star, Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def,
    RCLike.ofReal_real_eq_id, id_eq, dotProduct, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private lemma polynomial_diagonal {n : ℕ} (d : Fin n → ℝ) (q : ℝ[X]) :
    aeval (diagonal d) q = diagonal (fun i => q.eval (d i)) := by
  change aeval (diagonalAlgHom ℝ d) q = diagonalAlgHom ℝ (fun i => q.eval (d i))
  rw [aeval_algHom_apply]
  congr 1
  ext i
  simp

private lemma polynomial_coordinates {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (q : ℝ[X]) (v : Fin n → ℝ) :
    star hA.eigenvectorUnitary *ᵥ (aeval A q *ᵥ v) =
      fun i => q.eval (hA.eigenvalues i) * (star hA.eigenvectorUnitary *ᵥ v) i := by
  have hq : aeval A q =
      Unitary.conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (diagonal (fun i => q.eval (hA.eigenvalues i))) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [aeval_algHom_apply]
    congr 1
    simpa only [RCLike.ofReal_real_eq_id, Function.id_comp] using
      polynomial_diagonal hA.eigenvalues q
  rw [hq, Unitary.conjStarAlgAut_apply]
  simp only [← mulVec_mulVec]
  rw [mulVec_mulVec, Unitary.coe_star_mul_self]
  ext i
  simp only [one_mulVec, mulVec_diagonal]

private lemma energy_polynomial_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) (q : ℝ[X]) (v : Fin n → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hq : ∀ i, |q.eval (hA.isHermitian.eigenvalues i)| ≤ B) :
    energyNorm A (aeval A q *ᵥ v) ≤ B * energyNorm A v := by
  have he : (aeval A q *ᵥ v) ⬝ᵥ (A *ᵥ (aeval A q *ᵥ v)) ≤
      B ^ 2 * (v ⬝ᵥ (A *ᵥ v)) := by
    rw [energy_spectral hA.isHermitian, energy_spectral hA.isHermitian,
      polynomial_coordinates, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hl : 0 ≤ hA.isHermitian.eigenvalues i := (hA.eigenvalues_pos i).le
    have hs : (q.eval (hA.isHermitian.eigenvalues i)) ^ 2 ≤ B ^ 2 := by
      have := abs_le.mp (hq i)
      nlinarith
    dsimp
    nlinarith [mul_nonneg hl (sq_nonneg ((star hA.isHermitian.eigenvectorUnitary *ᵥ v) i)),
      mul_le_mul_of_nonneg_right hs
        (mul_nonneg hl (sq_nonneg ((star hA.isHermitian.eigenvectorUnitary *ᵥ v) i)))]
  unfold energyNorm
  calc
    _ ≤ √(B ^ 2 * (v ⬝ᵥ (A *ᵥ v))) := Real.sqrt_le_sqrt he
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

private lemma polynomial_mem_krylov {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (r : Fin n → ℝ) (k : ℕ) (p : ℝ[X]) (hp : p.natDegree < k) :
    aeval A p *ᵥ r ∈ krylov A r k := by
  rw [aeval_eq_sum_range' hp, sum_mulVec]
  apply Submodule.sum_mem
  intro i hi
  rw [smul_mulVec]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, rfl⟩

private lemma polynomial_comparison {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {xs x₀ x : Fin n → ℝ} (k : ℕ) (hk : 0 < k)
    (hmin : ∀ z ∈ krylov A (A *ᵥ (xs - x₀)) k,
      energyNorm A (x - xs) ≤ energyNorm A (x₀ + z - xs))
    (q : ℝ[X]) (hdeg : q.natDegree ≤ k) (hzero : q.eval 0 = 1) :
    energyNorm A (x - xs) ≤ energyNorm A (aeval A q *ᵥ (x₀ - xs)) := by
  let s := (1 - q).divX
  have hs : s.natDegree < k := by
    have hd := natDegree_sub_le (1 : ℝ[X]) q
    simp only [natDegree_one, zero_le, max_eq_right] at hd
    dsimp [s]
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have hf : s * X = 1 - q := by
    have hc : (1 - q).coeff 0 = 0 := by
      rw [coeff_sub, coeff_one_zero, coeff_zero_eq_eval_zero, hzero, sub_self]
    have ht := divX_mul_X_add (1 - q)
    rw [hc, C_0, add_zero] at ht
    exact ht
  have hm := polynomial_mem_krylov A (A *ᵥ (xs - x₀)) k s hs
  have he : x₀ + aeval A s *ᵥ (A *ᵥ (xs - x₀)) - xs =
      aeval A q *ᵥ (x₀ - xs) := by
    have ht := congrArg (fun p : ℝ[X] => aeval A p *ᵥ (x₀ - xs)) hf
    simp only [map_mul, aeval_X, map_sub, map_one, sub_mulVec, one_mulVec,
      ← mulVec_mulVec] at ht
    rw [show xs - x₀ = -(x₀ - xs) by abel, mulVec_neg, mulVec_neg]
    rw [ht]
    abel
  simpa only [he] using hmin _ hm

private lemma chebyshev_denominator {a c : ℝ} (ha : 0 < a) (hac : a < c) (k : ℕ) :
    1 ≤ (2 * ((√(c / a) - 1) / (√(c / a) + 1)) ^ k) *
      (Chebyshev.T ℝ (k : ℤ)).eval ((c + a) / (c - a)) := by
  let r := √(c / a)
  have hr : 1 < r := by
    apply (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr
    simpa only [one_pow] using (lt_div_iff₀ ha).mpr (by simpa using hac)
  have hrsq : r ^ 2 * a = c := by
    dsimp [r]
    rw [Real.sq_sqrt (div_nonneg (ha.trans hac).le ha.le), div_mul_cancel₀ _ ha.ne']
  have hrminus : r - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hr)
  have hrplus : r + 1 ≠ 0 := ne_of_gt (by linarith)
  let t := (r + 1) / (r - 1)
  have ht : 0 < t := div_pos (by linarith) (sub_pos.mpr hr)
  have hcosh : Real.cosh (Real.log t) = (c + a) / (c - a) := by
    rw [Real.cosh_log ht]
    dsimp [t]
    rw [← hrsq]
    have hden : r ^ 2 * a - a ≠ 0 := by rw [hrsq]; exact sub_ne_zero.mpr hac.ne'
    have hden' : r ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp [hden']
    ring
  have hcheb : (Chebyshev.T ℝ (k : ℤ)).eval ((c + a) / (c - a)) =
      Real.cosh ((k : ℝ) * Real.log t) := by
    rw [← hcosh, Chebyshev.T_real_cosh, Int.cast_natCast]
  have hbound : t ^ k ≤
      2 * (Chebyshev.T ℝ (k : ℤ)).eval ((c + a) / (c - a)) := by
    rw [hcheb, Real.cosh_eq, Real.exp_nat_mul, Real.exp_log ht]
    have := Real.exp_pos (-((k : ℝ) * Real.log t))
    linarith
  have hprod : ((r - 1) / (r + 1)) ^ k * t ^ k = 1 := by
    rw [← mul_pow]
    dsimp [t]
    field_simp
    simp
  have hρ : 0 ≤ ((r - 1) / (r + 1)) ^ k := by positivity
  have := mul_le_mul_of_nonneg_left hbound hρ
  rw [hprod] at this
  dsimp [r] at this
  nlinarith

private lemma chebyshev_polynomial {a c : ℝ} (ha : 0 < a) (hac : a < c) (k : ℕ) :
    ∃ q : ℝ[X], q.natDegree ≤ k ∧ q.eval 0 = 1 ∧
      ∀ t ∈ Set.Icc a c,
        |q.eval t| ≤ 2 * ((√(c / a) - 1) / (√(c / a) + 1)) ^ k := by
  let s := (c + a) / (c - a)
  let d := (Chebyshev.T ℝ (k : ℤ)).eval s
  let l : ℝ[X] := C ((c + a) / (c - a)) - C (2 / (c - a)) * X
  let q := C d⁻¹ * (Chebyshev.T ℝ (k : ℤ)).comp l
  have hs : 1 ≤ s := by
    dsimp [s]
    apply (le_div_iff₀ (sub_pos.mpr hac)).mpr
    linarith
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (Chebyshev.one_le_eval_T_real _ hs)
  have hl : l.natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  refine ⟨q, ?_, ?_, ?_⟩
  · apply (natDegree_C_mul_le _ _).trans
    apply natDegree_comp_le.trans
    simpa only [Chebyshev.natDegree_T, Int.natAbs_natCast, mul_one] using
      Nat.mul_le_mul_left k hl
  · dsimp [q, l]
    simp only [eval_mul, eval_C, eval_comp, eval_sub, eval_X, mul_zero, sub_zero]
    exact inv_mul_cancel₀ hd.ne'
  · intro t ht
    have hlt : |l.eval t| ≤ 1 := by
      have he : l.eval t = (c + a - 2 * t) / (c - a) := by
        dsimp [l]
        simp only [eval_sub, eval_C, eval_mul, eval_X]
        ring
      rw [he, abs_le]
      constructor
      · apply (le_div_iff₀ (sub_pos.mpr hac)).mpr
        linarith [ht.2]
      · apply (div_le_iff₀ (sub_pos.mpr hac)).mpr
        linarith [ht.1]
    have hn := Chebyshev.abs_eval_T_real_le_one (k : ℤ) hlt
    have hden := chebyshev_denominator ha hac k
    have hinv : d⁻¹ ≤ 2 * ((√(c / a) - 1) / (√(c / a) + 1)) ^ k := by
      rw [← one_div]
      apply (div_le_iff₀ hd).mpr
      exact hden
    calc
      |q.eval t| = d⁻¹ * |(Chebyshev.T ℝ (k : ℤ)).eval (l.eval t)| := by
        simp only [q, eval_mul, eval_C, eval_comp, abs_mul,
          abs_of_pos (inv_pos.mpr hd)]
      _ ≤ d⁻¹ * 1 := mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hd.le)
      _ ≤ _ := by simpa using hinv

/-- **The Chebyshev bound for Krylov energy minimizers**: if the eigenvalues of `A` lie in
`[a, c]` with `0 < a`, and `x` minimizes `‖· - x⋆‖_A` over `x₀ + 𝒦_k(A, A (x⋆ - x₀))`, then
`‖x - x⋆‖_A ≤ 2 ((√κ - 1) / (√κ + 1))^k ‖x₀ - x⋆‖_A` with `κ = c / a`. -/
theorem energyNorm_le_of_isMin_krylov {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {a c : ℝ} (ha : 0 < a)
    (hlow : ∀ i, a ≤ hA.isHermitian.eigenvalues i) (hup : ∀ i, hA.isHermitian.eigenvalues i ≤ c)
    {xs x₀ x : Fin n → ℝ} (k : ℕ)
    (hmin : ∀ z ∈ krylov A (A *ᵥ (xs - x₀)) k, energyNorm A (x - xs) ≤ energyNorm A (x₀ + z - xs)) :
    energyNorm A (x - xs) ≤
      2 * ((√(c / a) - 1) / (√(c / a) + 1)) ^ k * energyNorm A (x₀ - xs) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [energyNorm, dotProduct]
  by_cases hk : k = 0
  · subst k
    have hm := hmin 0 (Submodule.zero_mem _)
    simp only [add_zero] at hm
    have he : 0 ≤ energyNorm A (x₀ - xs) := Real.sqrt_nonneg _
    simpa only [pow_zero, mul_one] using hm.trans (by nlinarith)
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hacle : a ≤ c := (hlow i).trans (hup i)
  by_cases hac : a < c
  · obtain ⟨q, hdeg, hzero, hq⟩ := chebyshev_polynomial ha hac k
    have hr : 1 ≤ √(c / a) := by
      apply Real.one_le_sqrt.mpr
      apply (le_div_iff₀ ha).mpr
      simpa using hacle
    have hB : 0 ≤ 2 * ((√(c / a) - 1) / (√(c / a) + 1)) ^ k := by positivity
    exact (polynomial_comparison k hkpos hmin q hdeg hzero).trans
      (energy_polynomial_le hA q (x₀ - xs) hB
        (fun j => hq _ ⟨hlow j, hup j⟩))
  · have hca : a = c := le_antisymm hacle (le_of_not_gt hac)
    subst c
    let q : ℝ[X] := 1 - C a⁻¹ * X
    have hdeg : q.natDegree ≤ k := by
      apply le_trans _ hkpos
      apply (natDegree_sub_le _ _).trans
      apply max_le
      · simp
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    have hzero : q.eval 0 = 1 := by simp [q]
    have hq : ∀ j, |q.eval (hA.isHermitian.eigenvalues j)| ≤ 0 := by
      intro j
      have hj : hA.isHermitian.eigenvalues j = a := le_antisymm (hup j) (hlow j)
      simp [q, hj, inv_mul_cancel₀ ha.ne']
    have he : energyNorm A (x - xs) ≤ 0 := by
      simpa only [zero_mul] using
        (polynomial_comparison k hkpos hmin q hdeg hzero).trans
          (energy_polynomial_le hA q (x₀ - xs) le_rfl hq)
    simpa only [div_self ha.ne', Real.sqrt_one, sub_self, zero_div,
      zero_pow hk, mul_zero, zero_mul] using he

/-- **The conjugate gradient error bound**: if the eigenvalues of `A` lie in `[a, c]` with
`0 < a` and `A x⋆ = b`, the CG iterates satisfy
`‖x_k - x⋆‖_A ≤ 2 ((√κ - 1) / (√κ + 1))^k ‖x₀ - x⋆‖_A` with `κ = c / a`. -/
theorem energyNorm_iterate_sub_le {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {a c : ℝ} (ha : 0 < a)
    (hlow : ∀ i, a ≤ hA.isHermitian.eigenvalues i) (hup : ∀ i, hA.isHermitian.eigenvalues i ≤ c)
    {b xs : Fin n → ℝ} (hxs : A *ᵥ xs = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    energyNorm A ((iterate A b x₀ k).x - xs) ≤
      2 * ((√(c / a) - 1) / (√(c / a) + 1)) ^ k * energyNorm A (x₀ - xs) := by
  refine energyNorm_le_of_isMin_krylov hA ha hlow hup k fun z hz => ?_
  rw [mulVec_sub, hxs] at hz
  exact energyNorm_iterate_le hA hxs x₀ k hz

/-- The spectral condition number `λ_max / λ_min` of a positive definite matrix. For `n = 0` it
is `0 / 0 = 0` (no eigenvalues), a junk value; the bound below is stated for `0 < n`. -/
noncomputable def condNum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) : ℝ :=
  (⨆ i, hA.isHermitian.eigenvalues i) / ⨅ i, hA.isHermitian.eigenvalues i

/-- **The conjugate gradient error bound in terms of the condition number** `κ` of `A`:
`‖x_k - x⋆‖_A ≤ 2 ((√κ - 1) / (√κ + 1))^k ‖x₀ - x⋆‖_A`. -/
theorem energyNorm_iterate_sub_le_condNum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hn : 0 < n)
    (hA : A.PosDef) {b xs : Fin n → ℝ}
    (hxs : A *ᵥ xs = b) (x₀ : Fin n → ℝ) (k : ℕ) :
    energyNorm A ((iterate A b x₀ k).x - xs) ≤
      2 * ((√(condNum hA) - 1) / (√(condNum hA) + 1)) ^ k * energyNorm A (x₀ - xs) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := hA.isHermitian.eigenvalues)
  refine energyNorm_iterate_sub_le hA (hi₀ ▸ Matrix.PosDef.eigenvalues_pos hA i₀)
    (fun i => ciInf_le (Set.finite_range _).bddBelow i)
    (fun i => le_ciSup (Set.finite_range _).bddAbove i) hxs x₀ k

end MathlibExt.LinearAlgebra.Matrix.ConjugateGradient
