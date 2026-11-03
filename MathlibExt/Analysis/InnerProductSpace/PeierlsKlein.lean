/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.SchurHorn

public import Mathlib.Analysis.Convex.Birkhoff
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Tactic.Linarith

/-!
# Peierls and Klein inequalities for self-adjoint operators

For a self-adjoint operator `T` on a finite-dimensional complex Hilbert
space, with eigenvalues `λ₁ ≥ ⋯ ≥ λₙ`, and any orthonormal basis `b`,
Peierls' inequality says that the diagonal of `T` in the basis `b` is
less spread out than the eigenvalues, as measured by any convex function:
`∑ i, f (⟪bᵢ, T bᵢ⟫) ≤ ∑ j, f λⱼ`.

Klein's inequality is the first-order form of the same statement: for a
convex differentiable `f` and self-adjoint `S, T`,
`∑ i, (f μᵢ + f' μᵢ (dᵢ - μᵢ)) ≤ ∑ j, f λⱼ`, where `μ` are the
eigenvalues of `S` and `dᵢ = ⟪bᵢ, T bᵢ⟫` is the diagonal of `T` in any
orthonormal basis `b`. When `b` is an eigenbasis of `S` aligned with this
eigenvalue order, the left side is
`tr f(S) + tr (f'(S) (T - S))`, the classical form of Klein's inequality;
in particular, for `f x = x log x` this is the nonnegativity of the
quantum relative entropy (up to the trace terms).

The proof follows the classical route: the diagonal is a doubly
stochastic image of the eigenvalues (Schur's theorem, in
`MathlibExt.Analysis.InnerProductSpace.SchurHorn`), a doubly stochastic
matrix is a convex combination of permutation matrices (Birkhoff's
theorem), and Jensen's inequality applied coordinatewise gives Peierls;
Klein follows from Peierls and the first-order characterization of
convex differentiable functions.

## Main declarations

* `peierls_inequality` : `∑ i, f (re ⟪b i, T (b i)⟫) ≤ ∑ j, f (eigenvalues j)`.
* `klein_inequality` : the first-order (tangent-line) form above.
* `peierls_exp` : Peierls for `f = Real.exp`.
* `klein_sq` : Klein for `f x = x ^ 2`.
* `klein_entropy_tangent` : the entropy tangent bound in any orthonormal basis.
* `klein_entropy` : the aligned quantum-relative-entropy form in the eigenbasis of `S`,
  for positive definite `S` and positive semidefinite `T`.

Companion to the Hilbert-space / spectral material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean` and
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(the spectral theorem and the variational characterization of the
norm); Peierls' and Klein's inequalities are not among the 72 v1 targets.

References: Rudolf Peierls, "On a minimum property of the free energy",
*Physical Review* 54 (1938), 918; Oskar Klein, "Zur quantenmechanischen
Begründung des zweiten Hauptsatzes der Wärmelehre", *Zeitschrift für
Physik* 72 (1931), 767–775.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.PeierlsKlein

open Finset Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The first-order (tangent-line) characterization of a convex
differentiable function: the graph lies above every tangent line. -/
theorem add_deriv_mul_sub_le_of_convexOn {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ} (hf : ConvexOn ℝ s f)
    (hf' : DifferentiableAt ℝ f x) (hx : x ∈ s) (hy : y ∈ s) :
    f x + deriv f x * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hf.deriv_le_slope hx hy hxy hf'
    rw [slope_def_field] at h
    have hpos : (0 : ℝ) < y - x := sub_pos.mpr hxy
    rw [le_div_iff₀ hpos] at h
    linarith
  · simp
  · have h := hf.slope_le_deriv hy hx hxy hf'
    rw [slope_def_field] at h
    have hpos : (0 : ℝ) < x - y := sub_pos.mpr hxy
    rw [div_le_iff₀ hpos] at h
    linarith

/-- **Peierls' inequality**: the diagonal of a self-adjoint operator in
any orthonormal basis is majorized by its eigenvalues, as measured by
any convex function. -/
theorem peierls_inequality {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    (hμ : ∀ j, hT.eigenvalues hn j ∈ s)
    (b : OrthonormalBasis (Fin n) ℂ E) :
    ∑ i, f (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))))
      ≤ ∑ j, f (hT.eigenvalues hn j) := by
  obtain ⟨D, hD, hdiag⟩ :=
    MathlibExt.Analysis.InnerProductSpace.SchurHorn.schur_diagonal_eigenvalues_doublyStochastic
      T hT hn b
  obtain ⟨w, hw0, hw1, hwD⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hD
  set μ : Fin n → ℝ := hT.eigenvalues hn with hμdef
  -- The diagonal entries are convex combinations of the eigenvalues:
  -- the `i`-th diagonal entry is `∑ σ, w σ * μ (σ i)`.
  have hdiag_eq : ∀ i, RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i)))
      = ∑ σ : Equiv.Perm (Fin n), w σ * μ (σ i) := by
    intro i
    have h1 : (D *ᵥ μ) i = ∑ σ : Equiv.Perm (Fin n), w σ * μ (σ i) := by
      rw [← hwD, Matrix.sum_mulVec, Finset.sum_apply]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Matrix.smul_mulVec, Matrix.permMatrix_mulVec]
      simp [Function.comp, smul_eq_mul]
    have h2 := congrFun hdiag i
    rw [h1] at h2
    exact h2
  -- Jensen's inequality, applied coordinatewise.
  have hJensen : ∀ i, f (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))))
      ≤ ∑ σ : Equiv.Perm (Fin n), w σ * f (μ (σ i)) := by
    intro i
    rw [hdiag_eq i]
    have h := hf.map_sum_le (t := Finset.univ) (w := w) (p := fun σ => μ (σ i))
      (fun σ _ => hw0 σ) hw1 (fun σ _ => hμ (σ i))
    simpa only [smul_eq_mul] using h
  calc ∑ i, f (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))))
      ≤ ∑ i, ∑ σ : Equiv.Perm (Fin n), w σ * f (μ (σ i)) :=
        Finset.sum_le_sum fun i _ => hJensen i
    _ = ∑ σ : Equiv.Perm (Fin n), w σ * ∑ j, f (μ j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← Finset.mul_sum]
        congr 1
        exact Equiv.sum_comp σ (fun j => f (μ j))
    _ = ∑ j, f (μ j) := by rw [← Finset.sum_mul, hw1, one_mul]

/-- **Klein's inequality** (sum form): for a convex function `f`
differentiable at the eigenvalues of `S`, the tangent-line sum at the
eigenvalues of `S` evaluated on the diagonal of `T` is at most the sum
of `f` over the eigenvalues of `T`. -/
theorem klein_inequality {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f)
    (hf' : ∀ i, DifferentiableAt ℝ f (hS.eigenvalues hn i))
    (hμT : ∀ j, hT.eigenvalues hn j ∈ s)
    (hμS : ∀ j, hS.eigenvalues hn j ∈ s)
    (b : OrthonormalBasis (Fin n) ℂ E)
    (hd : ∀ i, RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) ∈ s) :
    ∑ i, (f (hS.eigenvalues hn i) + deriv f (hS.eigenvalues hn i) *
        (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) - hS.eigenvalues hn i))
      ≤ ∑ j, f (hT.eigenvalues hn j) := by
  have hP := peierls_inequality hn hT hf hμT b
  have hpt : ∀ i, f (hS.eigenvalues hn i) + deriv f (hS.eigenvalues hn i) *
      (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) - hS.eigenvalues hn i)
        ≤ f (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i)))) := fun i =>
    add_deriv_mul_sub_le_of_convexOn hf (hf' i) (hμS i) (hd i)
  calc ∑ i, (f (hS.eigenvalues hn i) + deriv f (hS.eigenvalues hn i) *
        (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) - hS.eigenvalues hn i))
      ≤ ∑ i, f (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i)))) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ ≤ ∑ j, f (hT.eigenvalues hn j) := hP

/-- Peierls' inequality for the exponential function. -/
theorem peierls_exp {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (b : OrthonormalBasis (Fin n) ℂ E) :
    ∑ i, Real.exp (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))))
      ≤ ∑ j, Real.exp (hT.eigenvalues hn j) :=
  peierls_inequality hn hT convexOn_exp (fun _ => Set.mem_univ _) b

/-- Klein's inequality for `f x = x ^ 2`. -/
theorem klein_sq {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (b : OrthonormalBasis (Fin n) ℂ E) :
    ∑ i, ((hS.eigenvalues hn i) ^ 2 + 2 * hS.eigenvalues hn i *
        (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) - hS.eigenvalues hn i))
      ≤ ∑ j, (hT.eigenvalues hn j) ^ 2 := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := even_two.convexOn_pow
  have hdiff : ∀ i, DifferentiableAt ℝ (fun x : ℝ => x ^ 2) (hS.eigenvalues hn i) :=
    fun _ => differentiableAt_id.pow 2
  have h := klein_inequality hn hT hS hconv hdiff
    (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) b (fun _ => Set.mem_univ _)
  have hderiv : ∀ x : ℝ, deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
    intro x
    simp
  simpa only [hderiv] using h

/-- Eigenvalues of a positive semidefinite symmetric operator are
nonnegative: an eigenvalue is the Rayleigh quotient at a unit
eigenvector. -/
theorem eigenvalues_nonneg_of_forall_nonneg_inner {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hTpos : ∀ x, 0 ≤ RCLike.re (inner (𝕜 := ℂ) x (T x))) (j : Fin n) :
    0 ≤ hT.eigenvalues hn j := by
  set e := hT.eigenvectorBasis hn j with he_def
  have he : T e = ((hT.eigenvalues hn j : ℂ)) • e := hT.apply_eigenvectorBasis hn j
  have hnorm : ‖e‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.norm_eq_one j
  have h := hTpos e
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  simp only [hnorm, one_pow, RCLike.ofReal_one, mul_one] at h
  exact h

/-- Eigenvalues of a positive definite symmetric operator are positive. -/
theorem eigenvalues_pos_of_forall_pos_inner {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric)
    (hTpos : ∀ x, x ≠ 0 → 0 < RCLike.re (inner (𝕜 := ℂ) x (T x))) (j : Fin n) :
    0 < hT.eigenvalues hn j := by
  set e := hT.eigenvectorBasis hn j with he_def
  have he : T e = ((hT.eigenvalues hn j : ℂ)) • e := hT.apply_eigenvectorBasis hn j
  have hnorm : ‖e‖ = 1 := (hT.eigenvectorBasis hn).orthonormal.norm_eq_one j
  have hne : e ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  have h := hTpos e hne
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  simp only [hnorm, one_pow, RCLike.ofReal_one, mul_one] at h
  exact h

/-- The entropy tangent bound in an arbitrary orthonormal basis. Its diagonal entries
need not align with the eigenvalues of `S`; `klein_entropy` supplies the aligned
quantum-relative-entropy form. -/
theorem klein_entropy_tangent {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hTpos : ∀ x, 0 ≤ RCLike.re (inner (𝕜 := ℂ) x (T x)))
    (hSpos : ∀ x, x ≠ 0 → 0 < RCLike.re (inner (𝕜 := ℂ) x (S x)))
    (b : OrthonormalBasis (Fin n) ℂ E) :
    ∑ i, (hS.eigenvalues hn i * Real.log (hS.eigenvalues hn i) +
        (Real.log (hS.eigenvalues hn i) + 1) *
        (RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) - hS.eigenvalues hn i))
      ≤ ∑ j, hT.eigenvalues hn j * Real.log (hT.eigenvalues hn j) := by
  have hμT : ∀ j, hT.eigenvalues hn j ∈ Set.Ici (0 : ℝ) :=
    fun j => eigenvalues_nonneg_of_forall_nonneg_inner hn hT hTpos j
  have hμSpos : ∀ j, 0 < hS.eigenvalues hn j :=
    fun j => eigenvalues_pos_of_forall_pos_inner hn hS hSpos j
  have hμS : ∀ j, hS.eigenvalues hn j ∈ Set.Ici (0 : ℝ) :=
    fun j => (hμSpos j).le
  have hd : ∀ i, RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) ∈ Set.Ici (0 : ℝ) :=
    fun i => hTpos (b i)
  have hdiff : ∀ i, DifferentiableAt ℝ (fun x : ℝ => x * Real.log x)
      (hS.eigenvalues hn i) :=
    fun i => (Real.hasDerivAt_mul_log (ne_of_gt (hμSpos i))).differentiableAt
  have h := klein_inequality hn hT hS Real.convexOn_mul_log hdiff hμT hμS b hd
  have hderiv : ∀ i, deriv (fun x : ℝ => x * Real.log x) (hS.eigenvalues hn i)
      = Real.log (hS.eigenvalues hn i) + 1 :=
    fun i => Real.deriv_mul_log (ne_of_gt (hμSpos i))
  simpa only [hderiv] using h

/-- Klein's entropy inequality in the eigenbasis of `S`. The eigenvalue at index `i`
is paired with its eigenvector, so this is the quantum-relative-entropy form up to
the trace terms. In particular, its tangent correction vanishes when `T = S`. -/
theorem klein_entropy {n : ℕ} (hn : Module.finrank ℂ E = n)
    {T S : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hTpos : ∀ x, 0 ≤ RCLike.re (inner (𝕜 := ℂ) x (T x)))
    (hSpos : ∀ x, x ≠ 0 → 0 < RCLike.re (inner (𝕜 := ℂ) x (S x))) :
    ∑ i, (hS.eigenvalues hn i * Real.log (hS.eigenvalues hn i) +
        (Real.log (hS.eigenvalues hn i) + 1) *
        (RCLike.re (inner (𝕜 := ℂ) (hS.eigenvectorBasis hn i)
          (T (hS.eigenvectorBasis hn i))) - hS.eigenvalues hn i))
      ≤ ∑ j, hT.eigenvalues hn j * Real.log (hT.eigenvalues hn j) :=
  klein_entropy_tangent hn hT hS hTpos hSpos (hS.eigenvectorBasis hn)

end MathlibExt.Analysis.InnerProductSpace.PeierlsKlein
