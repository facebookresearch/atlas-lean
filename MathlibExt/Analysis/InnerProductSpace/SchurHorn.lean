/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Convex.DoublyStochasticMatrix
public import Mathlib.Analysis.InnerProductSpace.Spectrum

@[expose] public section

/-!
# Schur's theorem on diagonals of self-adjoint operators

The real diagonal of a self-adjoint operator in an orthonormal basis is a doubly stochastic image
of its eigenvalues (the Schur direction of the Schur-Horn theorem).
-/

namespace MathlibExt.Analysis.InnerProductSpace.SchurHorn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/--
**Schur's theorem on diagonals of self-adjoint operators.** Let $E$ be a complex inner product
space of finite dimension $n$, let $T : E \to E$ be a linear operator that is symmetric, that is,
$\langle T x, y \rangle = \langle x, T y \rangle$ for all $x, y \in E$, let
$\lambda_1, \dots, \lambda_n$ be the eigenvalues of $T$ listed with multiplicity, and let
$b_1, \dots, b_n$ be an orthonormal basis of $E$. Then there is a doubly stochastic real
$n \times n$ matrix $D$ such that $\operatorname{Re} \langle b_i, T b_i \rangle =
\sum_{j=1}^n D_{ij} \lambda_j$ for every $i$.

Source: I. Schur, 1923, Über eine Klasse von Mittelbildungen mit Anwendungen auf die
Determinantentheorie; A. Horn, Doubly Stochastic Matrices and the Diagonal of a Rotation Matrix,
Amer. J. Math. 76 (1954), 620–630, DOI 10.2307/2372705.
Proves `Wanted` entry `schur_diagonal_eigenvalues_doublyStochastic`.
-/
theorem schur_diagonal_eigenvalues_doublyStochastic
    {n : ℕ} (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (hn : Module.finrank ℂ E = n)
    (b : OrthonormalBasis (Fin n) ℂ E) :
    ∃ D : Matrix (Fin n) (Fin n) ℝ,
      D ∈ doublyStochastic ℝ (Fin n) ∧
        (fun i => RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) : Fin n → ℝ) =
          D.mulVec (hT.eigenvalues hn) := by
  set e : OrthonormalBasis (Fin n) ℂ E := hT.eigenvectorBasis hn
  set μ : Fin n → ℝ := hT.eigenvalues hn
  set c : Fin n → Fin n → ℂ := fun i j => (e.repr (b i)).ofLp j
  set D : Matrix (Fin n) (Fin n) ℝ := fun i j => Complex.normSq (c i j)
  have hexpand : ∀ i, (∑ j, c i j • e j) = b i := fun i => e.sum_repr (b i)
  have heig : ∀ j, T (e j) = (((μ j : ℝ)) : ℂ) • e j :=
    fun j => hT.apply_eigenvectorBasis hn j
  have hTb : ∀ i, T (b i) = ∑ j, ((((μ j : ℝ)) : ℂ) * c i j) • e j := by
    intro i
    rw [← hexpand i, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, heig j, ← mul_smul, mul_comm (c i j)]
  have hinner : ∀ i, inner (𝕜 := ℂ) (b i) (T (b i))
      = ∑ j, (starRingEnd ℂ) (c i j) * ((((μ j : ℝ)) : ℂ) * c i j) := by
    intro i
    rw [hTb i, ← hexpand i]
    exact e.orthonormal.inner_sum _ _ Finset.univ
  have hparse : ∀ (f : OrthonormalBasis (Fin n) ℂ E) (x : E),
      ∑ j, Complex.normSq ((f.repr x).ofLp j) = ‖x‖ ^ 2 := by
    intro f x
    have h1 : ‖f.repr x‖ = ‖x‖ := f.repr.norm_map x
    have h2 : ‖f.repr x‖ = √(∑ j, ‖(f.repr x).ofLp j‖ ^ 2) :=
      EuclideanSpace.norm_eq _
    have hnn : 0 ≤ ∑ j, ‖(f.repr x).ofLp j‖ ^ 2 :=
      Finset.sum_nonneg (fun j _ => by positivity)
    have h3 : ∑ j, ‖(f.repr x).ofLp j‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← h1, h2, Real.sq_sqrt hnn]
    simp_rw [Complex.normSq_eq_norm_sq]
    exact h3
  have hrow : ∀ i, ∑ j, D i j = 1 := by
    intro i
    have h1 : (∑ j, D i j) = ∑ j, Complex.normSq ((e.repr (b i)).ofLp j) := rfl
    rw [h1, hparse e (b i), b.orthonormal.norm_eq_one i, one_pow]
  have hcol : ∀ j, ∑ i, D i j = 1 := by
    intro j
    have hstep : ∀ i, D i j = Complex.normSq ((b.repr (e j)).ofLp i) := by
      intro i
      have h1 : inner (𝕜 := ℂ) (e j) (b i)
          = (starRingEnd ℂ) (inner (𝕜 := ℂ) (b i) (e j)) :=
        (inner_conj_symm (e j) (b i)).symm
      have h2 : c i j = inner (𝕜 := ℂ) (e j) (b i) :=
        e.repr_apply_apply (b i) j
      change Complex.normSq (c i j) = _
      rw [h2, h1, ← b.repr_apply_apply (e j) i, Complex.normSq_conj]
    simp only [hstep]
    rw [hparse b (e j), e.orthonormal.norm_eq_one j, one_pow]
  have hdiag : ∀ i, RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i)))
      = ∑ j, D i j * μ j := by
    intro i
    have hterm : ∀ j, (starRingEnd ℂ) (c i j) * ((((μ j : ℝ)) : ℂ) * c i j)
        = ((((D i j * μ j : ℝ))) : ℂ) := by
      intro j
      change (starRingEnd ℂ) (c i j) * ((((μ j : ℝ)) : ℂ) * c i j)
        = ((((Complex.normSq (c i j) * μ j : ℝ))) : ℂ)
      calc (starRingEnd ℂ) (c i j) * ((((μ j : ℝ)) : ℂ) * c i j)
          = ((((μ j : ℝ)) : ℂ)) * ((c i j) * (starRingEnd ℂ) (c i j)) := by ring
        _ = ((((μ j : ℝ)) : ℂ)) * ((((Complex.normSq (c i j) : ℝ))) : ℂ) := by
            rw [Complex.mul_conj]
        _ = ((((Complex.normSq (c i j) * μ j : ℝ))) : ℂ) := by
            push_cast
            ring
    have hsum : inner (𝕜 := ℂ) (b i) (T (b i))
        = ((((∑ j, D i j * μ j : ℝ))) : ℂ) := by
      have hcast : ((((∑ j, D i j * μ j : ℝ))) : ℂ)
          = ∑ j, ((((D i j * μ j : ℝ))) : ℂ) := by
        push_cast
        rfl
      rw [hinner i, hcast]
      exact Finset.sum_congr rfl fun j _ => hterm j
    rw [hsum]
    simp
  refine ⟨D, ?_, ?_⟩
  · rw [mem_doublyStochastic_iff_sum]
    exact ⟨fun i j => Complex.normSq_nonneg _, hrow, hcol⟩
  · funext i
    show RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) = (D.mulVec μ) i
    exact (hdiag i).trans rfl

end MathlibExt.Analysis.InnerProductSpace.SchurHorn
