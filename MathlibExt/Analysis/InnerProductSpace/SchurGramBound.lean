/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.Analysis.Matrix.PosDef

/-!
# Schur-multiplier bound for Gram matrices

For a matrix `A` and two families of vectors `u v : X → E` indexed by a finite
type `X`, with values in an inner-product space `E` over `ℂ`, the Hadamard
(entrywise) product of `A` with the Gram matrix `fun x y => ⟪u x, v y⟫`
satisfies the operator-norm bound
`‖A ⊙ Gram(u, v)‖ ≤ ‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖)`.

The proof factors each coordinate of the Hadamard-Gram `mulVec` through an
inner product, applies Cauchy-Schwarz per coordinate, and bounds the remaining
spectral sum by a key estimate: `A` acting on `E`-valued families is bounded
by `‖A‖`, proved by identifying the norm sum with the quadratic form of
`Aᴴ * A` and diagonalizing via the spectral theorem for Hermitian matrices.

## Main statements

* `norm_hadamard_gram_factor_le`: `‖A ⊙ Gram(u, v)‖ ≤ ‖A‖ * sup ‖u‖ * sup ‖v‖`.
* `keyEstimate`: the spectral estimate `∑ x, ‖∑ y, A x y • z y‖ ^ 2 ≤
  ‖A‖ ^ 2 * ∑ y, ‖z y‖ ^ 2` behind the bound.
-/

@[expose] public section

open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators

namespace MathlibExt.Analysis.InnerProductSpace.SchurGramBound

/-- Squaring is monotone on nonnegative reals. -/
private theorem sq_le_sq_of_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    a ^ 2 ≤ b ^ 2 :=
  pow_le_pow_left₀ ha hab 2

/-- A norm is bounded by the supremum of norms. -/
private theorem le_iSup_norm {X E : Type*} [Fintype X]
    [NormedAddCommGroup E] (u : X → E) (x : X) : ‖u x‖ ≤ ⨆ x, ‖u x‖ := by
  have hfin : (Set.range fun x => ‖u x‖).Finite := Set.finite_range _
  exact le_ciSup hfin.bddAbove x

/-- The supremum of norms is nonnegative. -/
private theorem iSup_norm_nonneg {X E : Type*} [NormedAddCommGroup E] (u : X → E) :
    0 ≤ ⨆ x, ‖u x‖ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- The squared norm on Euclidean space is the sum of squared coordinate norms. -/
private theorem euclidean_norm_sq {𝕜 X : Type*} [RCLike 𝕜] [Fintype X]
    (s : EuclideanSpace 𝕜 X) : ‖s‖ ^ 2 = ∑ x, ‖s.ofLp x‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq s

/-- Completeness relation for the eigenvectors of a Hermitian matrix. -/
private theorem eigen_completeness {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℂ) (hM : M.IsHermitian) (y1 y2 : X) :
    (∑ k, (hM.eigenvectorBasis k).ofLp y1 *
        star ((hM.eigenvectorBasis k).ofLp y2)) = (if y1 = y2 then 1 else 0) := by
  have hterm : ∀ k : X, (hM.eigenvectorBasis k).ofLp y1 *
        star ((hM.eigenvectorBasis k).ofLp y2)
      = inner ℂ (EuclideanSpace.single y1 (1 : ℂ)) (hM.eigenvectorBasis k)
        * inner ℂ (hM.eigenvectorBasis k) (EuclideanSpace.single y2 (1 : ℂ)) := by
    intro k
    rw [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
    simp only [map_one, one_mul, starRingEnd_apply]
  have hrhs : inner ℂ (EuclideanSpace.single y1 (1 : ℂ))
        (EuclideanSpace.single y2 (1 : ℂ))
      = (if y1 = y2 then (1 : ℂ) else 0) := by
    rw [EuclideanSpace.inner_single_left, PiLp.single_apply, map_one, one_mul]
  calc (∑ k, (hM.eigenvectorBasis k).ofLp y1 *
          star ((hM.eigenvectorBasis k).ofLp y2))
      = ∑ k, inner ℂ (EuclideanSpace.single y1 (1 : ℂ)) (hM.eigenvectorBasis k)
          * inner ℂ (hM.eigenvectorBasis k) (EuclideanSpace.single y2 (1 : ℂ)) :=
        Finset.sum_congr rfl (fun k _ => hterm k)
    _ = inner ℂ (EuclideanSpace.single y1 (1 : ℂ))
          (EuclideanSpace.single y2 (1 : ℂ)) :=
        (hM.eigenvectorBasis).sum_inner_mul_inner _ _
    _ = (if y1 = y2 then (1 : ℂ) else 0) := hrhs

/-- A Hermitian eigenvalue is bounded by the operator norm. -/
private theorem eigen_le_norm {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℂ) (hM : M.IsHermitian) (k : X) :
    hM.eigenvalues k ≤ ‖M‖ := by
  have heig := hM.mulVec_eigenvectorBasis k
  have hnorm1 : ‖hM.eigenvectorBasis k‖ = 1 := hM.eigenvectorBasis.orthonormal.1 k
  have hle := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X) M).le_opNorm
    (hM.eigenvectorBasis k)
  rw [← Matrix.cstar_norm_def, hnorm1, mul_one] at hle
  have hofLp : (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X) M (hM.eigenvectorBasis k)).ofLp
      = (hM.eigenvalues k • (hM.eigenvectorBasis k).ofLp) := by
    rw [Matrix.ofLp_toEuclideanCLM]
    exact heig
  have hsmul : (hM.eigenvalues k : ℝ) • (hM.eigenvectorBasis k).ofLp
      = ((hM.eigenvalues k : ℝ) • hM.eigenvectorBasis k).ofLp := by
    rw [WithLp.ofLp_smul]
  have hvec : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X) M (hM.eigenvectorBasis k)
      = (hM.eigenvalues k : ℝ) • hM.eigenvectorBasis k := by
    apply WithLp.ofLp_injective
    rw [hofLp, hsmul]
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X) M (hM.eigenvectorBasis k)‖
      = |hM.eigenvalues k| := by
    rw [hvec, norm_smul, hnorm1, mul_one, Real.norm_eq_abs]
  rw [hnorm] at hle
  exact le_trans (le_abs_self _) hle

/-- Expansion of `⟪q, q⟫` for eigenbasis coefficients. -/
private theorem eigen_q_inner {X E : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : Matrix X X ℂ) (hM : M.IsHermitian) (z : X → E) (k : X) :
    inner ℂ (∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y)
        (∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y) =
      ∑ y1, ∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
        star ((hM.eigenvectorBasis k).ofLp y2) *
        inner ℂ (z y1) (z y2) := by
  have h1 : inner ℂ (∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y)
        (∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y) =
      ∑ y1, ∑ y2, inner ℂ (star ((hM.eigenvectorBasis k).ofLp y1) • z y1)
        (star ((hM.eigenvectorBasis k).ofLp y2) • z y2) := by
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro y1 _
    exact inner_sum _ _ _
  have h2 : ∀ y1 y2 : X,
      inner ℂ (star ((hM.eigenvectorBasis k).ofLp y1) • z y1)
          (star ((hM.eigenvectorBasis k).ofLp y2) • z y2) =
        (hM.eigenvectorBasis k).ofLp y1 *
          star ((hM.eigenvectorBasis k).ofLp y2) *
          inner ℂ (z y1) (z y2) := by
    intro y1 y2
    rw [inner_smul_left, inner_smul_right, starRingEnd_apply, star_star,
      mul_assoc]
  rw [h1]
  apply Finset.sum_congr rfl
  intro y1 _
  apply Finset.sum_congr rfl
  intro y2 _
  exact h2 y1 y2

/-- Parseval identity for `E`-valued families in the eigenbasis. -/
private theorem eigen_parseval {X E : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : Matrix X X ℂ) (hM : M.IsHermitian) (z : X → E) :
    (∑ k, (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2) =
      ∑ y, (‖z y‖ : ℂ) ^ 2 := by
  have hq : ∀ k : X, (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2 =
      ∑ y1, ∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
        star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2) := by
    intro k
    have e : (⟪∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y,
        ∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y⟫_ℂ) =
        (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2 :=
      inner_self_eq_norm_sq_to_K _
    rw [← e]
    exact eigen_q_inner M hM z k
  have hswap : (∑ k, ∑ y1, ∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
        star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2)) =
      ∑ y1, ∑ y2, (∑ k, (hM.eigenvectorBasis k).ofLp y1 *
        star ((hM.eigenvectorBasis k).ofLp y2)) * inner ℂ (z y1) (z y2) := by
    conv => lhs; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y1 _
    conv => lhs; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y2 _
    rw [Finset.sum_mul]
  have hdelta : ∀ y1 y2 : X, (∑ k, (hM.eigenvectorBasis k).ofLp y1 *
        star ((hM.eigenvectorBasis k).ofLp y2)) * inner ℂ (z y1) (z y2) =
      (if y1 = y2 then inner ℂ (z y1) (z y2) else 0) := by
    intro y1 y2
    rw [eigen_completeness M hM y1 y2, ite_mul, one_mul, zero_mul]
  have hcollapse : (∑ y1, ∑ y2,
        (if y1 = y2 then inner ℂ (z y1) (z y2) else 0)) =
      ∑ y, (‖z y‖ : ℂ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro y1 _
    have hite : (∑ y2, (if y1 = y2 then inner ℂ (z y1) (z y2) else 0)) =
        inner ℂ (z y1) (z y1) := by
      rw [Finset.sum_ite_eq]
      simp
    rw [hite]
    exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (z y1)
  calc (∑ k, (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2)
      = ∑ k, ∑ y1, ∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
          star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2) :=
        Finset.sum_congr rfl (fun k _ => hq k)
    _ = ∑ y1, ∑ y2, (∑ k, (hM.eigenvectorBasis k).ofLp y1 *
          star ((hM.eigenvectorBasis k).ofLp y2)) * inner ℂ (z y1) (z y2) :=
        hswap
    _ = ∑ y1, ∑ y2, (if y1 = y2 then inner ℂ (z y1) (z y2) else 0) := by
        apply Finset.sum_congr rfl
        intro y1 _
        apply Finset.sum_congr rfl
        intro y2 _
        exact hdelta y1 y2
    _ = ∑ y, (‖z y‖ : ℂ) ^ 2 := hcollapse

/-- Spectral expansion of Hermitian matrix entries. -/
private theorem eigen_entry {X : Type*} [Fintype X] [DecidableEq X]
    (M : Matrix X X ℂ) (hM : M.IsHermitian) (y1 y2 : X) :
    M y1 y2 = ∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
      ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2)) := by
  have hlam : ∀ k : X, ((hM.eigenvalues k : ℝ) : ℂ) *
      (hM.eigenvectorBasis k).ofLp y1 =
      ∑ j, M y1 j * (hM.eigenvectorBasis k).ofLp j := by
    intro k
    have e := congrFun (hM.mulVec_eigenvectorBasis k) y1
    rw [Pi.smul_apply, RCLike.real_smul_eq_coe_mul] at e
    exact e.symm
  have hexpand : (∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
        ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) =
      ∑ k, ∑ j, M y1 j * ((hM.eigenvectorBasis k).ofLp j *
        star ((hM.eigenvectorBasis k).ofLp y2)) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← mul_assoc, hlam k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_assoc]
  have hswap : (∑ k, ∑ j, M y1 j * ((hM.eigenvectorBasis k).ofLp j *
        star ((hM.eigenvectorBasis k).ofLp y2))) =
      ∑ j, M y1 j * (∑ k, (hM.eigenvectorBasis k).ofLp j *
        star ((hM.eigenvectorBasis k).ofLp y2)) := by
    conv => lhs; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  have hfinal : (∑ j, M y1 j * (∑ k, (hM.eigenvectorBasis k).ofLp j *
        star ((hM.eigenvectorBasis k).ofLp y2))) = M y1 y2 := by
    have hstep : ∀ j : X, M y1 j * (∑ k, (hM.eigenvectorBasis k).ofLp j *
        star ((hM.eigenvectorBasis k).ofLp y2)) =
        (if j = y2 then M y1 j else 0) := by
      intro j
      rw [eigen_completeness M hM j y2]
      split_ifs with h
      · rw [mul_one]
      · rw [mul_zero]
    have hsum : (∑ j, M y1 j * (∑ k, (hM.eigenvectorBasis k).ofLp j *
          star ((hM.eigenvectorBasis k).ofLp y2))) =
        ∑ j, (if j = y2 then M y1 j else 0) :=
      Finset.sum_congr rfl (fun j _ => hstep j)
    rw [hsum, Finset.sum_ite_eq']
    simp
  calc M y1 y2
      = ∑ j, M y1 j * (∑ k, (hM.eigenvectorBasis k).ofLp j *
          star ((hM.eigenvectorBasis k).ofLp y2)) := hfinal.symm
    _ = ∑ k, ∑ j, M y1 j * ((hM.eigenvectorBasis k).ofLp j *
          star ((hM.eigenvectorBasis k).ofLp y2)) := hswap.symm
    _ = ∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2)) := hexpand.symm

/-- Spectral expansion of the `E`-valued quadratic form. -/
private theorem eigen_quad {X E : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : Matrix X X ℂ) (hM : M.IsHermitian) (z : X → E) :
    (∑ y1, ∑ y2, M y1 y2 * inner ℂ (z y1) (z y2)) =
      ∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
        (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2 := by
  have hsub : (∑ y1, ∑ y2, M y1 y2 * inner ℂ (z y1) (z y2)) =
      ∑ y1, ∑ y2, (∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
        ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
        inner ℂ (z y1) (z y2) := by
    apply Finset.sum_congr rfl
    intro y1 _
    apply Finset.sum_congr rfl
    intro y2 _
    rw [eigen_entry M hM y1 y2]
  have hswap : (∑ y1, ∑ y2, ∑ k, (((hM.eigenvalues k : ℝ) : ℂ) *
        ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
        inner ℂ (z y1) (z y2)) =
      ∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
        (∑ y1, ∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
          star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2)) := by
    have hsw1 : (∑ y1, ∑ y2, ∑ k, (((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
          inner ℂ (z y1) (z y2)) =
        ∑ y1, ∑ k, ∑ y2, (((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
          inner ℂ (z y1) (z y2) := by
      apply Finset.sum_congr rfl
      intro y1 _
      conv => lhs; rw [Finset.sum_comm]
    rw [hsw1]
    conv => lhs; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    have hfac : ∀ y1 y2 : X, (((hM.eigenvalues k : ℝ) : ℂ) *
        ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
        inner ℂ (z y1) (z y2) =
        ((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2)) := by
      intro y1 y2
      rw [mul_assoc]
    have hsum : (∑ y1, ∑ y2, (((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
          inner ℂ (z y1) (z y2)) =
        ∑ y1, ∑ y2, ((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2)) := by
      apply Finset.sum_congr rfl
      intro y1 _
      apply Finset.sum_congr rfl
      intro y2 _
      exact hfac y1 y2
    rw [hsum]
    have hfactor : ∀ y1 : X, (∑ y2, ((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2))) =
        ((hM.eigenvalues k : ℝ) : ℂ) *
          (∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2)) := by
      intro y1
      rw [Finset.mul_sum]
    have hsum2 : (∑ y1, ∑ y2, ((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2))) =
        ∑ y1, ((hM.eigenvalues k : ℝ) : ℂ) *
          (∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2)) :=
      Finset.sum_congr rfl (fun y1 _ => hfactor y1)
    rw [hsum2, ← Finset.mul_sum]
  calc (∑ y1, ∑ y2, M y1 y2 * inner ℂ (z y1) (z y2))
      = ∑ y1, ∑ y2, (∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
          inner ℂ (z y1) (z y2) := hsub
    _ = ∑ y1, ∑ y2, ∑ k, (((hM.eigenvalues k : ℝ) : ℂ) *
          ((hM.eigenvectorBasis k).ofLp y1 * star ((hM.eigenvectorBasis k).ofLp y2))) *
          inner ℂ (z y1) (z y2) := by
        apply Finset.sum_congr rfl
        intro y1 _
        apply Finset.sum_congr rfl
        intro y2 _
        rw [Finset.sum_mul]
    _ = ∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
          (∑ y1, ∑ y2, (hM.eigenvectorBasis k).ofLp y1 *
            star ((hM.eigenvectorBasis k).ofLp y2) * inner ℂ (z y1) (z y2)) :=
        hswap
    _ = ∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
          (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        have e : (⟪∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y,
            ∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y⟫_ℂ) =
            (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2 :=
          inner_self_eq_norm_sq_to_K _
        rw [← e]
        exact (eigen_q_inner M hM z k).symm

/-- The norm sum as an `E`-valued quadratic form in `Aᴴ * A`. -/
private theorem quad_lhs {X E : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Matrix X X ℂ) (z : X → E) :
    (∑ x, (‖∑ y, A x y • z y‖ : ℂ) ^ 2) =
      ∑ y1, ∑ y2, (Aᴴ * A) y1 y2 * inner ℂ (z y1) (z y2) := by
  have hw : ∀ x : X, (‖∑ y, A x y • z y‖ : ℂ) ^ 2 =
      ∑ y1, ∑ y2, star (A x y1) * A x y2 * inner ℂ (z y1) (z y2) := by
    intro x
    have e : (⟪∑ y, A x y • z y, ∑ y, A x y • z y⟫_ℂ) =
        (‖∑ y, A x y • z y‖ : ℂ) ^ 2 :=
      inner_self_eq_norm_sq_to_K _
    rw [← e]
    have h1 : inner ℂ (∑ y, A x y • z y) (∑ y, A x y • z y) =
        ∑ y1, ∑ y2, inner ℂ (A x y1 • z y1) (A x y2 • z y2) := by
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro y1 _
      exact inner_sum _ _ _
    have h2 : ∀ y1 y2 : X, inner ℂ (A x y1 • z y1) (A x y2 • z y2) =
        star (A x y1) * A x y2 * inner ℂ (z y1) (z y2) := by
      intro y1 y2
      rw [inner_smul_left, inner_smul_right, starRingEnd_apply, mul_assoc]
    rw [h1]
    apply Finset.sum_congr rfl
    intro y1 _
    apply Finset.sum_congr rfl
    intro y2 _
    exact h2 y1 y2
  have hM : ∀ y1 y2 : X, (∑ x, star (A x y1) * A x y2) = (Aᴴ * A) y1 y2 := by
    intro y1 y2
    have e : (Aᴴ * A) y1 y2 = ∑ x, (Aᴴ) y1 x * A x y2 := Matrix.mul_apply
    rw [e]
    apply Finset.sum_congr rfl
    intro x _
    have c : (Aᴴ) y1 x = star (A x y1) := Matrix.conjTranspose_apply _ _ _
    rw [c]
  have hswap : (∑ x, ∑ y1, ∑ y2, star (A x y1) * A x y2 * inner ℂ (z y1) (z y2)) =
      ∑ y1, ∑ y2, (Aᴴ * A) y1 y2 * inner ℂ (z y1) (z y2) := by
    have hinner : ∀ y1 y2 : X,
        (∑ x, star (A x y1) * A x y2 * inner ℂ (z y1) (z y2)) =
        (∑ x, star (A x y1) * A x y2) * inner ℂ (z y1) (z y2) := by
      intro y1 y2
      rw [Finset.sum_mul]
    conv => lhs; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y1 _
    conv => lhs; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y2 _
    rw [← hM y1 y2]
    exact hinner y1 y2
  calc (∑ x, (‖∑ y, A x y • z y‖ : ℂ) ^ 2)
      = ∑ x, ∑ y1, ∑ y2, star (A x y1) * A x y2 * inner ℂ (z y1) (z y2) :=
        Finset.sum_congr rfl (fun x _ => hw x)
    _ = ∑ y1, ∑ y2, (Aᴴ * A) y1 y2 * inner ℂ (z y1) (z y2) := hswap

/-- Spectral key estimate: `A ⊗ Id` is bounded by `‖A‖`. -/
theorem keyEstimate {X E : Type*} [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Matrix X X ℂ) (z : X → E) :
    ∑ x, ‖∑ y, A x y • z y‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ y, ‖z y‖ ^ 2 := by
  have hM : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  have hspec : ((∑ x, ‖∑ y, A x y • z y‖ ^ 2 : ℝ) : ℂ) =
      ∑ k, ((hM.eigenvalues k : ℝ) : ℂ) *
        (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ : ℂ) ^ 2 := by
    have ql := quad_lhs A z
    have eq := eigen_quad (Aᴴ * A) hM z
    exact_mod_cast ql.trans eq
  have hreal : (∑ x, ‖∑ y, A x y • z y‖ ^ 2) =
      ∑ k, hM.eigenvalues k *
        (‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ ^ 2) := by
    exact_mod_cast hspec
  have hC : ∀ k : X, hM.eigenvalues k ≤ ‖A‖ ^ 2 := by
    intro k
    have e1 := eigen_le_norm (Aᴴ * A) hM k
    have e2 : ‖Aᴴ * A‖ = ‖A‖ ^ 2 := by
      have c := CStarRing.norm_star_mul_self (x := A)
      rw [Matrix.star_eq_conjTranspose] at c
      rw [c]
      ring
    rw [e2] at e1
    exact e1
  have hparse : (∑ k, ‖∑ y, star ((hM.eigenvectorBasis k).ofLp y) • z y‖ ^ 2) =
      ∑ y, ‖z y‖ ^ 2 := by
    have p := eigen_parseval (Aᴴ * A) hM z
    exact_mod_cast p
  rw [hreal, ← hparse, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_right (hC k) (sq_nonneg _)

/-- Each coordinate of the Hadamard-Gram `mulVec` factors through an inner product. -/
private theorem mulVec_hadamard_gram_factor {X E : Type*}
    [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Matrix X X ℂ) (u v : X → E) (t : X → ℂ) (x : X) :
    ((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ t) x =
      inner ℂ (u x) (∑ y, (A x y * t y) • v y) := by
  have hLHS : ((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ t) x =
      ∑ y, (A x y * inner ℂ (u x) (v y)) * t y := rfl
  have hRHS : inner ℂ (u x) (∑ y, (A x y * t y) • v y) =
      ∑ y, (A x y * t y) * inner ℂ (u x) (v y) := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [inner_smul_right]
  rw [hLHS, hRHS]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Per-coordinate Cauchy-Schwarz bound with the `u`-supremum factored out. -/
private theorem coord_sq_le {X E : Type*}
    [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Matrix X X ℂ) (u v : X → E) (t : X → ℂ) (x : X) :
    ‖((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ t) x‖ ^ 2 ≤
      (⨆ x, ‖u x‖) ^ 2 * ‖∑ y, (A x y * t y) • v y‖ ^ 2 := by
  rw [mulVec_hadamard_gram_factor]
  have hCS : ‖inner ℂ (u x) (∑ y, (A x y * t y) • v y)‖ ≤
      ‖u x‖ * ‖∑ y, (A x y * t y) • v y‖ :=
    norm_inner_le_norm _ _
  have hsq := sq_le_sq_of_le_of_nonneg (norm_nonneg _) hCS
  rw [mul_pow] at hsq
  have hu : ‖u x‖ ^ 2 ≤ (⨆ x, ‖u x‖) ^ 2 :=
    sq_le_sq_of_le_of_nonneg (norm_nonneg _) (le_iSup_norm u x)
  exact le_trans hsq (mul_le_mul_of_nonneg_right hu (sq_nonneg _))

/-- Schur-multiplier bound for a Gram matrix of two vector families: the
operator norm of the Hadamard product of `A` with `Gram(u, v)` is bounded by
`‖A‖` times the uniform bounds on `u` and `v`. -/
theorem norm_hadamard_gram_factor_le {X E : Type*}
    [Fintype X] [DecidableEq X]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Matrix X X ℂ) (u v : X → E) :
    ‖A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))‖ ≤
      ‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖) := by
  have hkey : ∀ (t : X → ℂ),
      ∑ x, ‖∑ y, (A x y * t y) • v y‖ ^ 2 ≤
        ‖A‖ ^ 2 * ((⨆ y, ‖v y‖) ^ 2 * ∑ y, ‖t y‖ ^ 2) := by
    intro t
    have hrewrite : ∀ x, (∑ y, (A x y * t y) • v y) =
        ∑ y, A x y • (t y • v y) := by
      intro x
      apply Finset.sum_congr rfl
      intro y _
      show (A x y * t y) • v y = A x y • (t y • v y)
      exact mul_smul _ _ _
    have hkey0 := keyEstimate A (fun y => t y • v y)
    have hLHS : (∑ x, ‖∑ y, (A x y * t y) • v y‖ ^ 2) =
        ∑ x, ‖∑ y, A x y • (t y • v y)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hrewrite x]
    have hV : (∑ y, ‖t y • v y‖ ^ 2) ≤
        (⨆ y, ‖v y‖) ^ 2 * ∑ y, ‖t y‖ ^ 2 := by
      have h1 : ∀ y, ‖t y • v y‖ ^ 2 ≤ (⨆ y, ‖v y‖) ^ 2 * ‖t y‖ ^ 2 := by
        intro y
        have e : ‖t y • v y‖ ^ 2 = ‖t y‖ ^ 2 * ‖v y‖ ^ 2 := by
          rw [norm_smul, mul_pow]
        have hv : ‖v y‖ ^ 2 ≤ (⨆ y, ‖v y‖) ^ 2 :=
          sq_le_sq_of_le_of_nonneg (norm_nonneg _) (le_iSup_norm v y)
        rw [e]
        calc ‖t y‖ ^ 2 * ‖v y‖ ^ 2 ≤ ‖t y‖ ^ 2 * (⨆ y, ‖v y‖) ^ 2 :=
              mul_le_mul_of_nonneg_left hv (sq_nonneg _)
          _ = (⨆ y, ‖v y‖) ^ 2 * ‖t y‖ ^ 2 := mul_comm _ _
      have h2 : (∑ y, ‖t y • v y‖ ^ 2) ≤
          ∑ y, (⨆ y, ‖v y‖) ^ 2 * ‖t y‖ ^ 2 :=
        Finset.sum_le_sum (fun y _ => h1 y)
      rw [← Finset.mul_sum] at h2
      exact h2
    rw [hLHS]
    refine le_trans hkey0 (mul_le_mul_of_nonneg_left hV (sq_nonneg _))
  have hCnonneg : 0 ≤ ‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (iSup_norm_nonneg u))
      (iSup_norm_nonneg v)
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hCnonneg (fun s => ?_)
  have hLHS : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X)
      (A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) s‖ ^ 2 =
      ∑ x, ‖((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ s.ofLp) x‖ ^ 2 := by
    rw [euclidean_norm_sq]
    apply Finset.sum_congr rfl
    intro x _
    exact congrArg (fun w : ℂ => ‖w‖ ^ 2)
      (congrFun (Matrix.ofLp_toEuclideanCLM
        (A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) s) x)
  have hcoord : ∀ x, ‖((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ s.ofLp) x‖ ^ 2 ≤
      (⨆ x, ‖u x‖) ^ 2 * ‖∑ y, (A x y * s.ofLp y) • v y‖ ^ 2 :=
    fun x => coord_sq_le A u v s.ofLp x
  have hsum : (∑ x, ‖((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ s.ofLp) x‖ ^ 2) ≤
      (⨆ x, ‖u x‖) ^ 2 * ∑ x, ‖∑ y, (A x y * s.ofLp y) • v y‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => hcoord x)
  have hkeyS := hkey s.ofLp
  have ht2 : ∑ y, ‖s.ofLp y‖ ^ 2 = ‖s‖ ^ 2 := (euclidean_norm_sq s).symm
  have hsq : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X)
      (A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) s‖ ^ 2 ≤
      ((‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖)) * ‖s‖) ^ 2 := by
    rw [hLHS]
    rw [ht2] at hkeyS
    have hcomb : (∑ x, ‖((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ s.ofLp) x‖ ^ 2) ≤
        (⨆ x, ‖u x‖) ^ 2 * (‖A‖ ^ 2 * ((⨆ y, ‖v y‖) ^ 2 * ‖s‖ ^ 2)) :=
      le_trans hsum (mul_le_mul_of_nonneg_left hkeyS (sq_nonneg _))
    calc (∑ x, ‖((A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) *ᵥ s.ofLp) x‖ ^ 2)
        ≤ (⨆ x, ‖u x‖) ^ 2 * (‖A‖ ^ 2 * ((⨆ y, ‖v y‖) ^ 2 * ‖s‖ ^ 2)) := hcomb
      _ = ((‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖)) * ‖s‖) ^ 2 := by ring
  have h0 : 0 ≤ (‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖)) * ‖s‖ :=
    mul_nonneg hCnonneg (norm_nonneg _)
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X)
        (A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) s‖
      = Real.sqrt (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := X)
        (A ⊙ Matrix.of (fun x y => inner ℂ (u x) (v y))) s‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖)) * ‖s‖) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = (‖A‖ * (⨆ x, ‖u x‖) * (⨆ y, ‖v y‖)) * ‖s‖ := Real.sqrt_sq h0

end MathlibExt.Analysis.InnerProductSpace.SchurGramBound
