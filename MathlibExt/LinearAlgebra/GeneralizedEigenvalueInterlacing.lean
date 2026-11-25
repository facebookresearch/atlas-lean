/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import MathlibExt.Analysis.InnerProductSpace.CauchyInterlacing

/-!
# Interlacing of generalized eigenvalues

`MetaMathlibExt.generalizedEigenvalue_interlacing` proves Cauchy interlacing for a Hermitian
matrix pencil and its leading principal subpencil by compressing a self-adjoint operator
in the inner product induced by the positive definite matrix.
-/

open Polynomial Matrix
open scoped ComplexOrder InnerProductSpace

namespace MetaMathlibExt

namespace generalizedEigenvalue_interlacing

-- In any basis, the matrix of the form ⟪x, T y⟫ is the Gram matrix times the matrix of T.
private theorem form_matrix {m : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : Module.Basis (Fin m) ℂ E) (T : E →ₗ[ℂ] E)
    {A B : Matrix (Fin m) (Fin m) ℂ}
    (hA : ∀ i j, ⟪b i, T (b j)⟫_ℂ = A i j) (hB : ∀ i j, ⟪b i, b j⟫_ℂ = B i j) :
    A = B * LinearMap.toMatrix b b T := by
  ext i j
  calc
    A i j = ⟪b i, T (b j)⟫_ℂ := (hA i j).symm
    _ = ⟪b i, ∑ k, b.repr (T (b j)) k • b k⟫_ℂ := by rw [b.sum_repr]
    _ = _ := by simp only [inner_sum, inner_smul_right, hB, Matrix.mul_apply,
        LinearMap.toMatrix_apply, mul_comm]

-- Factoring −B out of the pencil leaves the characteristic matrix of M.
private theorem pencil_roots {m : ℕ} (B M : Matrix (Fin m) (Fin m) ℂ) (hB : B.det ≠ 0) :
    ((B * M).map C - (X : ℂ[X]) • B.map C).det.roots = M.charpoly.roots := by
  have heq : (B * M).map C - (X : ℂ[X]) • B.map C =
      C.mapMatrix (-B) * M.charmatrix := by
    rw [map_neg, Matrix.charmatrix, Matrix.mul_sub, RingHom.mapMatrix_apply, Matrix.map_mul]
    simp [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_eq_add_neg, add_comm]
  rw [heq, Matrix.det_mul, ← C.map_det, roots_C_mul _ (by simp [Matrix.det_neg, hB])]
  rfl

private theorem eigenvalues_of_pencil {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (b : Module.Basis (Fin m) ℂ E)
    {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (hdim : Module.finrank ℂ E = m)
    {A B : Matrix (Fin m) (Fin m) ℂ} (hB : B.PosDef)
    (hform : ∀ i j, ⟪b i, T (b j)⟫_ℂ = A i j) (hgram : ∀ i j, ⟪b i, b j⟫_ℂ = B i j)
    (lam : Fin m → ℝ) (hlam : Antitone lam)
    (hroots : (A.map C - (X : ℂ[X]) • B.map C).det.roots =
      Finset.univ.val.map fun i => (lam i : ℂ)) :
    hT.eigenvalues hdim = lam := by
  rw [form_matrix b T hform hgram, pencil_roots _ _ hB.det_pos.ne', T.charpoly_toMatrix] at hroots
  rw [← List.ofFn_inj, ← hT.sort_roots_charpoly_eq_eigenvalues hdim, hroots]
  simp only [Fin.univ_val_map, Multiset.map_coe, List.map_ofFn, Function.comp_def,
    Multiset.coe_sort]
  change (List.ofFn lam).mergeSort _ = List.ofFn lam
  apply List.mergeSort_of_pairwise
  simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using hlam.sortedGE_ofFn

private theorem hasProjection {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (S : Submodule ℂ E) [FiniteDimensional ℂ S] : S.HasOrthogonalProjection := by
  have : CompleteSpace S := FiniteDimensional.completeSpace ℂ S
  infer_instance

end generalizedEigenvalue_interlacing

open generalizedEigenvalue_interlacing
open MathlibExt.Analysis.InnerProductSpace.CauchyInterlacing

set_option linter.unusedVariables false in
/-- **Cauchy interlacing for generalized eigenvalues.** Let $n \ge 1$, let $A$ be a Hermitian
and $B$ a positive definite complex $(n+1) \times (n+1)$ matrix, and let $A'$ and $B'$ be their
leading principal $n \times n$ submatrices (rows and columns $1, \dots, n$). Let
$\lambda_1 \ge \dots \ge \lambda_{n+1}$ be real numbers such that the roots of the polynomial
$\det(A - XB)$, counted with multiplicity, are exactly $\lambda_1, \dots, \lambda_{n+1}$, and
let $\lambda'_1 \ge \dots \ge \lambda'_n$ be real numbers such that the roots of
$\det(A' - XB')$, counted with multiplicity, are exactly $\lambda'_1, \dots, \lambda'_n$. Then
$\lambda_{k+1} \le \lambda'_k \le \lambda_k$ for every $k = 1, \dots, n$.

Source: Jorma K. Merikoski, Pentti Haukkanen, Antonio Sasaki, and Timo Tossavainen, *On
Generalized Eigenvalues of MAX Matrices to MIN Matrices and LCM Matrices to GCD Matrices*,
Journal of Integer Sequences 28 (2025), Article 25.7.1, Theorem 6 (`jis-2025-25.7.1-thm-6`). -/
public theorem generalizedEigenvalue_interlacing (n : ℕ) (hn : 1 ≤ n)
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hA : A.IsHermitian) (hB : B.PosDef)
    (lam : Fin (n + 1) → ℝ) (hlam : Antitone lam)
    (hroots : (A.map C - (X : ℂ[X]) • B.map C).det.roots =
      Finset.univ.val.map fun i => (lam i : ℂ))
    (lam' : Fin n → ℝ) (hlam' : Antitone lam')
    (hroots' : ((A.submatrix Fin.castSucc Fin.castSucc).map C -
        (X : ℂ[X]) • (B.submatrix Fin.castSucc Fin.castSucc).map C).det.roots =
      Finset.univ.val.map fun i => (lam' i : ℂ)) :
    ∀ k : Fin n, lam k.succ ≤ lam' k ∧ lam' k ≤ lam k.castSucc := by
  let b := Pi.basisFun ℂ (Fin (n + 1))
  let := B.toNormedAddCommGroup hB
  let := B.toSeminormedAddCommGroup hB.posSemidef
  let := B.toInnerProductSpace hB.posSemidef
  let T := (B⁻¹ * A).mulVecLin
  have hBT : B * (B⁻¹ * A) = A := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB.det_pos.ne'),
      Matrix.one_mul]
  have hpair (x y : Fin (n + 1) → ℂ) : ⟪x, T y⟫_ℂ = star x ⬝ᵥ A *ᵥ y := by
    change (B *ᵥ ((B⁻¹ * A) *ᵥ y)) ⬝ᵥ star x = _
    rw [Matrix.mulVec_mulVec, hBT, dotProduct_comm]
  have hT : LinearMap.IsSymmetric (𝕜 := ℂ) (E := Fin (n + 1) → ℂ) T := by
    intro x y
    rw [← inner_conj_symm, hpair, hpair]
    exact hA.star_dotProduct_mulVec_comm y x
  have hform (i j) : ⟪b i, T (b j)⟫_ℂ = A i j := by
    simp [hpair, b, Pi.basisFun_apply]
  have hgram (i j) : ⟪b i, b j⟫_ℂ = B i j := by
    change (B *ᵥ b j) ⬝ᵥ star (b i) = _
    simp [b, Pi.basisFun_apply]
  -- Restrict both forms to the span of the first n coordinate vectors.
  let S := Submodule.span ℂ (Set.range (b ∘ Fin.castSucc))
  let c : Module.Basis (Fin n) ℂ S :=
    Module.Basis.span (b.linearIndependent.comp Fin.castSucc (Fin.castSucc_injective n))
  have hc (i : Fin n) : (c i : Fin (n + 1) → ℂ) = b i.castSucc :=
    Module.Basis.coe_span_apply _ _
  have hdim : Module.finrank ℂ (Fin (n + 1) → ℂ) = n + 1 := by simp
  have hdim' : Module.finrank ℂ S = n := by simpa using Module.finrank_eq_card_basis c
  have : S.HasOrthogonalProjection := hasProjection S
  have he := eigenvalues_of_pencil b hT hdim hB hform hgram lam hlam hroots
  have he' := eigenvalues_of_pencil c (compression_isSymmetric hT S) hdim'
    (A := A.submatrix Fin.castSucc Fin.castSucc) (hB.submatrix (Fin.castSucc_injective n))
    (fun i j => by
      rw [compression_apply, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left, hc, hc]
      exact hform _ _)
    (fun i j => by
      change ⟪(c i : Fin (n + 1) → ℂ), (c j : Fin (n + 1) → ℂ)⟫_ℂ = _
      rw [hc, hc]
      exact hgram _ _) lam' hlam' hroots'
  intro k
  rw [← he, ← he']
  exact cauchy_interlacing hT hdim S hdim' (k := k.val) (by omega)

end MetaMathlibExt
