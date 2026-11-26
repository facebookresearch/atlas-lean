/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import MathlibExt.LinearAlgebra.Matrix.RealSVD
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import MathlibExt.LinearAlgebra.Matrix.Factorizations.SVD

/-!
# Polar decomposition

Every square complex matrix admits a polar decomposition, derived from the singular value
decomposition: if `A = U * D * star V`, then `A = (U * star V) * (V * D * star V)`.
The result is `Matrix.exists_unitaryGroup_posSemidef`. For an invertible square matrix over an
`RCLike` field, `Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det` gives the unique
unitary-positive-definite polar decomposition. For a real rectangular matrix, `Matrix.polarFactor`
is the canonical polar factor $U_r V_r^{\mathsf T}$, where the columns of $U_r$ and $V_r$ are the
left and right singular vectors for the positive singular values.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
**Polar decomposition of a complex square matrix.** Let $A$ be a square complex matrix indexed by
a finite type, and let $A^*$ be its conjugate transpose. Then there are a unitary matrix $U$ and a
positive semidefinite matrix $P$ such that $P^2 = A^* A$ and $A = UP$.

Source: R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013).
Proves `Wanted` entry `polar_decomposition`, restated over `Matrix.unitaryGroup` in place of the
entry's `IsUnitaryMatrix`.
-/
theorem exists_unitaryGroup_posSemidef (A : Matrix n n ℂ) :
    ∃ (U : Matrix.unitaryGroup n ℂ) (P : Matrix n n ℂ),
      P.PosSemidef ∧ P * P = Aᴴ * A ∧ A = (U : Matrix n n ℂ) * P := by
  obtain ⟨U, V, σ, hσ, hA⟩ := exists_unitaryGroup_diagonal_nonneg A
  set D : Matrix n n ℂ := diagonal fun i => (σ i : ℂ)
  have hD : D.PosSemidef := PosSemidef.diagonal fun i => Complex.zero_le_real.2 (hσ i)
  have hDs : star D = D := by
    simp [D, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
  have hU : ∀ X : Matrix n n ℂ, star (U : Matrix n n ℂ) * (U * X) = X := fun X => by
    rw [← mul_assoc, Matrix.mem_unitaryGroup_iff'.1 U.2, one_mul]
  have hV : ∀ X : Matrix n n ℂ, star (V : Matrix n n ℂ) * (V * X) = X := fun X => by
    rw [← mul_assoc, Matrix.mem_unitaryGroup_iff'.1 V.2, one_mul]
  refine ⟨U * star V, V * D * star (V : Matrix n n ℂ), ?_, ?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using hD.mul_mul_conjTranspose_same (V : Matrix n n ℂ)
  · rw [hA, ← Matrix.star_eq_conjTranspose]
    simp only [star_mul, star_star, hDs, mul_assoc, hU, hV]
  · rw [hA, Submonoid.coe_mul, Unitary.coe_star]
    simp only [mul_assoc, hV]

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n]
variable {𝕜 : Type*} [RCLike 𝕜]

private theorem polar_posDef_conjTranspose_mul_self [DecidableEq n] (A : Matrix n n 𝕜)
    (hA : IsUnit A.det) : (Aᴴ * A).PosDef :=
  PosDef.conjTranspose_mul_self A <|
    mulVec_injective_iff_isUnit.mpr <| (isUnit_iff_isUnit_det A).mpr hA

open scoped MatrixOrder Classical in
private theorem polar_posDef_sqrt {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    (CFC.sqrt Q).PosDef := by
  exact isStrictlyPositive_iff_posDef.mp hQ.isStrictlyPositive.sqrt

open scoped MatrixOrder Classical in
private theorem polar_sqrt_mul_self {Q : Matrix n n 𝕜} (hQ : Q.PosDef) :
    CFC.sqrt Q * CFC.sqrt Q = Q :=
  CFC.sqrt_mul_sqrt_self Q hQ.posSemidef.nonneg

private theorem polar_mul_inv_mem_unitaryGroup [DecidableEq n]
    {A P : Matrix n n 𝕜} (hP : P.PosDef) (hsq : P * P = Aᴴ * A) :
    A * P⁻¹ ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  simp only [star_mul, star_eq_conjTranspose, conjTranspose_nonsing_inv,
    hP.isHermitian.eq]
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  calc
    (P⁻¹ * Aᴴ) * (A * P⁻¹) = P⁻¹ * (Aᴴ * A) * P⁻¹ := by simp only [mul_assoc]
    _ = P⁻¹ * (P * P) * P⁻¹ := by rw [← hsq]
    _ = (P⁻¹ * P) * (P * P⁻¹) := by simp only [mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul P hPdet, mul_nonsing_inv P hPdet, one_mul]

open scoped MatrixOrder Classical in
private theorem polar_eq_sqrt_of_posDef_sq {P Q : Matrix n n 𝕜} (hP : P.PosDef)
    (hsq : P * P = Q) : P = CFC.sqrt Q :=
  (CFC.sqrt_unique hsq hP.posSemidef.nonneg).symm

private theorem polar_mul_inv_mul [DecidableEq n] {A P : Matrix n n 𝕜} (hP : P.PosDef) :
    A = (A * P⁻¹) * P := by
  have hPdet : IsUnit P.det := (isUnit_iff_isUnit_det P).mp hP.isUnit
  calc
    A = A * 1 := (mul_one A).symm
    _ = A * (P⁻¹ * P) := by rw [nonsing_inv_mul P hPdet]
    _ = (A * P⁻¹) * P := (mul_assoc _ _ _).symm

private theorem polar_sq_eq_conjTranspose_mul_self [DecidableEq n]
    {A U P : Matrix n n 𝕜} (hU : U ∈ unitaryGroup n 𝕜) (hP : P.PosDef)
    (hA : A = U * P) : P * P = Aᴴ * A := by
  have hUconj : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  calc
    P * P = P * (Uᴴ * U) * P := by rw [hUconj, mul_one]
    _ = (U * P)ᴴ * (U * P) := by
      rw [conjTranspose_mul, hP.isHermitian.eq]
      simp only [mul_assoc]
    _ = Aᴴ * A := by rw [← hA]

open scoped MatrixOrder in
/-- **Uniqueness of the polar decomposition of an invertible matrix.** Let $\mathbb{K}$ be
$\mathbb{R}$ or $\mathbb{C}$, and let $A$ be a square matrix over $\mathbb{K}$, indexed by a finite
type, with $\det A \neq 0$. Then there are a unitary matrix $U$ and a positive-definite matrix $P$
with $A = UP$, and they are unique: if $U'$ is unitary, $P'$ is positive definite and
$A = U'P'$, then $U' = U$ and $P' = P$. -/
theorem exists_unique_unitaryGroup_posDef_of_isUnit_det [DecidableEq n]
    (A : Matrix n n 𝕜) (hA : IsUnit A.det) :
    ∃ (U : Matrix.unitaryGroup n 𝕜) (P : Matrix n n 𝕜),
      P.PosDef ∧ A = (U : Matrix n n 𝕜) * P ∧
        ∀ (U' : Matrix.unitaryGroup n 𝕜) (P' : Matrix n n 𝕜),
          P'.PosDef → A = (U' : Matrix n n 𝕜) * P' → U' = U ∧ P' = P := by
  let Q := Aᴴ * A
  let P := CFC.sqrt Q
  let U := A * P⁻¹
  have hQ : Q.PosDef := by
    simpa only [Q] using polar_posDef_conjTranspose_mul_self A hA
  have hP : P.PosDef := by
    simpa only [P] using polar_posDef_sqrt hQ
  have hPsq : P * P = Aᴴ * A := by
    simpa only [P, Q] using polar_sqrt_mul_self hQ
  have hU : U ∈ unitaryGroup n 𝕜 := by
    simpa only [U] using polar_mul_inv_mem_unitaryGroup hP hPsq
  have hdecomp : A = U * P := by
    simpa only [U] using polar_mul_inv_mul hP
  refine ⟨⟨U, hU⟩, P, hP, hdecomp, ?_⟩
  intro U' P' hP' hdecomp'
  have hP'eq : P' = P := by
    apply polar_eq_sqrt_of_posDef_sq hP'
    simpa only [P, Q] using
      polar_sq_eq_conjTranspose_mul_self U'.property hP' hdecomp'
  have hU'eq : (U' : Matrix n n 𝕜) = U := by
    apply hP.isUnit.mul_right_cancel
    calc
      (U' : Matrix n n 𝕜) * P = U' * P' := by rw [hP'eq]
      _ = A := hdecomp'.symm
      _ = U * P := hdecomp
  exact ⟨Subtype.ext hU'eq, hP'eq⟩

private abbrev polarRectangularDiagonal {m n : ℕ} (d : Fin n → ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  of fun i j => if i.val = j.val then d j else 0

open MathlibExt.LinearAlgebra.Matrix.RealSVDWanted in
/-- **Canonical polar factor of a rectangular matrix.** Let $G$ be a real $m \times n$ matrix and
choose a real singular value decomposition $G = U \Sigma V^{\mathsf T}$, with $U$ and $V$
orthogonal and $\Sigma$ rectangular diagonal with nonnegative entries. Form $D$ by replacing each
positive entry of $\Sigma$ by $1$ and keeping the zeros. The polar factor is $U D V^{\mathsf T}$,
equivalently $U_r V_r^{\mathsf T}$, where the columns of $U_r$ and $V_r$ are the left and right
singular vectors for the positive singular values. The factor of the zero matrix is zero.

The construction uses classical choice to obtain an SVD, but the product is the same for every
such decomposition.

The definition follows the rank-reduced (compact SVD) convention. For every $G$, the factor is
the partial isometry $P$ of the canonical polar decomposition $G = P H$: the unique decomposition
with $P$ a partial isometry, $H$ symmetric positive semidefinite and the row space of $P$ equal
to the range of $H$, in which $H = (G^{\mathsf T} G)^{1/2}$. If $G$ has full rank $\min(m, n)$,
$P$ is semi-orthogonal ($P P^{\mathsf T} = I_m$ or $P^{\mathsf T} P = I_n$) and is the unique
polar factor of $G$ with orthonormal columns (or, when $m < n$, the transpose of that of
$G^{\mathsf T}$). It is also a semi-orthogonal matrix nearest to $G$ in every unitarily invariant
norm, and the unique nearest one in the Frobenius norm. In the spectral norm a nearest
semi-orthogonal matrix need not be unique: for $G = \operatorname{diag}(3, 1)$, both $I$ and
$\operatorname{diag}(1, -1)$ attain the least distance, $2$. If the rank of $G$ is less than
$\min(m, n)$, $P$ is not semi-orthogonal.

Sources: Amsel, Persson, Musco and Gower, *The Polar Express*, ICLR 2026, arXiv:2505.16932 v5,
Section 1.1, equation (1), and the Notation paragraph at the end of Section 1 (polynomials of a
matrix through its rank-reduced SVD); they describe the factor as the closest semi-orthogonal
matrix without naming a norm, and this definition gives a nearest semi-orthogonal matrix only at
full rank. Higham, *Functions of Matrices: Theory and Computation*, SIAM, 2008, Chapter 8,
Theorem 8.1 (the polar decomposition with orthonormal columns, unique at full rank), Theorem 8.3
(the canonical polar decomposition) and Theorem 8.4 (the polar factor as a nearest matrix with
orthonormal columns in every unitarily invariant norm, and the unique nearest one in the Frobenius
norm at full rank). -/
noncomputable def polarFactor {m n : ℕ} (G : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  let h := real_singular_value_decomposition m n G
  let σ := h.choose_spec.choose_spec.choose
  let D : Matrix (Fin m) (Fin n) ℝ :=
    of fun i j => if i.val = j.val then (if 0 < σ j then 1 else 0) else 0
  h.choose * D * h.choose_spec.chooseᵀ

private theorem polarRectangularDiagonal_transpose_mul_self {m n : ℕ} (σ : Fin n → ℝ)
    (hσ : ∀ j, m ≤ j.val → σ j = 0) :
    (polarRectangularDiagonal (m := m) σ)ᵀ * polarRectangularDiagonal σ =
      diagonal (fun j => σ j ^ 2) := by
  ext i j
  simp only [Matrix.mul_apply, transpose_apply, of_apply, diagonal_apply]
  by_cases hi : i.val < m
  · rw [Finset.sum_eq_single (⟨i.val, hi⟩ : Fin m)]
    · by_cases hij : i = j
      · subst j
        simp [pow_two]
      · simp [hij, Fin.val_ne_of_ne hij]
    · intro k _ hk
      have hki : k.val ≠ i.val := fun h => hk (Fin.ext h)
      simp [hki]
    · simp
  · have hki (k : Fin m) : k.val ≠ i.val := fun h => hi (h ▸ k.isLt)
    by_cases hij : i = j
    · subst j
      simp [hki, hσ i (Nat.le_of_not_gt hi)]
    · simp [hki, hij]

private theorem polarFactor_of_svd_eq_mul {m n : ℕ} {G : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {σ : Fin n → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hG : G = U * polarRectangularDiagonal σ * Vᵀ) :
    U * polarRectangularDiagonal (fun j => if 0 < σ j then 1 else 0) * Vᵀ =
      G * (V * diagonal (fun j => (σ j)⁻¹) * Vᵀ) := by
  have hD : polarRectangularDiagonal (m := m) σ * diagonal (fun j => (σ j)⁻¹) =
      polarRectangularDiagonal (fun j => if 0 < σ j then 1 else 0) := by
    ext i j
    rw [mul_diagonal]
    by_cases hj : 0 < σ j
    · simp [hj, hj.ne', apply_ite (· * (σ j)⁻¹)]
    · have hz : σ j = 0 := le_antisymm (le_of_not_gt hj) (hσ j)
      simp [hz]
  have hVtV := (mem_orthogonalGroup_iff' (Fin n) ℝ).mp hV
  rw [hG, ← hD]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᵀ V, hVtV, Matrix.one_mul]

private theorem polarFactor_gram_eq {m n : ℕ} {G : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {σ : Fin n → ℝ}
    (hzero : ∀ j, m ≤ j.val → σ j = 0) (hU : U ∈ orthogonalGroup (Fin m) ℝ)
    (hG : G = U * polarRectangularDiagonal σ * Vᵀ) :
    Gᵀ * G = V * diagonal (fun j => σ j ^ 2) * Vᵀ := by
  have hUtU := (mem_orthogonalGroup_iff' (Fin m) ℝ).mp hU
  rw [hG, transpose_mul, transpose_mul, transpose_transpose]
  simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ U, hUtU, Matrix.one_mul]
  rw [← Matrix.mul_assoc (polarRectangularDiagonal σ)ᵀ,
    polarRectangularDiagonal_transpose_mul_self σ hzero]

open MathlibExt.LinearAlgebra.Matrix.RealSVDWanted in
private theorem polarFactor_eq_of_svd {m n : ℕ} {G : Matrix (Fin m) (Fin n) ℝ}
    {U : Matrix (Fin m) (Fin m) ℝ} {V : Matrix (Fin n) (Fin n) ℝ} {σ : Fin n → ℝ}
    (hσ : ∀ j, 0 ≤ σ j) (hzero : ∀ j, m ≤ j.val → σ j = 0)
    (hU : U ∈ orthogonalGroup (Fin m) ℝ) (hV : V ∈ orthogonalGroup (Fin n) ℝ)
    (hG : G = U * polarRectangularDiagonal σ * Vᵀ) :
    G.polarFactor = U * polarRectangularDiagonal (fun j => if 0 < σ j then 1 else 0) * Vᵀ := by
  let h := real_singular_value_decomposition m n G
  let U' := h.choose
  let V' := h.choose_spec.choose
  let σ' := h.choose_spec.choose_spec.choose
  have hspec : (∀ j, 0 ≤ σ' j) ∧ (∀ j, m ≤ j.val → σ' j = 0) ∧
      U' ∈ orthogonalGroup (Fin m) ℝ ∧ V' ∈ orthogonalGroup (Fin n) ℝ ∧
      G = U' * polarRectangularDiagonal σ' * V'ᵀ := h.choose_spec.choose_spec.choose_spec
  obtain ⟨hσ', hzero', hU', hV', hG'⟩ := hspec
  change U' * polarRectangularDiagonal (m := m) (fun j => if 0 < σ' j then 1 else 0) * V'ᵀ = _
  rw [polarFactor_of_svd_eq_mul hσ' hV' hG', polarFactor_of_svd_eq_mul hσ hV hG]
  -- In the change of right singular basis, entries joining distinct singular values vanish.
  have hVtV := (mem_orthogonalGroup_iff' (Fin n) ℝ).mp hV
  have hV'tV' := (mem_orthogonalGroup_iff' (Fin n) ℝ).mp hV'
  have hV'V't := (mem_orthogonalGroup_iff (Fin n) ℝ).mp hV'
  have hVVt := (mem_orthogonalGroup_iff (Fin n) ℝ).mp hV
  have hsquares : diagonal (fun j => σ' j ^ 2) * (V'ᵀ * V) =
      (V'ᵀ * V) * diagonal (fun j => σ j ^ 2) := by
    calc
      _ = V'ᵀ * (Gᵀ * G) * V := by
        rw [polarFactor_gram_eq hzero' hU' hG', ← Matrix.mul_assoc V'ᵀ,
          ← Matrix.mul_assoc V'ᵀ, hV'tV', Matrix.one_mul, Matrix.mul_assoc]
      _ = _ := by
        rw [polarFactor_gram_eq hzero hU hG]
        simp only [Matrix.mul_assoc, hVtV, Matrix.mul_one]
  have hinvs : diagonal (fun j => (σ' j)⁻¹) * (V'ᵀ * V) =
      (V'ᵀ * V) * diagonal (fun j => (σ j)⁻¹) := by
    ext i j
    have hij := congr(($hsquares) i j)
    simp only [diagonal_mul, mul_diagonal] at hij ⊢
    by_cases hz : (V'ᵀ * V) i j = 0
    · simp [hz]
    have heq := mul_right_cancel₀ hz (hij.trans (mul_comm _ _))
    rw [(sq_eq_sq₀ (hσ' i) (hσ j)).mp heq, mul_comm]
  congr 1
  calc
    _ = V' * (diagonal (fun j => (σ' j)⁻¹) * (V'ᵀ * V)) * Vᵀ := by
      symm
      rw [← Matrix.mul_assoc (diagonal _), ← Matrix.mul_assoc V', ← Matrix.mul_assoc V',
        Matrix.mul_assoc _ V Vᵀ, hVVt, Matrix.mul_one]
    _ = V' * ((V'ᵀ * V) * diagonal (fun j => (σ j)⁻¹)) * Vᵀ := by rw [hinvs]
    _ = _ := by
      rw [← Matrix.mul_assoc V', ← Matrix.mul_assoc V', hV'V't, Matrix.one_mul]

end Matrix
