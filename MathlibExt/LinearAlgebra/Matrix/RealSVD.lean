/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Rectangular real singular value decomposition

This file proves that every rectangular real matrix admits a singular value decomposition with
orthogonal left and right factors and a rectangular diagonal matrix of nonnegative singular values.
-/

@[expose] public section

namespace Matrix

private theorem realSVD_inner_image_eigenvectorBasis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (i j : Fin n) :
    inner ℝ (T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i))
        (T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) j)) =
      T.singularValues j.val ^ 2 * if i = j then 1 else 0 := by
  set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  set ev := T.isSymmetric_adjoint_comp_self.eigenvalues hn
  have hAdj :
      inner ℝ (T (b i)) (T (b j)) = inner ℝ (b i) ((T.adjoint ∘ₗ T) (b j)) :=
    (LinearMap.adjoint_inner_right T (b i) (T (b j))).symm
  rw [hAdj, LinearMap.IsSymmetric.apply_eigenvectorBasis, real_inner_smul_right,
    b.inner_eq_ite, ← T.sq_singularValues_fin hn]
  norm_num

private theorem realSVD_image_eigenvectorBasis_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : Module.finrank ℝ E = n) (j : Fin n) (hσ : T.singularValues j.val = 0) :
    T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) j) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [realSVD_inner_image_eigenvectorBasis T hn j j, hσ]
  norm_num

private theorem realSVD_singularValues_eq_zero_of_finrank_codomain_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {m j : ℕ}
    (hm : Module.finrank ℝ F = m) (h : m ≤ j) : T.singularValues j = 0 := by
  rw [T.singularValues_eq_zero_iff_le_finrank_range]
  calc
    Module.finrank ℝ T.range ≤ Module.finrank ℝ F := Submodule.finrank_le T.range
    _ = m := hm
    _ ≤ j := h

private noncomputable def realSVD_normalizedImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {n : ℕ}
    (hn : Module.finrank ℝ E = n) {m : ℕ} (i : Fin m) : F :=
  if hi : i.val < n then
    (T.singularValues i.val)⁻¹ •
      T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) ⟨i.val, hi⟩)
  else 0

private def realSVD_nonzeroImageIndices
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) (n m : ℕ) : Set (Fin m) :=
  {i | i.val < n ∧ T.singularValues i.val ≠ 0}

private theorem realSVD_normalizedImages_orthonormal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {n m : ℕ}
    (hn : Module.finrank ℝ E = n) :
    Orthonormal ℝ ((realSVD_nonzeroImageIndices T n m).domRestrict
      (realSVD_normalizedImage T hn)) := by
  rw [orthonormal_iff_ite]
  intro i j
  obtain ⟨hi, hσi⟩ := i.property
  obtain ⟨hj, hσj⟩ := j.property
  by_cases hij : i = j
  · subst j
    simp only [Set.domRestrict_apply]
    rw [realSVD_normalizedImage, dite_eq_left hi, real_inner_smul_left,
      real_inner_smul_right, realSVD_inner_image_eigenvectorBasis T hn]
    field_simp
  · have hv : i.val.val ≠ j.val.val := by
      intro h
      apply hij
      exact Subtype.ext (Fin.ext h)
    have hfin : (⟨i.val.val, hi⟩ : Fin n) ≠ ⟨j.val.val, hj⟩ := by
      intro h
      exact hv (congrArg (fun x : Fin n => x.val) h)
    simp [Set.domRestrict_apply, realSVD_normalizedImage, hi, hj,
      real_inner_smul_left, real_inner_smul_right,
      realSVD_inner_image_eigenvectorBasis T hn, hfin, hij]

private theorem realSVD_exists_leftBasis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (T : E →ₗ[ℝ] F) {n m : ℕ}
    (hn : Module.finrank ℝ E = n) (hm : Module.finrank ℝ F = m) :
    ∃ u : OrthonormalBasis (Fin m) ℝ F, ∀ j : Fin n,
      T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) j) =
        if h : j.val < m then T.singularValues j.val • u ⟨j.val, h⟩ else 0 := by
  have hcard : Module.finrank ℝ F = Fintype.card (Fin m) := by
    simpa using hm
  obtain ⟨u, hu⟩ :=
    (realSVD_normalizedImages_orthonormal T hn).exists_orthonormalBasis_extension_of_card_eq
      hcard
  refine ⟨u, fun j => ?_⟩
  by_cases hjm : j.val < m
  · rw [dite_eq_left hjm]
    by_cases hσ : T.singularValues j.val = 0
    · rw [hσ, zero_smul]
      exact realSVD_image_eigenvectorBasis_eq_zero T hn j hσ
    · have hmem : (⟨j.val, hjm⟩ : Fin m) ∈ realSVD_nonzeroImageIndices T n m :=
        ⟨j.isLt, hσ⟩
      rw [hu _ hmem, realSVD_normalizedImage, dite_eq_left j.isLt, smul_smul,
        mul_inv_cancel₀ hσ, one_smul]
  · rw [dite_eq_right hjm]
    apply realSVD_image_eigenvectorBasis_eq_zero T hn j
    exact realSVD_singularValues_eq_zero_of_finrank_codomain_le T hm (Nat.le_of_not_gt hjm)

private theorem realSVD_toMatrix_eq_rectangularDiagonal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n m : ℕ}
    (T : E →ₗ[ℝ] F) (v : OrthonormalBasis (Fin n) ℝ E)
    (u : OrthonormalBasis (Fin m) ℝ F) (σ : Fin n → ℝ)
    (h : ∀ j : Fin n, T (v j) = if hj : j.val < m then σ j • u ⟨j.val, hj⟩ else 0) :
    LinearMap.toMatrix v.toBasis u.toBasis T =
      Matrix.of (fun i j => if i.val = j.val then σ j else 0) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change u.toBasis.repr (T (v j)) i = if i.val = j.val then σ j else 0
  rw [h j]
  by_cases hj : j.val < m
  · rw [dite_eq_left hj]
    simp [Fin.ext_iff]
  · rw [dite_eq_right hj]
    have hne : i.val ≠ j.val := fun hij => hj (hij ▸ i.isLt)
    simp [hne]

/--
**Orthogonal reduction of a real matrix to rectangular diagonal form.** Let $A$ be a real
$m \times n$ matrix. Then there are orthogonal matrices $U$ of size $m \times m$ and $V$ of size
$n \times n$ and real numbers $\sigma_1 \ge \sigma_2 \ge \dots \ge \sigma_n \ge 0$ with
$\sigma_j = 0$ for every $j > m$, such that $AV = U\Sigma$, where $\Sigma$ is the $m \times n$
matrix with $\Sigma_{jj} = \sigma_j$ for $j \le \min(m, n)$ and all other entries zero.

Source: S. Axler, Linear Algebra Done Right, 4th ed., Section 7E.
-/
theorem exists_orthogonalGroup_mul_eq_rectangularDiagonal
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
        (σ : Fin n → ℝ),
      (∀ j, 0 ≤ σ j) ∧ Antitone σ ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
      A * (V : Matrix (Fin n) (Fin n) ℝ) =
        (U : Matrix (Fin m) (Fin m) ℝ) *
          Matrix.of (fun i j => if i.val = j.val then σ j else 0) := by
  classical
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    Matrix.toEuclideanLin A
  let v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
  obtain ⟨u, hu⟩ := realSVD_exists_leftBasis T finrank_euclideanSpace_fin
    finrank_euclideanSpace_fin
  have hA : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis T = A := by
    change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℝ).toBasis (Matrix.toEuclideanLin A) = A
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact LinearMap.toMatrix_toLin _ _ _
  have hdiag : LinearMap.toMatrix v.toBasis u.toBasis T =
      Matrix.of (fun i j => if i.val = j.val then T.singularValues j.val else 0) :=
    realSVD_toMatrix_eq_rectangularDiagonal T v u (fun j => T.singularValues j.val) hu
  refine ⟨⟨(EuclideanSpace.basisFun (Fin m) ℝ).toBasis.toMatrix u,
      (EuclideanSpace.basisFun (Fin m) ℝ).toMatrix_orthonormalBasis_mem_orthogonal u⟩,
    ⟨(EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix v,
      (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal v⟩,
    fun j => T.singularValues j.val, ?_, ?_, ?_, ?_⟩
  · exact fun j => T.singularValues_nonneg j.val
  · intro i j hij
    exact T.singularValues_antitone hij
  · intro j hj
    exact realSVD_singularValues_eq_zero_of_finrank_codomain_le T
      finrank_euclideanSpace_fin hj
  · calc
      A * (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.toMatrix v =
          LinearMap.toMatrix v.toBasis (EuclideanSpace.basisFun (Fin m) ℝ).toBasis T := by
            rw [← hA]
            exact linearMap_toMatrix_mul_basis_toMatrix v.toBasis
              (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
              (EuclideanSpace.basisFun (Fin m) ℝ).toBasis T
      _ = (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.toMatrix u *
          LinearMap.toMatrix v.toBasis u.toBasis T := by
            symm
            exact basis_toMatrix_mul_linearMap_toMatrix v.toBasis
              (EuclideanSpace.basisFun (Fin m) ℝ).toBasis u.toBasis T
      _ = (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.toMatrix u *
          Matrix.of (fun i j => if i.val = j.val then T.singularValues j.val else 0) := by
            exact congrArg ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis.toMatrix u * ·) hdiag

/--
**Real singular value decomposition with nonincreasing singular values.** Let $A$ be a real
$m \times n$ matrix. Then there are orthogonal matrices $U$ of size $m \times m$ and $V$ of size
$n \times n$ and real numbers $\sigma_1 \ge \sigma_2 \ge \dots \ge \sigma_n \ge 0$ with
$\sigma_j = 0$ for every $j > m$, such that $A = U \Sigma V^{\mathsf{T}}$, where $\Sigma$ is the
$m \times n$ matrix with $\Sigma_{jj} = \sigma_j$ for $j \le \min(m, n)$ and all other entries
zero.

Proof: multiply the factorization $AV = U\Sigma$ on the right by $V^{\mathsf{T}}$.
-/
theorem exists_orthogonalGroup_rectangularDiagonal_antitone
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (U : Matrix.orthogonalGroup (Fin m) ℝ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
        (σ : Fin n → ℝ),
      (∀ j, 0 ≤ σ j) ∧ Antitone σ ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
      A = (U : Matrix (Fin m) (Fin m) ℝ) *
        Matrix.of (fun i j => if i.val = j.val then σ j else 0) *
          Matrix.transpose (V : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨U, V, σ, hσ, hanti, hzero, hAV⟩ :=
    exists_orthogonalGroup_mul_eq_rectangularDiagonal m n A
  refine ⟨U, V, σ, hσ, hanti, hzero, ?_⟩
  have hVVt : (V : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.transpose (V : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp V.2
  calc
    A = A * 1 := (Matrix.mul_one A).symm
    _ = A * ((V : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.transpose (V : Matrix (Fin n) (Fin n) ℝ)) := by rw [hVVt]
    _ = (A * (V : Matrix (Fin n) (Fin n) ℝ)) *
        Matrix.transpose (V : Matrix (Fin n) (Fin n) ℝ) := by rw [Matrix.mul_assoc]
    _ = ((U : Matrix (Fin m) (Fin m) ℝ) *
        Matrix.of (fun i j => if i.val = j.val then σ j else 0)) *
        Matrix.transpose (V : Matrix (Fin n) (Fin n) ℝ) := by
      rw [hAV]

end Matrix

namespace MathlibExt.LinearAlgebra.Matrix.RealSVDWanted

/--
**Real singular value decomposition.** Let $A$ be a real $m \times n$ matrix. Then there are
orthogonal matrices $U$ of size $m \times m$ and $V$ of size $n \times n$ and real numbers
$\sigma_1, \dots, \sigma_n \ge 0$ with $\sigma_j = 0$ for every $j > m$, such that
$A = U \Sigma V^{\mathsf{T}}$, where $\Sigma$ is the $m \times n$ matrix with
$\Sigma_{jj} = \sigma_j$ for $j \le \min(m, n)$ and all other entries zero.

Proof: apply the spectral theorem to $A^{\mathsf{T}} A$, normalize the images under $A$ of the
eigenvectors with positive eigenvalues, and extend them to an orthonormal basis of
$\mathbb{R}^m$, as in the proof of S. Axler, Linear Algebra Done Right, 4th ed., 7.70, and the
matrix form that follows it (Section 7E).

Proves `Wanted` entry `real_singular_value_decomposition`.

Sources: Mathlib `docs/undergrad.yaml`, Numerical Analysis / Iterative methods / singular value
decomposition; G. H. Golub and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins
University Press (2013), Theorem 2.4.1.
-/
theorem real_singular_value_decomposition (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (U : Matrix (Fin m) (Fin m) ℝ) (V : Matrix (Fin n) (Fin n) ℝ) (σ : Fin n → ℝ),
      (∀ j, 0 ≤ σ j) ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
      U ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧ V ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      A = U * Matrix.of (fun i j => if i.val = j.val then σ j else 0) *
        Matrix.transpose V := by
  obtain ⟨U, V, σ, hσ, -, hzero, hA⟩ :=
    Matrix.exists_orthogonalGroup_rectangularDiagonal_antitone m n A
  exact ⟨U, V, σ, hσ, hzero, U.2, V.2, hA⟩

end MathlibExt.LinearAlgebra.Matrix.RealSVDWanted
