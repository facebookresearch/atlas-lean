/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Rectangular complex singular value decomposition

Every rectangular complex matrix admits a singular value decomposition with
unitary left and right factors and a rectangular diagonal matrix of nonnegative
singular values. The square complex case is
`Matrix.exists_unitaryGroup_diagonal_nonneg` (in
`MathlibExt/LinearAlgebra/Matrix/Factorizations/SVD.lean`) and the rectangular
real case is `Matrix.exists_orthogonalGroup_rectangularDiagonal_antitone` (in
`MathlibExt/LinearAlgebra/Matrix/RealSVD.lean`); the rectangular complex case
was missing.
-/

@[expose] public section

namespace Matrix

private theorem complexSVD_inner_image_eigenvectorBasis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (i j : Fin n) :
    inner ℂ (T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) i))
        (T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) j)) =
      ((T.singularValues j.val ^ 2 : ℝ) : ℂ) * (if i = j then (1 : ℂ) else 0) := by
  set b := T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn
  have hAdj :
      inner ℂ (T (b i)) (T (b j)) = inner ℂ (b i) ((T.adjoint ∘ₗ T) (b j)) :=
    (LinearMap.adjoint_inner_right T (b i) (T (b j))).symm
  rw [hAdj, LinearMap.IsSymmetric.apply_eigenvectorBasis, inner_smul_right,
    b.inner_eq_ite, ← T.sq_singularValues_fin hn]
  by_cases hij : i = j <;> simp [hij]

private theorem complexSVD_image_eigenvectorBasis_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {n : ℕ}
    (hn : Module.finrank ℂ E = n) (j : Fin n) (hσ : T.singularValues j.val = 0) :
    T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) j) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [complexSVD_inner_image_eigenvectorBasis T hn j j, hσ]
  norm_num

private theorem complexSVD_singularValues_eq_zero_of_finrank_codomain_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {m j : ℕ}
    (hm : Module.finrank ℂ F = m) (h : m ≤ j) : T.singularValues j = 0 := by
  rw [T.singularValues_eq_zero_iff_le_finrank_range]
  calc
    Module.finrank ℂ T.range ≤ Module.finrank ℂ F := Submodule.finrank_le T.range
    _ = m := hm
    _ ≤ j := h

private noncomputable def complexSVD_normalizedImage
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {n : ℕ}
    (hn : Module.finrank ℂ E = n) {m : ℕ} (i : Fin m) : F :=
  if hi : i.val < n then
    ((T.singularValues i.val : ℂ))⁻¹ •
      T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) ⟨i.val, hi⟩)
  else 0

private def complexSVD_nonzeroImageIndices
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) (n m : ℕ) : Set (Fin m) :=
  {i | i.val < n ∧ T.singularValues i.val ≠ 0}

private theorem complexSVD_normalizedImages_orthonormal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {n m : ℕ}
    (hn : Module.finrank ℂ E = n) :
    Orthonormal ℂ ((complexSVD_nonzeroImageIndices T n m).domRestrict
      (complexSVD_normalizedImage T hn)) := by
  rw [orthonormal_iff_ite]
  intro i j
  obtain ⟨hi, hσi⟩ := i.property
  obtain ⟨hj, hσj⟩ := j.property
  by_cases hij : i = j
  · subst j
    have hσℂ : ((T.singularValues i.val.val : ℂ)) ≠ 0 := by exact_mod_cast hσi
    have hca : (starRingEnd ℂ) ((↑(T.singularValues i.val.val) : ℂ)⁻¹) =
        ((↑(T.singularValues i.val.val) : ℂ))⁻¹ := by
      rw [map_inv₀]
      congr 1
      exact RCLike.conj_ofReal _
    simp only [Set.domRestrict_apply]
    rw [complexSVD_normalizedImage, dite_eq_left hi, inner_smul_left, inner_smul_right,
      complexSVD_inner_image_eigenvectorBasis T hn]
    simp only [ite_true, mul_one, Complex.ofReal_pow, hca]
    field_simp
  · have hv : i.val.val ≠ j.val.val := by
      intro h
      apply hij
      exact Subtype.ext (Fin.ext h)
    have hfin : (⟨i.val.val, hi⟩ : Fin n) ≠ ⟨j.val.val, hj⟩ := by
      intro h
      exact hv (congrArg (fun x : Fin n => x.val) h)
    rw [ite_eq_right hij]
    simp only [Set.domRestrict_apply]
    rw [complexSVD_normalizedImage, dite_eq_left hi, complexSVD_normalizedImage,
      dite_eq_left hj, inner_smul_left, inner_smul_right,
      complexSVD_inner_image_eigenvectorBasis T hn, ite_eq_right hfin]
    simp

private theorem complexSVD_exists_leftBasis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) {n m : ℕ}
    (hn : Module.finrank ℂ E = n) (hm : Module.finrank ℂ F = m) :
    ∃ u : OrthonormalBasis (Fin m) ℂ F, ∀ j : Fin n,
      T ((T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn) j) =
        if h : j.val < m then (T.singularValues j.val : ℂ) • u ⟨j.val, h⟩ else 0 := by
  have hcard : Module.finrank ℂ F = Fintype.card (Fin m) := by
    simpa using hm
  obtain ⟨u, hu⟩ :=
    (complexSVD_normalizedImages_orthonormal T hn).exists_orthonormalBasis_extension_of_card_eq
      hcard
  refine ⟨u, fun j => ?_⟩
  by_cases hjm : j.val < m
  · rw [dite_eq_left hjm]
    by_cases hσ : T.singularValues j.val = 0
    · rw [hσ, Complex.ofReal_zero, zero_smul]
      exact complexSVD_image_eigenvectorBasis_eq_zero T hn j hσ
    · have hσℂ : ((T.singularValues j.val : ℂ)) ≠ 0 := by exact_mod_cast hσ
      have hmem : (⟨j.val, hjm⟩ : Fin m) ∈ complexSVD_nonzeroImageIndices T n m :=
        ⟨j.isLt, hσ⟩
      rw [hu _ hmem, complexSVD_normalizedImage, dite_eq_left j.isLt, smul_smul,
        mul_inv_cancel₀ hσℂ, one_smul]
  · rw [dite_eq_right hjm]
    apply complexSVD_image_eigenvectorBasis_eq_zero T hn j
    exact complexSVD_singularValues_eq_zero_of_finrank_codomain_le T hm
      (Nat.le_of_not_gt hjm)

private theorem complexSVD_toMatrix_eq_rectangularDiagonal
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {n m : ℕ}
    (T : E →ₗ[ℂ] F) (v : OrthonormalBasis (Fin n) ℂ E)
    (u : OrthonormalBasis (Fin m) ℂ F) (σ : Fin n → ℝ)
    (h : ∀ j : Fin n, T (v j) = if hj : j.val < m then (σ j : ℂ) • u ⟨j.val, hj⟩ else 0) :
    LinearMap.toMatrix v.toBasis u.toBasis T =
      Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change u.toBasis.repr (T (v j)) i = if i.val = j.val then (σ j : ℂ) else 0
  rw [h j]
  by_cases hj : j.val < m
  · rw [dite_eq_left hj, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, inner_smul_right, u.inner_eq_ite]
    by_cases hij : i = ⟨j.val, hj⟩
    · subst hij; simp
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp [hij, hne]
  · rw [dite_eq_right hj]
    have hne : i.val ≠ j.val := fun hij => hj (hij ▸ i.isLt)
    simp [hne]

/--
Every rectangular complex matrix becomes rectangular diagonal after a unitary
change of basis on the right, with a further unitary change of basis on the
codomain (S. Axler, Linear Algebra Done Right, 4th ed., Section 7E).
-/
theorem exists_unitaryGroup_mul_eq_rectangularDiagonal
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (U : Matrix.unitaryGroup (Fin m) ℂ) (V : Matrix.unitaryGroup (Fin n) ℂ)
        (σ : Fin n → ℝ),
      (∀ j, 0 ≤ σ j) ∧ Antitone σ ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
      A * (V : Matrix (Fin n) (Fin n) ℂ) =
        (U : Matrix (Fin m) (Fin m) ℂ) *
          Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0) := by
  classical
  let T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
    Matrix.toEuclideanLin A
  let v := T.isSymmetric_adjoint_comp_self.eigenvectorBasis finrank_euclideanSpace_fin
  obtain ⟨u, hu⟩ := complexSVD_exists_leftBasis T finrank_euclideanSpace_fin
    finrank_euclideanSpace_fin
  have hA : LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℂ).toBasis T = A := by
    change LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin m) ℂ).toBasis (Matrix.toEuclideanLin A) = A
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact LinearMap.toMatrix_toLin _ _ _
  have hdiag : LinearMap.toMatrix v.toBasis u.toBasis T =
      Matrix.of (fun i j => if i.val = j.val then (T.singularValues j.val : ℂ) else 0) := by
    refine complexSVD_toMatrix_eq_rectangularDiagonal T v u
      (fun j => T.singularValues j.val) ?_
    intro j
    exact hu j
  refine ⟨⟨(EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix u,
      (EuclideanSpace.basisFun (Fin m) ℂ).toMatrix_orthonormalBasis_mem_unitary u⟩,
    ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix v,
      (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary v⟩,
    fun j => T.singularValues j.val, ?_, ?_, ?_, ?_⟩
  · exact fun j => T.singularValues_nonneg j.val
  · intro i j hij
    exact T.singularValues_antitone hij
  · intro j hj
    exact complexSVD_singularValues_eq_zero_of_finrank_codomain_le T
      finrank_euclideanSpace_fin hj
  · calc
      A * (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix v =
          LinearMap.toMatrix v.toBasis (EuclideanSpace.basisFun (Fin m) ℂ).toBasis T := by
            rw [← hA]
            exact linearMap_toMatrix_mul_basis_toMatrix v.toBasis
              (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
              (EuclideanSpace.basisFun (Fin m) ℂ).toBasis T
      _ = (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix u *
          LinearMap.toMatrix v.toBasis u.toBasis T := by
            symm
            exact basis_toMatrix_mul_linearMap_toMatrix v.toBasis
              (EuclideanSpace.basisFun (Fin m) ℂ).toBasis u.toBasis T
      _ = (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix u *
          Matrix.of (fun i j => if i.val = j.val then (T.singularValues j.val : ℂ) else 0) := by
            exact congrArg
              ((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.toMatrix u * ·) hdiag

/--
This is the rectangular complex SVD with singular values in nonincreasing order.

Proof: Multiply the rectangular-diagonal factorization on the right by `Vᴴ`.
-/
theorem exists_unitaryGroup_rectangularDiagonal_antitone
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (U : Matrix.unitaryGroup (Fin m) ℂ) (V : Matrix.unitaryGroup (Fin n) ℂ)
        (σ : Fin n → ℝ),
      (∀ j, 0 ≤ σ j) ∧ Antitone σ ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
      A = (U : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0) *
          star (V : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨U, V, σ, hσ, hanti, hzero, hAV⟩ :=
    exists_unitaryGroup_mul_eq_rectangularDiagonal m n A
  refine ⟨U, V, σ, hσ, hanti, hzero, ?_⟩
  have hVVt : (V : Matrix (Fin n) (Fin n) ℂ) *
      star (V : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp V.2
  calc
    A = A * 1 := (Matrix.mul_one A).symm
    _ = A * ((V : Matrix (Fin n) (Fin n) ℂ) *
        star (V : Matrix (Fin n) (Fin n) ℂ)) := by rw [hVVt]
    _ = (A * (V : Matrix (Fin n) (Fin n) ℂ)) *
        star (V : Matrix (Fin n) (Fin n) ℂ) := by rw [Matrix.mul_assoc]
    _ = ((U : Matrix (Fin m) (Fin m) ℂ) *
        Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0)) *
        star (V : Matrix (Fin n) (Fin n) ℂ) := by
      rw [hAV]

/--
Frobenius-norm identity for an SVD: the sum of the squared singular values is
the sum of the squared norms of the entries.
-/
theorem sum_sq_singularValues_eq_sum_sq_norm_of_svd {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) {U : Matrix (Fin m) (Fin m) ℂ}
    {V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    {σ : Fin n → ℝ} (hσ : ∀ j, m ≤ j.val → σ j = 0)
    (hA : A = U * Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0) * star V) :
    ∑ j, σ j ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  classical
  set S : Matrix (Fin m) (Fin n) ℂ :=
    Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0) with hS
  have hstarσ : ∀ j, star (↑(σ j) : ℂ) = (↑(σ j) : ℂ) := fun j => Complex.conj_ofReal _
  have hnorm : ∀ z : ℂ, star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    show (starRingEnd ℂ z) * z = ((‖z‖ ^ 2 : ℝ) : ℂ)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hstarA : Aᴴ = V * (Sᴴ * Uᴴ) := by
    rw [hA]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hUU : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  have hVV : Vᴴ * V = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hV
  have hAA : Aᴴ * A = V * (Sᴴ * S) * Vᴴ := by
    rw [hstarA, hA, Matrix.star_eq_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (S * Vᴴ), hUU, Matrix.one_mul]
  have htrace : Matrix.trace (Aᴴ * A) = Matrix.trace (Sᴴ * S) := by
    rw [hAA, Matrix.trace_mul_comm (V * (Sᴴ * S)) Vᴴ,
      ← Matrix.mul_assoc Vᴴ V (Sᴴ * S), hVV, Matrix.one_mul]
  have hterm : ∀ j : Fin n, (Sᴴ * S) j j = ((σ j ^ 2 : ℝ) : ℂ) := by
    intro j
    rw [Matrix.mul_apply]
    by_cases hj : j.val < m
    · have hsum : (∑ k, Sᴴ j k * S k j) =
          Sᴴ j (⟨j.val, hj⟩ : Fin m) * S (⟨j.val, hj⟩ : Fin m) j := by
        apply Finset.sum_eq_single_of_mem (⟨j.val, hj⟩ : Fin m) (Finset.mem_univ _)
        intro b _ hb
        have hne : b.val ≠ j.val := fun h => hb (Fin.ext h)
        rw [Matrix.conjTranspose_apply]
        have h1 : S b j = 0 := by
          simp only [hS, Matrix.of_apply, ite_eq_right hne]
        rw [h1, star_zero, zero_mul]
      rw [hsum]
      have h1 : S (⟨j.val, hj⟩ : Fin m) j = (↑(σ j) : ℂ) := by
        simp only [hS, Matrix.of_apply, ite_true]
      have h2 : Sᴴ j (⟨j.val, hj⟩ : Fin m) = (↑(σ j) : ℂ) := by
        rw [Matrix.conjTranspose_apply, h1, hstarσ]
      rw [h2, h1, ← Complex.ofReal_mul, pow_two]
    · have hσj : σ j = 0 := hσ j (Nat.le_of_not_gt hj)
      have hzero : ∑ i, Sᴴ j i * S i j = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hne : i.val ≠ j.val := by
          have hi : i.val < m := i.isLt
          omega
        rw [Matrix.conjTranspose_apply]
        have h1 : S i j = 0 := by
          simp only [hS, Matrix.of_apply, ite_eq_right hne]
        rw [h1, star_zero, zero_mul]
      rw [hzero, hσj]
      simp
  have htraceS : Matrix.trace (Sᴴ * S) = ((∑ j, σ j ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => hterm j
  have htraceA : Matrix.trace (Aᴴ * A) =
      ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, hnorm]
    rw [Finset.sum_comm]
    simp only [← Complex.ofReal_sum]
  have hcast : ((∑ j, σ j ^ 2 : ℝ) : ℂ) =
      ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) :=
    htraceS.symm.trans htrace.symm |>.trans htraceA
  exact Complex.ofReal_injective hcast

end Matrix

namespace MathlibExt.LinearAlgebra.Matrix.ComplexSVDWanted

/--
Rectangular complex singular value decomposition: every complex `m × n` matrix
factors as `U * Σ * Vᴴ` with `U` and `V` unitary and `Σ` rectangular diagonal
with nonnegative entries; the singular values beyond the first `min m n`
(indices `j` with `m ≤ j.val`) are zero.

Sources: S. Axler, Linear Algebra Done Right, 4th ed., Section 7E; G. H. Golub
and C. F. Van Loan, Matrix Computations, 4th ed., Johns Hopkins University
Press (2013), Theorem 2.4.1.

Proof: Apply the spectral theorem to `AᴴA`, normalize the images of the
eigenvectors with positive eigenvalues, and extend them to an orthonormal basis
of the codomain, as in the proof of S. Axler, Linear Algebra Done Right,
4th ed., 7.70, and the matrix form that follows it (Section 7E).
-/
theorem complex_singular_value_decomposition (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (V : Matrix (Fin n) (Fin n) ℂ) (σ : Fin n → ℝ),
      (∀ j, 0 ≤ σ j) ∧ (∀ j, m ≤ j.val → σ j = 0) ∧
      U ∈ Matrix.unitaryGroup (Fin m) ℂ ∧ V ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      A = U * Matrix.of (fun i j => if i.val = j.val then (σ j : ℂ) else 0) *
        star V := by
  obtain ⟨U, V, σ, hσ, -, hzero, hA⟩ :=
    Matrix.exists_unitaryGroup_rectangularDiagonal_antitone m n A
  exact ⟨U, V, σ, hσ, hzero, U.2, V.2, hA⟩

end MathlibExt.LinearAlgebra.Matrix.ComplexSVDWanted
