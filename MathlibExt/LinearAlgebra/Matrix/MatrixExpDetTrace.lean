/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Matrix.Normed

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Determinant and finite-series formulas for the matrix exponential

This file proves that the determinant of a complex matrix exponential is the exponential of its
trace, and that the exponential series truncates for a nilpotent matrix.
-/

@[expose] public section

open scoped BigOperators

namespace MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem matrixExp_exp_eq_sum_of_pow_eq_zero (A : Matrix n n ℂ) {m : ℕ}
    (hA : A ^ m = 0) :
    NormedSpace.exp A = ∑ k ∈ Finset.range m, (Nat.factorial k : ℂ)⁻¹ • A ^ k := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  exact tsum_eq_sum fun k hk ↦ by
    have hmk : m ≤ k := Nat.le_of_not_gt fun hkm ↦ hk (Finset.mem_range.mpr hkm)
    rw [pow_eq_zero_of_le hmk hA, smul_zero]

omit [Fintype n] [DecidableEq n] in
private theorem matrixExp_exp_pi_apply [Finite n] (v : n → ℂ) (i : n) :
    NormedSpace.exp v i = Complex.exp (v i) := by
  let _ := Fintype.ofFinite n
  simpa only [Pi.evalRingHom_apply, Complex.exp_eq_exp_ℂ] using
    (NormedSpace.map_exp (Pi.evalRingHom (fun _ : n ↦ ℂ) i) (continuous_apply i) v)

private theorem matrixExp_det_exp_diagonal (v : n → ℂ) :
    Matrix.det (NormedSpace.exp (Matrix.diagonal v)) =
      Complex.exp (Matrix.trace (Matrix.diagonal v)) := by
  rw [Matrix.exp_diagonal, Matrix.det_diagonal, Matrix.trace_diagonal, Complex.exp_sum]
  simp_rw [matrixExp_exp_pi_apply]

omit [Fintype n] [DecidableEq n] in
private theorem matrixExp_dfinsupp_basis_apply
    {R ι : Type*} [Semiring R] [DecidableEq ι] {M : ι → Type*}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] {η : ι → Type*}
    (b : ∀ i, Module.Basis (η i) R (M i)) (i : Σ x, η x) :
    DFinsupp.basis b i = DFinsupp.single i.1 (b i.1 i.2) := by
  rcases i with ⟨x, i⟩
  apply Module.Basis.apply_eq_iff.mpr
  ext ⟨y, j⟩
  by_cases hxy : x = y
  · subst y
    simp [DFinsupp.basis]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  · simp [DFinsupp.basis, hxy]

omit [Fintype n] [DecidableEq n] in
private noncomputable def matrixExp_eigenbasis {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) :
    Module.Basis (Σ z, Module.Basis.ofVectorSpaceIndex ℂ (f.eigenspace z)) ℂ V := by
  classical
  let b (z : ℂ) := Module.Basis.ofVectorSpace ℂ (f.eigenspace z)
  exact (DFinsupp.basis b).map (f.eigenspaces_iSupIndep.linearEquiv h)

omit [Fintype n] [DecidableEq n] in
private theorem matrixExp_eigenbasis_apply_mem {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤)
    (i : Σ z, Module.Basis.ofVectorSpaceIndex ℂ (f.eigenspace z)) :
    matrixExp_eigenbasis f h i ∈ f.eigenspace i.1 := by
  classical
  rw [matrixExp_eigenbasis, Module.Basis.map_apply, matrixExp_dfinsupp_basis_apply,
    iSupIndep.linearEquiv_apply, DFinsupp.sumAddHom_single]
  exact (Module.Basis.ofVectorSpace ℂ (f.eigenspace i.1) i.2).property

omit [Fintype n] [DecidableEq n] in
private noncomputable def matrixExp_diagonalizingBasis
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] (b₀ : Module.Basis ι ℂ V)
    (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) : Module.Basis ι ℂ V :=
  (matrixExp_eigenbasis f h).reindex (b₀.indexEquiv (matrixExp_eigenbasis f h)).symm

omit [Fintype n] [DecidableEq n] in
private noncomputable def matrixExp_diagonalizingEigenvalue
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] (b₀ : Module.Basis ι ℂ V)
  (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) (i : ι) : ℂ :=
  (b₀.indexEquiv (matrixExp_eigenbasis f h) i).1

omit [Fintype n] [DecidableEq n] in
private theorem matrixExp_diagonalizingBasis_apply_mem
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] (b₀ : Module.Basis ι ℂ V)
    (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) (i : ι) :
    matrixExp_diagonalizingBasis b₀ f h i ∈
      f.eigenspace (matrixExp_diagonalizingEigenvalue b₀ f h i) := by
  rw [matrixExp_diagonalizingBasis, Module.Basis.reindex_apply]
  exact matrixExp_eigenbasis_apply_mem f h (b₀.indexEquiv (matrixExp_eigenbasis f h) i)

omit [Fintype n] [DecidableEq n] in
private theorem matrixExp_toMatrix_diagonalizingBasis
    {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι] [DecidableEq ι]
    (b₀ : Module.Basis ι ℂ V) (f : Module.End ℂ V) (h : ⨆ z, f.eigenspace z = ⊤) :
    LinearMap.toMatrix (matrixExp_diagonalizingBasis b₀ f h)
        (matrixExp_diagonalizingBasis b₀ f h) f =
      Matrix.diagonal (matrixExp_diagonalizingEigenvalue b₀ f h) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply,
    Module.End.mem_eigenspace_iff.mp (matrixExp_diagonalizingBasis_apply_mem b₀ f h j),
    map_smul, Module.Basis.repr_self]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

private noncomputable def matrixExp_changeBasisAlgEquiv
    (b : Module.Basis n ℂ (n → ℂ)) : Matrix n n ℂ ≃ₐ[ℂ] Matrix n n ℂ :=
  (Matrix.toLinAlgEquiv' : Matrix n n ℂ ≃ₐ[ℂ] Module.End ℂ (n → ℂ)).trans
    (LinearMap.toMatrixAlgEquiv b)

open scoped Matrix.Norms.Operator in
private theorem matrixExp_changeBasis_exp (b : Module.Basis n ℂ (n → ℂ))
    (A : Matrix n n ℂ) :
    matrixExp_changeBasisAlgEquiv b (NormedSpace.exp A) =
      NormedSpace.exp (matrixExp_changeBasisAlgEquiv b A) := by
  let e := matrixExp_changeBasisAlgEquiv b
  let f : Matrix n n ℂ →+* Matrix n n ℂ := e.toRingEquiv.toRingHom
  have hc : Continuous f := by
    change Continuous e
    exact e.toLinearMap.continuous_of_finiteDimensional
  change f (NormedSpace.exp A) = NormedSpace.exp (f A)
  exact NormedSpace.map_exp f hc A

private theorem matrixExp_det_changeBasis (b : Module.Basis n ℂ (n → ℂ))
    (A : Matrix n n ℂ) :
    Matrix.det (matrixExp_changeBasisAlgEquiv b A) = Matrix.det A := by
  change Matrix.det (LinearMap.toMatrix b b (Matrix.toLin' A)) = Matrix.det A
  rw [LinearMap.det_toMatrix]
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℂ n)]
  rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

private theorem matrixExp_trace_changeBasis (b : Module.Basis n ℂ (n → ℂ))
    (A : Matrix n n ℂ) :
    Matrix.trace (matrixExp_changeBasisAlgEquiv b A) = Matrix.trace A := by
  change Matrix.trace (LinearMap.toMatrix b b (Matrix.toLin' A)) = Matrix.trace A
  rw [← LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_toLin'_eq]

private theorem matrixExp_det_exp_of_isSemisimple (A : Matrix n n ℂ)
    (hA : Module.End.IsSemisimple (Matrix.toLin' A)) :
    Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := by
  let f : Module.End ℂ (n → ℂ) := Matrix.toLin' A
  have htop : ⨆ z, f.eigenspace z = ⊤ := hA.iSup_eigenspace_eq_top
  let b₀ := Pi.basisFun ℂ n
  let b := matrixExp_diagonalizingBasis b₀ f htop
  let v := matrixExp_diagonalizingEigenvalue b₀ f htop
  have hdiag : matrixExp_changeBasisAlgEquiv b A = Matrix.diagonal v := by
    exact matrixExp_toMatrix_diagonalizingBasis b₀ f htop
  calc
    Matrix.det (NormedSpace.exp A) =
        Matrix.det (matrixExp_changeBasisAlgEquiv b (NormedSpace.exp A)) :=
      (matrixExp_det_changeBasis b (NormedSpace.exp A)).symm
    _ = Matrix.det (NormedSpace.exp (matrixExp_changeBasisAlgEquiv b A)) := by
      rw [matrixExp_changeBasis_exp]
    _ = Matrix.det (NormedSpace.exp (Matrix.diagonal v)) := by rw [hdiag]
    _ = Complex.exp (Matrix.trace (Matrix.diagonal v)) := matrixExp_det_exp_diagonal v
    _ = Complex.exp (Matrix.trace (matrixExp_changeBasisAlgEquiv b A)) := by rw [hdiag]
    _ = Complex.exp (Matrix.trace A) := by rw [matrixExp_trace_changeBasis]

private theorem matrixExp_det_one_add_of_isNilpotent (A : Matrix n n ℂ)
    (hA : IsNilpotent A) : Matrix.det (1 + A) = 1 := by
  obtain ⟨r, -, hchar⟩ := Polynomial.isUnit_iff.mp
    (Matrix.isUnit_charpolyRev_of_isNilpotent hA)
  have hr : r = 1 := by
    simpa using congrArg (Polynomial.eval 0) hchar
  have hchar' : A.charpolyRev = 1 := by rw [← hchar, hr, map_one]
  have heval := congrArg (Polynomial.eval (-1)) hchar'
  have hdiag : Matrix.diagonal (fun _ : n ↦ (-1 : ℂ)) = -1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  simpa [Matrix.charpolyRev, eval_det, hdiag] using heval

private theorem matrixExp_normed_exp_eq_nilpotent_exp (A : Matrix n n ℂ)
    (hA : IsNilpotent A) : NormedSpace.exp A = IsNilpotent.exp A := by
  obtain ⟨m, hm⟩ := hA
  rw [matrixExp_exp_eq_sum_of_pow_eq_zero A hm, IsNilpotent.exp_eq_sum hm]
  apply Finset.sum_congr rfl
  intro k _
  simpa using (ratCast_smul_eq ℂ ℚ ((k.factorial : ℚ)⁻¹) (A ^ k))

private theorem matrixExp_det_exp_of_isNilpotent (A : Matrix n n ℂ)
    (hA : IsNilpotent A) : Matrix.det (NormedSpace.exp A) = 1 := by
  have h : IsNilpotent (NormedSpace.exp A - 1) := by
    rw [matrixExp_normed_exp_eq_nilpotent_exp A hA]
    exact hA.isNilpotent_exp_sub_one
  simpa using matrixExp_det_one_add_of_isNilpotent (NormedSpace.exp A - 1) h

private theorem matrixExp_exists_isNilpotent_isSemisimple (A : Matrix n n ℂ) :
    ∃ N S : Matrix n n ℂ, IsNilpotent N ∧
      Module.End.IsSemisimple (Matrix.toLin' S) ∧ Commute N S ∧ A = N + S := by
  let f : Module.End ℂ (n → ℂ) := Matrix.toLin' A
  obtain ⟨N, hNmem, S, hSmem, hN, hS, hdecomp⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := f)
  let e : Module.End ℂ (n → ℂ) ≃ₐ[ℂ] Matrix n n ℂ :=
    LinearMap.toMatrixAlgEquiv (Pi.basisFun ℂ n)
  have he (g : Module.End ℂ (n → ℂ)) : e g = LinearMap.toMatrix' g := by
    change LinearMap.toMatrix (Pi.basisFun ℂ n) (Pi.basisFun ℂ n) g = _
    rw [LinearMap.toMatrix_eq_toMatrix']
  have hNS : Commute N S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hSmem
      (Algebra.commute_of_mem_adjoin_self hNmem).symm
  refine ⟨e N, e S, hN.map e, ?_, hNS.map e, ?_⟩
  · rw [he, Matrix.toLin'_toMatrix']
    exact hS
  · rw [he, he]
    have h := congrArg LinearMap.toMatrix' hdecomp
    simpa [f] using h

/--
Jacobi's formula: the determinant of the matrix exponential is the exponential of the trace.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Exponential / matrix exponential;
B. C. Hall, Lie Groups, Lie Algebras, and Representations, 2nd ed., Springer (2015),
Proposition 2.23.

Proves `Wanted` entry `matrix_det_exp_eq_exp_trace`.

Proof: the three cases of B. C. Hall, An Elementary Introduction to Groups and Representations,
https://arxiv.org/abs/math-ph/0005032, Theorem 3.10. The Jordan-Chevalley decomposition
(`Module.End.exists_isNilpotent_isSemisimple`) writes `A = N + S` with `N` nilpotent, `S`
semisimple and `N`, `S` commuting, so `exp A = exp N * exp S`. Diagonalizing `S` gives
`det (exp S) = exp (trace S)`. For the nilpotent part, where Hall uses a strictly upper-triangular
form, `exp N - 1` is nilpotent, so `det (exp N) = 1`, while `trace N = 0`.
-/
theorem matrix_det_exp_eq_exp_trace (A : Matrix n n ℂ) :
    Matrix.det (NormedSpace.exp A) = Complex.exp (Matrix.trace A) := by
  obtain ⟨N, S, hN, hS, hNS, rfl⟩ := matrixExp_exists_isNilpotent_isSemisimple A
  have htraceN : Matrix.trace N = 0 :=
    (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [Matrix.exp_add_of_commute N S hNS, Matrix.det_mul,
    matrixExp_det_exp_of_isNilpotent N hN, matrixExp_det_exp_of_isSemisimple S hS,
    Matrix.trace_add, htraceN, zero_add, one_mul]

/--
The exponential of a nilpotent matrix is a finite partial sum of the exponential series.

Sources: Mathlib `docs/undergrad.yaml`, Linear algebra / Exponential / matrix exponential;
R. A. Horn and C. R. Johnson, Matrix Analysis, 2nd ed., Cambridge University Press (2013),
Section 3.2.

Proves `Wanted` entry `matrix_exp_eq_sum_of_isNilpotent`.

Proof: if `A ^ m = 0`, every term of the exponential series from index `m` on vanishes.
-/
theorem matrix_exp_eq_sum_of_isNilpotent (A : Matrix n n ℂ) (h : IsNilpotent A) :
    ∃ m : ℕ, NormedSpace.exp A = ∑ k ∈ Finset.range m, (Nat.factorial k : ℂ)⁻¹ • A ^ k := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, matrixExp_exp_eq_sum_of_pow_eq_zero A hm⟩

end MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted
