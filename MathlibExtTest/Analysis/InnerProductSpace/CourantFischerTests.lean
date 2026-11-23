/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CauchyInterlacing
public import MathlibExt.Analysis.InnerProductSpace.CourantFischer
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for Courant–Fischer and Cauchy interlacing

The diagonal operator `diag (3, 1)` on `EuclideanSpace ℝ (Fin 2)` has
eigenvalues `3, 1`. The tests check:

* the eigenvalues of the diagonal operator, via its characteristic
  polynomial;
* the Rayleigh form on the two coordinate vectors;
* the min–max and max–min statements (extremal subspaces and the
  lower-bound forms), with the attaining vector giving the exact
  eigenvalue `1` at `k = 1`;
* Cauchy interlacing for the compression to the first coordinate axis:
  `1 ≤ 3 ≤ 3`.
-/

namespace MathlibExtTest.Analysis.InnerProductSpace.CourantFischerTests

open Filter Topology
open scoped _root_.InnerProductSpace
open MathlibExt.Analysis.InnerProductSpace.CourantFischer
open MathlibExt.Analysis.InnerProductSpace.CauchyInterlacing
open Polynomial

/-- The diagonal operator with eigenvalues `3, 1` on `ℝ²`. -/
noncomputable def testDiag : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Matrix.diagonal ![3, 1]).toEuclideanLin

/-- The diagonal operator is symmetric. -/
theorem testDiag_isSymmetric : testDiag.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_diagonal _)

/-- The dimension of the test space. -/
theorem testFinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 :=
  finrank_euclideanSpace_fin

/-- The diagonal operator acts by its diagonal entries on basis vectors. -/
theorem testDiag_basisFun (i : Fin 2) :
    testDiag ((EuclideanSpace.basisFun (Fin 2) ℝ) i) =
      (![3, 1] : Fin 2 → ℝ) i • (EuclideanSpace.basisFun (Fin 2) ℝ) i := by
  show Matrix.toLin (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (Matrix.diagonal ![3, 1])
      ((EuclideanSpace.basisFun (Fin 2) ℝ).toBasis i) = _
  rw [Matrix.toLin_self, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq, OrthonormalBasis.coe_toBasis]
  · intro j _ hji
    rw [Matrix.diagonal_apply_ne _ hji, zero_smul]
  · simp

/-- The diagonal operator acts by its diagonal entries on coordinate vectors. -/
theorem testDiag_single (i : Fin 2) :
    testDiag (EuclideanSpace.single i 1) =
      (![3, 1] : Fin 2 → ℝ) i • EuclideanSpace.single i 1 := by
  rw [← EuclideanSpace.basisFun_apply (Fin 2) ℝ i]
  exact testDiag_basisFun i

/-- The eigenvalues of the diagonal operator are `3, 1`. -/
theorem testDiag_eigenvalues :
    testDiag_isSymmetric.eigenvalues testFinrank = ![3, 1] := by
  have hchar : testDiag.charpoly =
      ∏ i : Fin 2, (X - C ((![3, 1] : Fin 2 → ℝ) i)) := by
    show ((Matrix.diagonal (![3, 1] : Fin 2 → ℝ)).toEuclideanLin :
        EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).charpoly = _
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    have h := LinearMap.charpoly_toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (f := Matrix.toLin (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis (Matrix.diagonal ![3, 1]))
    rw [← h, LinearMap.toMatrix_toLin, Matrix.charpoly_diagonal]
  have hroots : testDiag.charpoly.roots = {3, 1} := by
    rw [hchar, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Polynomial.roots_mul
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero _) (Polynomial.X_sub_C_ne_zero _)),
      Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C]
    rfl
  have hsort := testDiag_isSymmetric.sort_roots_charpoly_eq_eigenvalues testFinrank
  have hmap : ({3, 1} : Multiset ℝ).map RCLike.re = {3, 1} := by
    have h : ∀ x ∈ ({3, 1} : Multiset ℝ), RCLike.re x = x := fun x _ => rfl
    rw [Multiset.map_congr rfl h]
    rfl
  have hmul : ((List.ofFn (testDiag_isSymmetric.eigenvalues testFinrank) : List ℝ) :
      Multiset ℝ) = {3, 1} := by
    rw [← hsort, Multiset.sort_eq, hroots]
    exact hmap
  have hperm : List.Perm (List.ofFn (testDiag_isSymmetric.eigenvalues testFinrank)) [3, 1] := by
    have h2 : ((List.ofFn (testDiag_isSymmetric.eigenvalues testFinrank) : List ℝ) :
        Multiset ℝ) = (([3, 1] : List ℝ) : Multiset ℝ) := by
      rw [hmul]
      rfl
    exact Multiset.coe_eq_coe.mp h2
  have hsorted : (List.ofFn (testDiag_isSymmetric.eigenvalues testFinrank)).SortedGE :=
    (testDiag_isSymmetric.eigenvalues_antitone testFinrank).sortedGE_ofFn
  have hsorted2 : ([3, 1] : List ℝ).SortedGE := by
    rw [List.sortedGE_iff_pairwise]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
    · intro y hy
      simp only [List.mem_singleton] at hy
      rw [hy]
      norm_num
    · intro y hy
      simp at hy
  have hlist : List.ofFn (testDiag_isSymmetric.eigenvalues testFinrank) = [3, 1] :=
    hperm.eq_of_sortedGE hsorted hsorted2
  have hof : List.ofFn (![3, 1] : Fin 2 → ℝ) = [3, 1] := rfl
  exact List.ofFn_inj.mp (hlist.trans hof.symm)

/-- The Rayleigh form on the first coordinate vector is `3`. -/
example : rayleighForm testDiag (EuclideanSpace.single 0 1) = 3 := by
  unfold rayleighForm
  rw [testDiag_single 0]
  have h0 : (![3, 1] : Fin 2 → ℝ) 0 = 3 := rfl
  rw [h0, inner_smul_left, ← EuclideanSpace.basisFun_apply (Fin 2) ℝ 0]
  simp

/-- The Rayleigh form on the second coordinate vector is `1`. -/
example : rayleighForm testDiag (EuclideanSpace.single 1 1) = 1 := by
  unfold rayleighForm
  rw [testDiag_single 1]
  have h1 : (![3, 1] : Fin 2 → ℝ) 1 = 1 := rfl
  rw [h1, inner_smul_left, ← EuclideanSpace.basisFun_apply (Fin 2) ℝ 1]
  simp

/-- Min–max at `k = 0`: there is a unit vector with Rayleigh quotient `3`. -/
example : ∃ x : EuclideanSpace ℝ (Fin 2), ‖x‖ = 1 ∧
    rayleighForm testDiag x = 3 := by
  obtain ⟨W, hWdim, hWbound, ⟨x, hxW, hx1, hxeq⟩⟩ :=
    exists_tail_submodule testDiag_isSymmetric testFinrank (show (0:ℕ) < 2 by norm_num)
  refine ⟨x, hx1, ?_⟩
  rw [hxeq, testDiag_eigenvalues]
  rfl

/-- Min–max at `k = 1`: the extremal subspace has dimension `1`, and the
attaining vector has Rayleigh quotient `1`. -/
example : ∃ W : Submodule ℝ (EuclideanSpace ℝ (Fin 2)),
    Module.finrank ℝ W = 1 ∧ ∃ x ∈ W, ‖x‖ = 1 ∧ rayleighForm testDiag x = 1 := by
  obtain ⟨W, hWdim, hWbound, ⟨x, hxW, hx1, hxeq⟩⟩ :=
    exists_tail_submodule testDiag_isSymmetric testFinrank (show (1:ℕ) < 2 by norm_num)
  refine ⟨W, hWdim, ⟨x, hxW, hx1, ?_⟩⟩
  rw [hxeq, testDiag_eigenvalues]
  rfl

/-- Min–max lower-bound form at `k = 0`: every `2`-dimensional subspace
contains a unit vector with Rayleigh quotient at least `3`. -/
example : ∃ x ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))), ‖x‖ = 1 ∧
    3 ≤ rayleighForm testDiag x := by
  obtain ⟨x, hxW, hx1, hge⟩ := exists_unit_ge_of_submodule testDiag_isSymmetric
    testFinrank (show (0:ℕ) < 2 by norm_num) ⊤ (by simp)
  refine ⟨x, hxW, hx1, ?_⟩
  have h0 : testDiag_isSymmetric.eigenvalues testFinrank ⟨0, by norm_num⟩ = 3 := by
    rw [testDiag_eigenvalues]
    rfl
  rw [h0] at hge
  exact hge

/-- Max–min lower-bound form at `k = 1`: every `2`-dimensional subspace
contains a unit vector with Rayleigh quotient at most `1`. -/
example : ∃ x ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))), ‖x‖ = 1 ∧
    rayleighForm testDiag x ≤ 1 := by
  obtain ⟨x, hxW, hx1, hle⟩ := exists_unit_le_of_submodule testDiag_isSymmetric
    testFinrank (show (1:ℕ) < 2 by norm_num) ⊤ (by simp)
  refine ⟨x, hxW, hx1, ?_⟩
  have h1 : testDiag_isSymmetric.eigenvalues testFinrank ⟨1, by norm_num⟩ = 1 := by
    rw [testDiag_eigenvalues]
    rfl
  rw [h1] at hle
  exact hle

/-- The first coordinate axis, a codimension-one subspace. -/
noncomputable def testAxis : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℝ {EuclideanSpace.single 0 1}

instance : CompleteSpace testAxis :=
  FiniteDimensional.complete (𝕜 := ℝ) (E := ↥testAxis)

instance : testAxis.HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace (K := testAxis)

/-- The first coordinate vector lies on the first coordinate axis. -/
theorem testAxis_mem : EuclideanSpace.single 0 1 ∈ testAxis := by
  unfold testAxis
  rw [Submodule.mem_span_singleton]
  exact ⟨1, by simp⟩

/-- The first coordinate axis has dimension `1`. -/
theorem testAxis_finrank : Module.finrank ℝ testAxis = 1 := by
  show Module.finrank ℝ (Submodule.span ℝ {EuclideanSpace.single 0 1}) = 1
  exact finrank_span_singleton (by
    intro h
    rw [← EuclideanSpace.basisFun_apply] at h
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero 0 h)

/-- The compression to the first coordinate axis has eigenvalue `3`. -/
theorem testCompression_eigenvalues (hS : Module.finrank ℝ testAxis = 2 - 1) :
    (compression_isSymmetric testDiag_isSymmetric testAxis).eigenvalues hS =
      ![3] := by
  have hact : ∀ y : testAxis,
      compression testDiag testAxis y = (3 : ℝ) • y := by
    intro y
    rw [compression_apply]
    have hy : (y : EuclideanSpace ℝ (Fin 2)) ∈ testAxis := y.2
    unfold testAxis at hy
    rw [Submodule.mem_span_singleton] at hy
    obtain ⟨a, ha⟩ := hy
    have hT : testDiag (y : EuclideanSpace ℝ (Fin 2)) =
        (3 : ℝ) • (y : EuclideanSpace ℝ (Fin 2)) := by
      rw [← ha, map_smul, testDiag_single 0]
      have h3 : (![3, 1] : Fin 2 → ℝ) 0 = 3 := rfl
      rw [h3, smul_smul, smul_smul, mul_comm]
    rw [hT, map_smul]
    congr 1
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y
  have hmem : (⟨EuclideanSpace.single 0 1, testAxis_mem⟩ : testAxis) ∈
      Module.End.eigenspace (compression testDiag testAxis) (3 : ℝ) := by
    rw [Module.End.mem_eigenspace_iff]
    exact hact _
  have hne : (⟨EuclideanSpace.single 0 1, testAxis_mem⟩ : testAxis) ≠ 0 := by
    intro h
    have h2 : EuclideanSpace.single (0 : Fin 2) (1 : ℝ) = 0 :=
      congrArg Subtype.val h
    rw [← EuclideanSpace.basisFun_apply] at h2
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.ne_zero 0 h2
  have heig : Module.End.HasEigenvalue (compression testDiag testAxis) (3 : ℝ) :=
    (Submodule.ne_bot_iff _).mpr ⟨_, hmem, hne⟩
  obtain ⟨i, hi⟩ :=
    (compression_isSymmetric testDiag_isSymmetric testAxis).exists_eigenvalues_eq hS heig
  have hi2 : (compression_isSymmetric testDiag_isSymmetric testAxis).eigenvalues hS
      i = 3 := by
    simpa using hi
  have ei : i = ⟨0, by norm_num⟩ := Fin.eq_zero i
  rw [ei] at hi2
  funext j
  rw [Fin.eq_zero j]
  show (compression_isSymmetric testDiag_isSymmetric testAxis).eigenvalues hS
      ⟨0, by norm_num⟩ = ![3] ⟨0, by norm_num⟩
  rw [hi2]
  rfl

/-- Cauchy interlacing for the compression to the first coordinate axis:
`1 ≤ 3 ≤ 3`. -/
example : (1 : ℝ) ≤ 3 ∧ (3 : ℝ) ≤ 3 := by
  have hS : Module.finrank ℝ testAxis = 2 - 1 := by
    rw [testAxis_finrank]
  obtain ⟨hlo, hhi⟩ := cauchy_interlacing testDiag_isSymmetric testFinrank
    testAxis hS (show (0 : ℕ) + 1 < 2 by norm_num)
  rw [testCompression_eigenvalues hS] at hlo hhi
  have h0 : testDiag_isSymmetric.eigenvalues testFinrank ⟨1, by norm_num⟩ = 1 := by
    rw [testDiag_eigenvalues]
    rfl
  have h1 : testDiag_isSymmetric.eigenvalues testFinrank ⟨0, by norm_num⟩ = 3 := by
    rw [testDiag_eigenvalues]
    rfl
  rw [h0] at hlo
  rw [h1] at hhi
  exact ⟨hlo, hhi⟩

end MathlibExtTest.Analysis.InnerProductSpace.CourantFischerTests
