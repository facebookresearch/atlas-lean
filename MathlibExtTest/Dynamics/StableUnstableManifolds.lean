/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.StableUnstableManifolds
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.Dynamics.StableUnstableManifolds

open MathlibExt.Dynamics.StableUnstableManifoldsWanted.Dynamics.StableUnstableManifoldsProblem
open Filter Polynomial
open scoped Topology

private noncomputable def saddleMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![1 / 2, 2]

private noncomputable def saddle : E 2 →L[ℝ] E 2 :=
  saddleMatrix.toEuclideanLin.toContinuousLinearMap

private theorem saddle_roots :
    complexEigenvalues saddle = ({(1 / 2 : ℂ), 2} : Multiset ℂ) := by
  change (saddleMatrix.toEuclideanLin.charpoly.map (algebraMap ℝ ℂ)).roots = _
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.charpoly_toLin]
  simp [saddleMatrix, Matrix.charpoly_diagonal, Fin.prod_univ_two]
  rw [Polynomial.roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C, Multiset.singleton_add]

private theorem saddle_hyperbolic : IsHyperbolicLinear saddle := by
  intro μ hμ
  rw [saddle_roots] at hμ
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hμ
  rcases hμ with rfl | rfl
  · norm_num [norm_div, Complex.norm_two]
  · norm_num [Complex.norm_two]

private theorem saddle_invertible : saddle.IsInvertible := by
  have hdet : saddle.det ≠ 0 := by
    change saddleMatrix.toEuclideanLin.det ≠ 0
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, LinearMap.det_toLin]
    norm_num [saddleMatrix, Matrix.det_diagonal, Fin.prod_univ_two]
  exact ⟨saddle.toContinuousLinearEquivOfDetNeZero hdet, rfl⟩

-- Both contraction and expansion occur in this example.
example :
    ∃ U : Set (E 2), IsOpen U ∧ 0 ∈ U ∧
      {x | (∀ k : ℕ, saddle^[k] x ∈ U) ∧
            Tendsto (fun k => saddle^[k] x) atTop (𝓝 0)} ∩
      {x | ∃ y : ℕ → E 2, y 0 = x ∧ (∀ k, y k ∈ U) ∧
            (∀ k, saddle (y (k + 1)) = y k) ∧ Tendsto y atTop (𝓝 0)} = {0} := by
  have hderiv : fderiv ℝ saddle 0 = saddle := saddle.fderiv
  obtain ⟨U, hU, hzero, _, _, rfl, rfl, h⟩ := stable_unstable_manifolds_exist
    2 saddle 0 saddle.contDiff.contDiffAt (map_zero saddle)
    (hderiv.symm ▸ saddle_hyperbolic) (hderiv.symm ▸ saddle_invertible)
  exact ⟨U, hU, hzero, h⟩

-- An eigenvalue on the unit circle is excluded, including with multiplicity two.
example : ¬ IsHyperbolicLinear (1 : E 2 →L[ℝ] E 2) := by
  intro h
  have hroots : complexEigenvalues (1 : E 2 →L[ℝ] E 2) = ({1, 1} : Multiset ℂ) := by
    change (((1 : E 2 →ₗ[ℝ] E 2).charpoly).map (algebraMap ℝ ℂ)).roots = _
    rw [LinearMap.charpoly_one, finrank_euclideanSpace_fin, Polynomial.map_pow,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.roots_pow]
    have h₁ : (X - 1 : ℂ[X]).roots = {1} := by simpa using roots_X_sub_C (1 : ℂ)
    rw [h₁, two_smul, Multiset.singleton_add, Multiset.insert_eq_cons]
  exact h 1 (by rw [hroots]; simp [Multiset.insert_eq_cons]) norm_one

end MathlibExtTest.Dynamics.StableUnstableManifolds
