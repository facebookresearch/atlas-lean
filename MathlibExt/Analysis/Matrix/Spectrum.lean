/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.RealRooted
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Spectral norm and largest roots

This file identifies the L2 operator norm of a positive semidefinite matrix with the largest root
of its characteristic polynomial.
-/

@[expose] public section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Matrix

private lemma ksL2_opNorm_eq_norm_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) :
    ‖A‖ = ‖fun i ↦ (hA.eigenvalues i : ℂ)‖ := by
  calc
    ‖A‖ = ‖((Unitary.conjStarAlgAut ℂ (Matrix n n ℂ)) hA.eigenvectorUnitary)
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))‖ :=
      congrArg norm hA.spectral_theorem
    _ = ‖fun i ↦ (hA.eigenvalues i : ℂ)‖ := by
      rw [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
        CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
        Matrix.l2_opNorm_diagonal]
      rfl

/-- **Hermitian matrices have real-rooted characteristic polynomials.** The characteristic
polynomial of a Hermitian complex matrix is real-rooted. -/
public theorem IsHermitian.charpoly_isRealRooted
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) : A.charpoly.IsRealRooted := by
  intro z hz
  rw [hA.roots_charpoly_eq_eigenvalues] at hz
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hz
  simp

/-- **Spectral norm of a positive semidefinite matrix.** Let $A$ be a positive semidefinite
complex square matrix indexed by a nonempty finite set. Then the operator norm of $A$ with
respect to the Euclidean ($\ell^2$) norm equals the largest real part of a root of the
characteristic polynomial of $A$. Since these roots are real, this is its largest root. -/
public theorem PosSemidef.l2_opNorm_eq_maxRealRoot_charpoly
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] {A : Matrix n n ℂ}
    (hA : A.PosSemidef) : ‖A‖ = A.charpoly.maxRealRoot := by
  rw [ksL2_opNorm_eq_norm_eigenvalues hA.1]
  have heigen_root (i : n) : (hA.1.eigenvalues i : ℂ) ∈ A.charpoly.roots := by
    rw [hA.1.roots_charpoly_eq_eigenvalues]
    apply Multiset.mem_map.mpr
    exact ⟨i, by simp, rfl⟩
  have heigen_le (i : n) : hA.1.eigenvalues i ≤ A.charpoly.maxRealRoot :=
    A.charpoly.root_re_le_maxRealRoot (heigen_root i)
  let i₀ : n := Classical.choice inferInstance
  have hmax_nonneg : 0 ≤ A.charpoly.maxRealRoot :=
    (hA.eigenvalues_nonneg i₀).trans (heigen_le i₀)
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg hmax_nonneg).mpr
    intro i
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
    exact heigen_le i
  · have hdegree : 0 < A.charpoly.natDegree := by
      rw [Matrix.charpoly_natDegree_eq_dim]
      exact Fintype.card_pos
    have hroot : (A.charpoly.maxRealRoot : ℂ) ∈ A.charpoly.roots :=
      A.charpoly.coe_maxRealRoot_mem_roots hA.1.charpoly_isRealRooted hdegree
    rw [hA.1.roots_charpoly_eq_eigenvalues] at hroot
    obtain ⟨i, hi, heq⟩ := Multiset.mem_map.mp hroot
    have hmax_eq : A.charpoly.maxRealRoot = hA.1.eigenvalues i := by
      have hre := congrArg Complex.re heq
      simpa using hre.symm
    rw [hmax_eq]
    calc
      hA.1.eigenvalues i = ‖(hA.1.eigenvalues i : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA.eigenvalues_nonneg i)]
      _ ≤ ‖fun j ↦ (hA.1.eigenvalues j : ℂ)‖ :=
        norm_le_pi_norm (fun j ↦ (hA.1.eigenvalues j : ℂ)) i

end Matrix
