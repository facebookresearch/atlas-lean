/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Spectral theorem for normal complex matrices

A normal complex matrix is unitarily diagonalizable: if
`star M * M = M * star M` (the condition `IsStarNormal M`), there is a unitary
matrix `P` and a diagonal `d` with
`star P * M * P = diagonal d`.

This is the normal-matrix part of the spectral theorem in AlgebraNotes
(Section: The Spectral Theorem, Subsection: The Spectral Theorem,
Theorem (Spectral Theorem)). The Hermitian cases of that theorem are already in
Mathlib (`Matrix.IsHermitian.spectral_theorem`), so they are not repeated here.

Adapted from `SpectralTheorem.normal_complex_unitarily_diagonalizable` in
`v1/Atlas/AlgebraNotes/code/SpectralTheorem.lean`, frozen at Git blob
`393e4c75ddc778f12a3b02e3fb1ef19f653cd76a`.
-/

@[expose] public section

namespace Matrix

set_option maxHeartbeats 1600000 in
/-- **Spectral theorem for normal matrices.** A normal complex matrix is unitarily
diagonalizable: there is a unitary `P` and a diagonal `d` with
`star P * M * P = diagonal d`.

Source: AlgebraNotes, Section: The Spectral Theorem, Subsection: The Spectral
Theorem, Theorem (Spectral Theorem) (normal-matrix case; the Hermitian cases are
Mathlib's `Matrix.IsHermitian.spectral_theorem`).

Adapted from `SpectralTheorem.normal_complex_unitarily_diagonalizable` in
`v1/Atlas/AlgebraNotes/code/SpectralTheorem.lean`, frozen at Git blob
`393e4c75ddc778f12a3b02e3fb1ef19f653cd76a`. -/
public theorem exists_unitary_diagonal_of_isStarNormal
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : IsStarNormal M) :
    ∃ (P : Matrix n n ℂ) (_ : P ∈ Matrix.unitaryGroup n ℂ) (d : n → ℂ),
      star P * M * P = diagonal d := by
  have hN : M.conjTranspose * M = M * M.conjTranspose := by
    have h := hM.star_comm_self
    simp only [star_eq_conjTranspose] at h
    exact h
  set H := (1 / 2 : ℂ) • (M + M.conjTranspose) with hH_def
  set K := (-(Complex.I) / 2 : ℂ) • (M - M.conjTranspose) with hK_def
  have hH_herm : H.IsHermitian := by
    ext i j
    simp only [hH_def, conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul, star_mul', star_add, RCLike.star_def, map_ofNat, map_one, map_div₀,
      starRingEnd_self_apply]
    have h : starRingEnd ℂ (M j i) = M.conjTranspose i j := by simp [conjTranspose_apply]
    rw [h]
    ring
  have hK_herm : K.IsHermitian := by
    ext i j
    simp only [hK_def, conjTranspose_apply, Matrix.smul_apply, Matrix.sub_apply,
      smul_eq_mul, star_mul', star_sub, RCLike.star_def, map_neg, map_div₀,
      map_ofNat, starRingEnd_self_apply, Complex.conj_I]
    have h : starRingEnd ℂ (M j i) = M.conjTranspose i j := by simp [conjTranspose_apply]
    rw [h]
    ring
  have hA_eq : M = H + Complex.I • K := by
    ext i j
    simp only [hH_def, hK_def, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      smul_eq_mul]
    ring_nf
    simp [Complex.I_sq]
    ring
  have hTh_sym : (toEuclideanLin H).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hH_herm
  have hTk_sym : (toEuclideanLin K).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hK_herm
  have hHK : H * K = K * H := by
    have key : (M + M.conjTranspose) * (M - M.conjTranspose) =
        (M - M.conjTranspose) * (M + M.conjTranspose) := by
      simp only [add_mul, mul_sub, sub_mul, mul_add]
      rw [show M * M.conjTranspose = M.conjTranspose * M from hN.symm]
      abel
    simp only [hH_def, hK_def, Matrix.smul_mul, Matrix.mul_smul]
    rw [key, smul_comm]
  have hcomm : Commute (toEuclideanLin H) (toEuclideanLin K) := by
    show toEuclideanLin H ∘ₗ toEuclideanLin K = toEuclideanLin K ∘ₗ toEuclideanLin H
    ext v
    simp only [LinearMap.comp_apply, toLpLin_apply, Matrix.mulVec_mulVec, hHK]
  have hdecomp := hTh_sym.directSum_isInternal_of_commute hTk_sym hcomm
  have horth := hTh_sym.orthogonalFamily_eigenspace_inf_eigenspace hTk_sym
  set W : ℂ × ℂ → Submodule ℂ (EuclideanSpace ℂ n) :=
    fun p => Module.End.eigenspace (toEuclideanLin H) p.2 ⊓
      Module.End.eigenspace (toEuclideanLin K) p.1
  have hfin : Finite {p : ℂ × ℂ // W p ≠ ⊥} := by
    apply Finite.of_injective
      (fun (s : {p : ℂ × ℂ // W p ≠ ⊥}) =>
        (show Module.End.Eigenvalues (toEuclideanLin K) from
          ⟨s.1.1, Module.End.hasEigenvalue_iff.mpr
            (ne_bot_of_le_ne_bot s.2 inf_le_right)⟩,
         show Module.End.Eigenvalues (toEuclideanLin H) from
          ⟨s.1.2, Module.End.hasEigenvalue_iff.mpr
            (ne_bot_of_le_ne_bot s.2 inf_le_left)⟩))
    intro a b hab
    dsimp only at hab
    rw [Prod.ext_iff] at hab
    obtain ⟨h1, h2⟩ := hab
    exact Subtype.ext (Prod.ext (congrArg Subtype.val h1) (congrArg Subtype.val h2))
  haveI : Fintype {p : ℂ × ℂ // W p ≠ ⊥} := @Fintype.ofFinite _ hfin
  have hdecomp' : DirectSum.IsInternal (fun (s : {p : ℂ × ℂ // W p ≠ ⊥}) => W s.1) := by
    apply (horth.comp Subtype.val_injective).isInternal_iff.mpr
    have hsup : (⨆ s : {p : ℂ × ℂ // W p ≠ ⊥}, W s.1) = ⨆ p, W p := iSup_ne_bot_subtype W
    rw [hsup]
    exact horth.isInternal_iff.mp hdecomp
  have horth' := horth.comp (Subtype.val_injective (α := ℂ × ℂ) (p := fun p => W p ≠ ⊥))
  set basis₀ := hdecomp'.subordinateOrthonormalBasis (finrank_euclideanSpace (ι := n)) horth'
  set basis := basis₀.reindex (Fintype.equivFin n).symm
  have hA_op : toEuclideanLin M = toEuclideanLin H + Complex.I • toEuclideanLin K := by
    rw [hA_eq]
    simp [map_add, map_smul]
  set ev : n → ℂ := fun j =>
    let j' := (Fintype.equivFin n) j
    let s := hdecomp'.subordinateOrthonormalBasisIndex (finrank_euclideanSpace (ι := n)) j'
      horth'
    s.1.2 + Complex.I * s.1.1
  set P := (EuclideanSpace.basisFun n ℂ).toBasis.toMatrix (basis.toBasis)
  have hP_mem : P ∈ unitaryGroup n ℂ :=
    (EuclideanSpace.basisFun n ℂ).toMatrix_orthonormalBasis_mem_unitary basis
  have hstarP_P : star P * P = 1 := mem_unitaryGroup_iff'.mp hP_mem
  refine ⟨P, hP_mem, ev, ?_⟩
  have hMbasis : ∀ j, toEuclideanLin M (basis j) = ev j • (basis j) := by
    intro j
    set j' := (Fintype.equivFin n) j
    set s := hdecomp'.subordinateOrthonormalBasisIndex (finrank_euclideanSpace (ι := n)) j'
      horth'
    have hsub := hdecomp'.subordinateOrthonormalBasis_subordinate
      (finrank_euclideanSpace (ι := n)) j' horth'
    have hbj : (basis j : EuclideanSpace ℂ n) = basis₀ j' := by
      simp only [basis, OrthonormalBasis.reindex_apply]
      congr 1
    have hmem : (basis₀ j' : EuclideanSpace ℂ n) ∈ W s.1 := hsub
    rw [Submodule.mem_inf] at hmem
    have hmH := Module.End.mem_eigenspace_iff.mp hmem.1
    have hmK := Module.End.mem_eigenspace_iff.mp hmem.2
    rw [hA_op, LinearMap.add_apply, LinearMap.smul_apply, hbj, hmH, hmK]
    simp only [ev, j', s, smul_smul, add_smul]
  have h1 : M * P = P * diagonal ev := by
    apply Matrix.ext
    intro i j
    have hkey := hMbasis j
    rw [toLpLin_apply] at hkey
    have hMb : (M *ᵥ (basis j : EuclideanSpace ℂ n).ofLp) i =
        ev j * (basis j : EuclideanSpace ℂ n).ofLp i := by
      have := congr_fun (congrArg (fun x : EuclideanSpace ℂ n => x.ofLp) hkey) i
      simpa [Pi.smul_apply, smul_eq_mul] using this
    change (M *ᵥ (basis j : EuclideanSpace ℂ n).ofLp) i =
      ∑ x, (basis x : EuclideanSpace ℂ n).ofLp i * (if x = j then ev x else 0)
    rw [hMb]
    simp [Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
  calc star P * M * P = star P * (M * P) := by rw [Matrix.mul_assoc]
    _ = star P * (P * diagonal ev) := by rw [h1]
    _ = (star P * P) * diagonal ev := by rw [← Matrix.mul_assoc]
    _ = 1 * diagonal ev := by rw [hstarP_P]
    _ = diagonal ev := Matrix.one_mul _

end Matrix
