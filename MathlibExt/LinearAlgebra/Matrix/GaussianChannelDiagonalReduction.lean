/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.PosSemidefDeterminant
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Gaussian channel diagonal reduction

A real Gaussian channel with positive semidefinite Gram
matrix reduces, by orthogonal diagonalization, to parallel
scalar channels: the determinant ratio against the diagonalized
covariance is the product of the scalar ratios, hence at most
what the diagonal entries give. Hadamard's inequality (the
canonical `Matrix.PosSemidef.det_re_le_prod_diag_re`, imported)
is the key input, with a real arbitrary-finite-index adapter.
-/

@[expose] public section

open Matrix
open scoped ComplexOrder

namespace Matrix

/-- Hadamard's inequality for real positive semidefinite matrices over an arbitrary finite
index type: `det A ≤ ∏ i, A i i`. To be derived from the complex `Fin n` Atlas theorem by
complexification and reindexing, not re-proved. -/
theorem PosSemidef.det_le_prod_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set B : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    A.submatrix e.symm e.symm with hB
  set C : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ :=
    B.map Complex.ofReal with hC
  have hBpsd : B.PosSemidef := hA.submatrix e.symm
  have hBdet : B.det = A.det := Matrix.det_submatrix_equiv_self e.symm A
  have hBdiag : ∏ i, B i i = ∏ i, A i i := Equiv.prod_comp e.symm (fun j => A j j)
  have hsym : ∀ i j, B i j = B j i := by
    intro i j
    have h2 : Bᴴ = B := hBpsd.isHermitian
    have h := congrFun (congrFun h2 j) i
    rwa [Matrix.conjTranspose_apply, star_trivial] at h
  have hCherm : C.IsHermitian := by
    show Cᴴ = C
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.conjTranspose_apply, hC, Matrix.map_apply, Complex.star_def,
      Complex.conj_ofReal, hsym i j]
  have hz : ∀ x : Fin (Fintype.card ι) → ℂ, star x ⬝ᵥ (C *ᵥ x)
      = ∑ i, ∑ j, (starRingEnd ℂ) (x i) * (Complex.ofReal (B i j) * x j) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, hC, Matrix.map_apply, Pi.star_apply,
      Complex.star_def, Finset.mul_sum]
  have hterm_re : ∀ (a b : ℂ) (c : ℝ),
      ((starRingEnd ℂ) a * (Complex.ofReal c * b)).re
        = c * (a.re * b.re) + c * (a.im * b.im) := by
    intro a b c
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hterm_im : ∀ (a b : ℂ) (c : ℝ),
      ((starRingEnd ℂ) a * (Complex.ofReal c * b)).im
        = c * (a.re * b.im - a.im * b.re) := by
    intro a b c
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hquad : ∀ u : Fin (Fintype.card ι) → ℝ, star u ⬝ᵥ (B *ᵥ u)
      = ∑ i, ∑ j, B i j * (u i * u j) := by
    intro u
    simp only [dotProduct, Matrix.mulVec, star_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have hCpsd : C.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hCherm fun x => ?_
    have hz' := hz x
    apply RCLike.nonneg_iff.mpr
    constructor
    · show 0 ≤ Complex.re (star x ⬝ᵥ (C *ᵥ x))
      rw [hz']
      simp only [Complex.re_sum, hterm_re, Finset.sum_add_distrib]
      have eU : (∑ i, ∑ j, B i j * ((x i).re * (x j).re))
          = star (fun i => (x i).re) ⬝ᵥ (B *ᵥ fun i => (x i).re) := (hquad _).symm
      have eV : (∑ i, ∑ j, B i j * ((x i).im * (x j).im))
          = star (fun i => (x i).im) ⬝ᵥ (B *ᵥ fun i => (x i).im) := (hquad _).symm
      rw [eU, eV]
      exact add_nonneg (hBpsd.dotProduct_mulVec_nonneg _)
        (hBpsd.dotProduct_mulVec_nonneg _)
    · show Complex.im (star x ⬝ᵥ (C *ᵥ x)) = 0
      rw [hz']
      simp only [Complex.im_sum, hterm_im]
      have hSS : (∑ i, ∑ j, B i j * ((x i).re * (x j).im - (x i).im * (x j).re))
          = -(∑ i, ∑ j, B i j * ((x i).re * (x j).im - (x i).im * (x j).re)) :=
        Finset.sum_comm.trans (by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro a _
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl; intro b _
          rw [hsym b a]
          ring)
      linarith [hSS]
  have hCdet : (C.det).re = B.det := by
    have h := Complex.ofRealHom.map_det B
    have hCeq : C = Complex.ofRealHom.mapMatrix B := by
      refine Matrix.ext fun i j => ?_
      rfl
    have hcoe : ⇑Complex.ofRealHom B.det = Complex.ofReal B.det := rfl
    rw [hCeq, ← h, hcoe, Complex.ofReal_re]
  have hCdiag : ∀ i, (C i i).re = B i i := by
    intro i
    simp only [hC, Matrix.map_apply, Complex.ofReal_re]
  have hmirror := Matrix.PosSemidef.det_re_le_prod_diag_re hCpsd
  rw [hCdet] at hmirror
  simp only [hCdiag] at hmirror
  rw [hBdet, hBdiag] at hmirror
  exact hmirror

end Matrix

namespace MathlibExt.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction

/-- Whitened channel Gram matrix `Hᵀ R⁻¹ H`. -/
noncomputable def channelGram {m n : Type*} [Fintype m] [DecidableEq m]
    (H : Matrix m n ℝ) (R : Matrix m m ℝ) : Matrix n n ℝ :=
  Hᵀ * R⁻¹ * H

/-- For positive definite noise covariance `R`, `Hᵀ R⁻¹ H` is positive semidefinite. -/
theorem channelGram_posSemidef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef) :
    (channelGram H R).PosSemidef := by
  have hRinv : R⁻¹.PosSemidef := hR.posSemidef.inv
  have h := hRinv.conjTranspose_mul_mul_same H
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

/-- Channel eigenvalues `λ_i` of `Hᵀ R⁻¹ H`, from Mathlib's spectral theorem. -/
noncomputable def channelEigenvalues {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef) : n → ℝ :=
  (channelGram_posSemidef H hR).isHermitian.eigenvalues

/-- Orthogonal input basis `V`: Mathlib's eigenvector unitary of `Hᵀ R⁻¹ H`, as a real
matrix (columns are orthonormal eigenvectors). -/
noncomputable def inputBasis {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef) : Matrix n n ℝ :=
  ((channelGram_posSemidef H hR).isHermitian.eigenvectorUnitary : Matrix n n ℝ)

/-- Rotated input covariance `Vᵀ K V`. -/
noncomputable def rotatedCovariance {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    (K : Matrix n n ℝ) : Matrix n n ℝ :=
  (inputBasis H hR)ᵀ * K * inputBasis H hR

/-- Power allocation `p_i`: the diagonal of the rotated covariance. -/
noncomputable def powerAllocation {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    (K : Matrix n n ℝ) : n → ℝ :=
  fun i => rotatedCovariance H hR K i i

/-- Input covariance after replacing the rotated covariance by its diagonal,
`V diag(p) Vᵀ`. -/
noncomputable def diagonalizedCovariance {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    (K : Matrix n n ℝ) : Matrix n n ℝ :=
  inputBasis H hR * diagonal (powerAllocation H hR K) * (inputBasis H hR)ᵀ

/-- Determinant ratio `det (R + H K Hᵀ) / det R`. -/
noncomputable def detRatio {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (H : Matrix m n ℝ) (R : Matrix m m ℝ) (K : Matrix n n ℝ) : ℝ :=
  (R + H * K * Hᵀ).det / R.det

private theorem detRatio_eq_one_add_gram {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    (K : Matrix n n ℝ) :
    detRatio H R K = (1 + channelGram H R * K).det := by
  have hRne : R.det ≠ 0 := hR.det_pos.ne'
  have hRunit : IsUnit R.det := isUnit_iff_ne_zero.mpr hRne
  have hmdl := Matrix.det_add_mul (H * K) Hᵀ hRunit
  have eGK : Hᵀ * R⁻¹ * (H * K) = channelGram H R * K := by
    unfold channelGram
    simp only [Matrix.mul_assoc]
  unfold detRatio
  rw [hmdl, eGK, mul_div_cancel_left₀ _ hRne]

private theorem detRatio_le_prod_aux {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) (V : Matrix n n ℝ) (lam : n → ℝ)
    (hV : Vᵀ * V = 1) (hG : channelGram H R = V * diagonal lam * Vᵀ) :
    detRatio H R K ≤ ∏ i, (1 + lam i * (Vᵀ * K * V) i i) := by
  have hlam : ∀ i, 0 ≤ lam i := by
    have h1 : (Vᴴ * channelGram H R * V).PosSemidef :=
      (channelGram_posSemidef H hR).conjTranspose_mul_mul_same V
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
    have hVV : Vᵀ * channelGram H R * V
        = (Vᵀ * V) * diagonal lam * (Vᵀ * V) := by
      rw [hG]
      simp only [mul_assoc]
    rw [hVV, hV, one_mul, mul_one] at h1
    exact Matrix.posSemidef_diagonal_iff.mp h1
  have hKtild_psd : (Vᵀ * K * V).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hK.conjTranspose_mul_mul_same V
  have hSS : diagonal (fun i => Real.sqrt (lam i))
      * diagonal (fun i => Real.sqrt (lam i)) = diagonal lam := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hlam i)
  have hSKS : (diagonal (fun i => Real.sqrt (lam i)) * (Vᵀ * K * V)
      * diagonal (fun i => Real.sqrt (lam i))).PosSemidef := by
    have h := hKtild_psd.conjTranspose_mul_mul_same
      (diagonal (fun i => Real.sqrt (lam i)))
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.diagonal_transpose] at h
  have hdet1 : detRatio H R K = (1 + (Vᵀ * K * V) * diagonal lam).det := by
    have hratio := detRatio_eq_one_add_gram H hR K
    rw [hratio, hG]
    have e1 : (V * diagonal lam * Vᵀ) * K = (V * diagonal lam) * (Vᵀ * K) := by
      simp only [mul_assoc]
    have eWA := Matrix.det_one_add_mul_comm (V * diagonal lam) (Vᵀ * K)
    rw [e1, eWA]
    have e2 : (Vᵀ * K) * (V * diagonal lam) = (Vᵀ * K * V) * diagonal lam := by
      simp only [mul_assoc]
    rw [e2]
  have hdet2 : (1 + (Vᵀ * K * V) * diagonal lam).det
      = (1 + diagonal (fun i => Real.sqrt (lam i)) * (Vᵀ * K * V)
        * diagonal (fun i => Real.sqrt (lam i))).det := by
    have e3 : (Vᵀ * K * V) * diagonal lam
        = ((Vᵀ * K * V) * diagonal (fun i => Real.sqrt (lam i)))
          * diagonal (fun i => Real.sqrt (lam i)) := by
      rw [← hSS]
      simp only [mul_assoc]
    rw [e3]
    have eWA := Matrix.det_one_add_mul_comm
      ((Vᵀ * K * V) * diagonal (fun i => Real.sqrt (lam i)))
      (diagonal (fun i => Real.sqrt (lam i)))
    rw [eWA]
    congr 1
    simp only [mul_assoc]
  have hdiag : ∀ i, (1 + diagonal (fun i => Real.sqrt (lam i)) * (Vᵀ * K * V)
      * diagonal (fun i => Real.sqrt (lam i))) i i
      = 1 + lam i * (Vᵀ * K * V) i i := by
    intro i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    have hsq : Real.sqrt (lam i) * (Vᵀ * K * V) i i * Real.sqrt (lam i)
        = lam i * (Vᵀ * K * V) i i := by
      have hss : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i :=
        Real.mul_self_sqrt (hlam i)
      calc Real.sqrt (lam i) * (Vᵀ * K * V) i i * Real.sqrt (lam i)
          = (Real.sqrt (lam i) * Real.sqrt (lam i)) * (Vᵀ * K * V) i i := by ring
        _ = lam i * (Vᵀ * K * V) i i := by rw [hss]
    rw [hsq]
  have hSKSpd : (1 + diagonal (fun i => Real.sqrt (lam i)) * (Vᵀ * K * V)
      * diagonal (fun i => Real.sqrt (lam i))).PosSemidef :=
    Matrix.PosSemidef.one.add hSKS
  have hHad := Matrix.PosSemidef.det_le_prod_diag hSKSpd
  rw [hdet1, hdet2]
  refine hHad.trans (le_of_eq ?_)
  apply Finset.prod_congr rfl
  intro i _
  exact hdiag i

private theorem detRatio_eq_prod_aux {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    (V : Matrix n n ℝ) (lam p : n → ℝ) (hV : Vᵀ * V = 1)
    (hG : channelGram H R = V * diagonal lam * Vᵀ) :
    detRatio H R (V * diagonal p * Vᵀ) = ∏ i, (1 + lam i * p i) := by
  have hratio := detRatio_eq_one_add_gram H hR (V * diagonal p * Vᵀ)
  rw [hratio, hG]
  have h1 : V * diagonal lam * Vᵀ * V = V * diagonal lam := by
    rw [mul_assoc _ _ V, hV, mul_one]
  have e : (V * diagonal lam * Vᵀ) * (V * diagonal p * Vᵀ)
      = (V * (diagonal lam * diagonal p)) * Vᵀ := by
    calc (V * diagonal lam * Vᵀ) * (V * diagonal p * Vᵀ)
        = ((V * diagonal lam * Vᵀ * V) * diagonal p) * Vᵀ := by
          simp only [mul_assoc]
      _ = (V * (diagonal lam * diagonal p)) * Vᵀ := by
          rw [h1]; simp only [mul_assoc]
  rw [e]
  have eWA := Matrix.det_one_add_mul_comm (V * (diagonal lam * diagonal p)) Vᵀ
  rw [eWA]
  have e2 : Vᵀ * (V * (diagonal lam * diagonal p)) = diagonal lam * diagonal p := by
    rw [← mul_assoc, hV, one_mul]
  rw [e2]
  have e3 : (1 : Matrix n n ℝ) + diagonal lam * diagonal p
      = diagonal (fun i => 1 + lam i * p i) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, Matrix.diagonal_add]
  rw [e3, Matrix.det_diagonal]

/-! ### Spectral data -/

/-- The input basis is orthogonal: `Vᵀ V = 1` and `V Vᵀ = 1`. -/
theorem inputBasis_orthogonal {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef) :
    (inputBasis H hR)ᵀ * inputBasis H hR = 1 ∧ inputBasis H hR * (inputBasis H hR)ᵀ = 1 := by
  have hm1 := Matrix.mem_unitaryGroup_iff'.mp
    ((channelGram_posSemidef H hR).isHermitian.eigenvectorUnitary).2
  have hm2 := Matrix.mem_unitaryGroup_iff.mp
    ((channelGram_posSemidef H hR).isHermitian.eigenvectorUnitary).2
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hm1 hm2
  unfold inputBasis
  exact ⟨hm1, hm2⟩

/-- Orthogonal diagonalization `Hᵀ R⁻¹ H = V diag(λ) Vᵀ`. -/
theorem channelGram_eq_spectral {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef) :
    channelGram H R =
      inputBasis H hR * diagonal (channelEigenvalues H hR) * (inputBasis H hR)ᵀ := by
  have hspec := (channelGram_posSemidef H hR).isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hspec
  have hcomp : RCLike.ofReal ∘ (channelGram_posSemidef H hR).isHermitian.eigenvalues
      = (channelGram_posSemidef H hR).isHermitian.eigenvalues := by
    rw [RCLike.ofReal_real_eq_id]; rfl
  rw [hcomp] at hspec
  unfold inputBasis channelEigenvalues
  exact hspec

/-- The channel eigenvalues are nonnegative. -/
theorem channelEigenvalues_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef) (i : n) :
    0 ≤ channelEigenvalues H hR i := by
  exact (channelGram_posSemidef H hR).eigenvalues_nonneg i

/-! ### Diagonal reduction -/

/-- The allocated powers of a PSD covariance are nonnegative. -/
theorem powerAllocation_nonneg {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) (i : n) :
    0 ≤ powerAllocation H hR K i := by
  have h : ((inputBasis H hR)ᵀ * K * inputBasis H hR).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hK.conjTranspose_mul_mul_same (inputBasis H hR)
  exact h.diag_nonneg

/-- The diagonalized covariance of a PSD covariance is PSD. -/
theorem diagonalizedCovariance_posSemidef {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) :
    (diagonalizedCovariance H hR K).PosSemidef := by
  have hp : ∀ i, 0 ≤ powerAllocation H hR K i :=
    fun i => powerAllocation_nonneg H hR hK i
  have hD : (diagonal (powerAllocation H hR K)).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr hp
  have h := hD.mul_mul_conjTranspose_same (inputBasis H hR)
  simpa only [diagonalizedCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- Replacing the rotated covariance by its diagonal preserves the trace (total power). -/
theorem trace_diagonalizedCovariance {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    (K : Matrix n n ℝ) :
    (diagonalizedCovariance H hR K).trace = K.trace := by
  have hV1 := (inputBasis_orthogonal H hR).1
  have hV2 := (inputBasis_orthogonal H hR).2
  have hsum : (diagonalizedCovariance H hR K).trace
      = ∑ i, powerAllocation H hR K i := by
    unfold diagonalizedCovariance
    rw [Matrix.trace_mul_comm, ← mul_assoc, hV1, one_mul, Matrix.trace_diagonal]
  have hVK : ((inputBasis H hR)ᵀ * K * inputBasis H hR).trace = K.trace := by
    rw [Matrix.trace_mul_comm, ← mul_assoc, hV2, one_mul]
  have hsum2 : ∑ i, powerAllocation H hR K i
      = ((inputBasis H hR)ᵀ * K * inputBasis H hR).trace := by
    simp only [powerAllocation, rotatedCovariance, Matrix.trace, Matrix.diag]
  exact hsum.trans (hsum2.trans hVK)

/-- Replacing the rotated covariance by its diagonal cannot reduce `det (R + H K Hᵀ) / det R`. -/
theorem detRatio_le_detRatio_diagonalizedCovariance {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) :
    detRatio H R K ≤ detRatio H R (diagonalizedCovariance H hR K) := by
  have hle := detRatio_le_prod_aux H hR hK (inputBasis H hR) (channelEigenvalues H hR)
    (inputBasis_orthogonal H hR).1 (channelGram_eq_spectral H hR)
  have heq := detRatio_eq_prod_aux H hR (inputBasis H hR) (channelEigenvalues H hR)
    (powerAllocation H hR K) (inputBasis_orthogonal H hR).1 (channelGram_eq_spectral H hR)
  have heq2 : detRatio H R (diagonalizedCovariance H hR K)
      = ∏ i, (1 + channelEigenvalues H hR i * powerAllocation H hR K i) := heq
  rw [heq2]
  exact hle

/-- For the diagonalized covariance the ratio is `∏ i, (1 + λ_i p_i)`. -/
theorem detRatio_diagonalizedCovariance_eq_prod {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) :
    detRatio H R (diagonalizedCovariance H hR K) =
      ∏ i, (1 + channelEigenvalues H hR i * powerAllocation H hR K i) := by
  exact detRatio_eq_prod_aux H hR (inputBasis H hR) (channelEigenvalues H hR)
    (powerAllocation H hR K) (inputBasis_orthogonal H hR).1 (channelGram_eq_spectral H hR)

/-- **Diagonal reduction of the Gaussian channel determinant.** For SPD `R` and PSD `K`, in the
orthogonal eigenbasis `V` of `Hᵀ R⁻¹ H` (eigenvalues `λ_i ≥ 0`), replacing `Vᵀ K V` by its
diagonal `p` preserves the trace, cannot reduce `det (R + H K Hᵀ) / det R`, and gives
`∏ i, (1 + λ_i p_i)`. -/
theorem gaussianChannel_diagonalReduction {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) :
    (∀ i, 0 ≤ channelEigenvalues H hR i) ∧
      (diagonalizedCovariance H hR K).trace = K.trace ∧
      detRatio H R K ≤ detRatio H R (diagonalizedCovariance H hR K) ∧
      detRatio H R (diagonalizedCovariance H hR K) =
        ∏ i, (1 + channelEigenvalues H hR i * powerAllocation H hR K i) := by
  exact ⟨fun i => channelEigenvalues_nonneg H hR i,
    trace_diagonalizedCovariance H hR K,
    detRatio_le_detRatio_diagonalizedCovariance H hR hK,
    detRatio_diagonalizedCovariance_eq_prod H hR hK⟩

/-! ### Basis-generic form -/

/-- For any orthogonal `V` and real `λ` with `Hᵀ R⁻¹ H = V diag(λ) Vᵀ` and PSD `K`,
`det (R + H K Hᵀ) / det R ≤ ∏ i, (1 + λ_i (Vᵀ K V)_{ii})`. -/
theorem detRatio_le_prod_of_orthogonal_diagonalization {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) (V : Matrix n n ℝ) (lam : n → ℝ)
    (hV : Vᵀ * V = 1) (hG : channelGram H R = V * diagonal lam * Vᵀ) :
    detRatio H R K ≤ ∏ i, (1 + lam i * (Vᵀ * K * V) i i) := by
  exact detRatio_le_prod_aux H hR hK V lam hV hG

/-- For any orthogonal `V` and real `λ` with `Hᵀ R⁻¹ H = V diag(λ) Vᵀ` and any `p`,
`det (R + H (V diag(p) Vᵀ) Hᵀ) / det R = ∏ i, (1 + λ_i p_i)`. -/
theorem detRatio_eq_prod_of_orthogonal_diagonalization {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    (V : Matrix n n ℝ) (lam p : n → ℝ) (hV : Vᵀ * V = 1)
    (hG : channelGram H R = V * diagonal lam * Vᵀ) :
    detRatio H R (V * diagonal p * Vᵀ) = ∏ i, (1 + lam i * p i) := by
  exact detRatio_eq_prod_aux H hR V lam p hV hG

/-! ### Validation cases -/

/-- All channel eigenvalues zero give determinant ratio one, for every PSD input covariance. -/
theorem detRatio_eq_one_of_channelEigenvalues_eq_zero {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (H : Matrix m n ℝ) {R : Matrix m m ℝ} (hR : R.PosDef)
    {K : Matrix n n ℝ} (hK : K.PosSemidef) (h0 : ∀ i, channelEigenvalues H hR i = 0) :
    detRatio H R K = 1 := by
  have h00 : (channelGram_posSemidef H hR).isHermitian.eigenvalues = 0 := funext h0
  have hG0 : channelGram H R = 0 :=
    (channelGram_posSemidef H hR).isHermitian.eigenvalues_eq_zero_iff.mp h00
  have hratio := detRatio_eq_one_add_gram H hR K
  rw [hratio, hG0, zero_mul, add_zero, Matrix.det_one]

end MathlibExt.LinearAlgebra.Matrix.GaussianChannelDiagonalReduction
