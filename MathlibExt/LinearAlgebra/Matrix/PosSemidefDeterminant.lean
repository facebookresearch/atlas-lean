/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Determinant inequalities for positive semidefinite matrices

For a positive semidefinite matrix `A`, the determinant is controlled by
the diagonal and by the trace. The diagonal bound
`det A ≤ ∏ i, A i i` is Hadamard's inequality applied to the positive
square root `B = √A`, whose row norms squared are the diagonal entries of
`A = B * B`. The trace bound `(det A) ^ (1 / n) ≤ (tr A) / n` is the
arithmetic-geometric mean inequality applied to the (nonnegative)
eigenvalues of `A`, with equality exactly for scalar matrices.

This is a companion to the self-adjoint / positivity material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(self-adjoint operators, positivity iff the spectrum is nonnegative):
in finite dimension the spectrum is the list of eigenvalues, and the
two inequalities above are the determinant form of that spectral picture.
It is not one of the 72 v1 targets. The ingredients are in pinned Mathlib
(eigenvalues of Hermitian matrices, the continuous functional calculus
square root) and in base MathlibExt (Hadamard's determinant inequality
for general complex matrices), but the positive semidefinite determinant
bounds themselves are in neither.

## Main declarations

* `Matrix.PosSemidef.det_re_le_prod_diag_re` : `(A.det).re ≤ ∏ i, (A i i).re`.
* `Matrix.PosSemidef.geomMean_det_le_trace_div` :
  `(A.det).re ^ (n⁻¹ : ℝ) ≤ (A.trace).re / n`.
* `Matrix.PosSemidef.det_re_le_pow_trace_div` :
  `(A.det).re ≤ ((A.trace).re / n) ^ n`.
* `Matrix.PosSemidef.amgm_eq_iff` : equality in the AM–GM bound holds
  iff `A` is a nonnegative scalar matrix.
* `Matrix.PosSemidef.trace_mul_nonneg_re` : `0 ≤ ((A * B).trace).re`
  for `A` and `B` positive semidefinite.
-/

@[expose] public section

namespace Matrix

open Finset
open scoped ComplexOrder MatrixOrder
open MathlibExt.LinearAlgebra.Matrix.HadamardDeterminant

variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}

/-- The real part of the determinant of a positive semidefinite matrix is
the product of its eigenvalues. -/
private theorem PosSemidef.det_re_eq_prod_eigenvalues (hA : A.PosSemidef) :
    (A.det).re = ∏ i, hA.isHermitian.eigenvalues i := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  exact RCLike.ofReal_re (K := ℂ) _

/-- The real part of the trace of a positive semidefinite matrix is the
sum of its eigenvalues. -/
private theorem PosSemidef.trace_re_eq_sum_eigenvalues (hA : A.PosSemidef) :
    (A.trace).re = ∑ i, hA.isHermitian.eigenvalues i := by
  rw [hA.isHermitian.trace_eq_sum_eigenvalues, ← RCLike.ofReal_sum]
  exact RCLike.ofReal_re (K := ℂ) _

/-- The real part of the determinant of a positive semidefinite matrix is
nonnegative. -/
private theorem PosSemidef.det_re_nonneg (hA : A.PosSemidef) :
    0 ≤ (A.det).re :=
  (RCLike.nonneg_iff.mp hA.det_nonneg).1

/-- The positive square root of a matrix is Hermitian. -/
private theorem sqrt_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A := by
  rw [← Matrix.star_eq_conjTranspose]
  exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A))

/-- The positive square root of a positive semidefinite matrix squares
to the matrix. -/
private theorem PosSemidef.sqrt_mul_sqrt (hA : A.PosSemidef) :
    CFC.sqrt A * CFC.sqrt A = A :=
  CFC.sqrt_mul_sqrt_self A (ha := hA.nonneg)

/-- **Hadamard's inequality for positive semidefinite matrices**: the
determinant is at most the product of the diagonal entries. -/
theorem PosSemidef.det_re_le_prod_diag_re (hA : A.PosSemidef) :
    (A.det).re ≤ ∏ i, (A i i).re := by
  set S := CFC.sqrt A with hSdef
  have hS_herm : Sᴴ = S := sqrt_conjTranspose A
  have hSS : S * S = A := hA.sqrt_mul_sqrt
  have hdet : A.det = S.det ^ 2 := by
    rw [← hSS, Matrix.det_mul, pow_two]
  have hdet_im : (S.det).im = 0 := by
    have hstar : star (S.det) = S.det := by
      rw [← Matrix.det_conjTranspose, hS_herm]
    have hconj : (starRingEnd ℂ) (S.det) = S.det := by
      rw [← Complex.star_def]
      exact hstar
    exact Complex.conj_eq_iff_im.mp hconj
  have hA_re : (A.det).re = ‖S.det‖ ^ 2 := by
    rw [hdet, pow_two, Complex.mul_re, hdet_im, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_apply, hdet_im]
    ring
  have hrow : ∀ i, ∑ j, Complex.normSq (S i j) = (A i i).re := by
    intro i
    have hrow' : A i i = ∑ j, S i j * star (S i j) := by
      have h := congrFun (congrFun (show S * Sᴴ = A by rw [hS_herm]; exact hSS) i) i
      rw [Matrix.mul_apply] at h
      simp only [Matrix.conjTranspose_apply] at h
      exact h.symm
    have h2 := congrArg Complex.re hrow'
    rw [Complex.re_sum] at h2
    rw [h2]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  have hHad := hadamard_determinant_inequality S
  have hsq : ‖S.det‖ ^ 2 ≤ (∏ i, Real.sqrt (∑ j, Complex.normSq (S i j))) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hHad 2
  rw [← Finset.prod_pow] at hsq
  have hprod : (∏ i, (Real.sqrt (∑ j, Complex.normSq (S i j))) ^ 2) =
      ∏ i, (A i i).re := by
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _), hrow i]
  rw [← hA_re, hprod] at hsq
  exact hsq

/-- **AM–GM inequality for the determinant of a positive semidefinite
matrix**: the geometric mean of the eigenvalues is at most the
arithmetic mean, i.e. `(det A) ^ (1 / n) ≤ (tr A) / n`. -/
theorem PosSemidef.geomMean_det_le_trace_div (hA : A.PosSemidef) (hn : 0 < n) :
    (A.det).re ^ ((n : ℝ)⁻¹) ≤ (A.trace).re / (n : ℝ) := by
  have hsum_pos : (0 : ℝ) < ∑ _i : Fin n, (1 : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact_mod_cast hn
  have h := Real.geom_mean_le_arith_mean (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ)) (fun i => hA.isHermitian.eigenvalues i)
    (fun _ _ => zero_le_one) hsum_pos (fun i _ => hA.eigenvalues_nonneg i)
  simp only [Real.rpow_one, one_mul] at h
  rw [hA.det_re_eq_prod_eigenvalues, hA.trace_re_eq_sum_eigenvalues]
  have hsum : ∑ _i ∈ (Finset.univ : Finset (Fin n)), (1 : ℝ) = (n : ℝ) := by
    simp
  rw [hsum] at h
  exact h

/-- **AM–GM inequality for the determinant of a positive semidefinite
matrix, power form**: `det A ≤ ((tr A) / n) ^ n`. -/
theorem PosSemidef.det_re_le_pow_trace_div (hA : A.PosSemidef) (hn : 0 < n) :
    (A.det).re ≤ ((A.trace).re / (n : ℝ)) ^ n := by
  have h := hA.geomMean_det_le_trace_div hn
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hA.det_re_nonneg _)
    h n
  rwa [Real.rpow_inv_natCast_pow hA.det_re_nonneg
    (Nat.pos_iff_ne_zero.mp hn)] at hpow

/-- **Equality in the AM–GM bound for the determinant** holds iff `A`
is a nonnegative scalar matrix. -/
theorem PosSemidef.amgm_eq_iff (hA : A.PosSemidef) (hn : 0 < n) :
    (A.det).re ^ ((n : ℝ)⁻¹) = (A.trace).re / (n : ℝ) ↔
      ∃ c : ℝ, 0 ≤ c ∧ A = (c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  constructor
  · intro heq
    -- All eigenvalues are equal, by the equality condition for weighted AM–GM.
    have hall : ∀ i j : Fin n,
        hA.isHermitian.eigenvalues i = hA.isHermitian.eigenvalues j := by
      have hsum : ∑ _i ∈ (Finset.univ : Finset (Fin n)), ((n : ℝ)⁻¹) = 1 := by
        simp [hn']
      have hiff := (Real.geom_mean_eq_arith_mean_weighted_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin n))) (w := fun _ => ((n : ℝ)⁻¹))
        (z := fun i => hA.isHermitian.eigenvalues i)
        (fun _ _ => by positivity) hsum (fun i _ => hA.eigenvalues_nonneg i))
      have heq' : ∏ i ∈ (Finset.univ : Finset (Fin n)),
            (hA.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) =
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            ((n : ℝ)⁻¹) * hA.isHermitian.eigenvalues i := by
        rw [Real.finsetProd_rpow _ _ (fun i _ => hA.eigenvalues_nonneg i),
          ← hA.det_re_eq_prod_eigenvalues, heq, hA.trace_re_eq_sum_eigenvalues,
          div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      exact fun i j => hiff.mp heq' i (Finset.mem_univ i) (inv_ne_zero hn') j
        (Finset.mem_univ j) (inv_ne_zero hn')
    obtain ⟨i0⟩ : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    refine ⟨hA.isHermitian.eigenvalues i0, hA.eigenvalues_nonneg i0, ?_⟩
    -- The spectral theorem: `A` is unitarily conjugate to its diagonal
    -- of eigenvalues, and a constant diagonal is a scalar matrix.
    have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) =
        ((hA.isHermitian.eigenvalues i0 : ℝ) : ℂ) •
          (1 : Matrix (Fin n) (Fin n) ℂ) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.diagonal, hall i i0]
      · simp [Matrix.diagonal, hij, Matrix.one_apply_ne hij]
    calc A = Unitary.conjStarAlgAut ℂ _ hA.isHermitian.eigenvectorUnitary
            (Matrix.diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues)) :=
          hA.isHermitian.spectral_theorem
      _ = Unitary.conjStarAlgAut ℂ _ hA.isHermitian.eigenvectorUnitary
            (((hA.isHermitian.eigenvalues i0 : ℝ) : ℂ) •
              (1 : Matrix (Fin n) (Fin n) ℂ)) := by rw [hdiag]
      _ = ((hA.isHermitian.eigenvalues i0 : ℝ) : ℂ) •
            (1 : Matrix (Fin n) (Fin n) ℂ) := by
          rw [Unitary.conjStarAlgAut_apply, mul_smul_comm, smul_mul_assoc,
            mul_one, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  · rintro ⟨c, hc, rfl⟩
    have hdet : (((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det).re = c ^ n := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
        ← Complex.ofReal_pow, Complex.ofReal_re]
    have htr : (((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).trace).re = c * (n : ℝ) := by
      rw [Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul,
        ← Complex.ofReal_natCast (n := n), ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hdet, htr, Real.pow_rpow_inv_natCast hc hn0]
    exact (mul_div_cancel_right₀ c hn').symm

/-- The trace of a product of positive semidefinite matrices is
nonnegative. -/
theorem PosSemidef.trace_mul_nonneg_re (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ ((A * B).trace).re := by
  set C := CFC.sqrt A with hCdef
  have hC_herm : Cᴴ = C := sqrt_conjTranspose A
  have hCC : C * C = A := hA.sqrt_mul_sqrt
  have htr : (A * B).trace = (C * B * C).trace := by
    rw [← hCC, Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [htr]
  have hpsd : (C * B * C).PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same C
    rwa [hC_herm] at h
  exact (RCLike.nonneg_iff.mp hpsd.trace_nonneg).1

end Matrix


namespace Matrix

open scoped ComplexOrder in
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
