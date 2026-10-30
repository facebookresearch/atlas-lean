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
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Minkowski's determinant inequality for positive semidefinite matrices

For positive semidefinite matrices `A` and `B` of size `n`,
`det (A + B) ^ (1 / n) ≥ det A ^ (1 / n) + det B ^ (1 / n)`.
In particular the determinant is monotone on the positive semidefinite cone.

This is a companion to the self-adjoint / positivity material of
`v1/Atlas/IntroductionToFunctionalAnalysis/code/SpectralTheory.lean`
(self-adjoint operators, positivity iff the spectrum is nonnegative):
in finite dimension the spectrum is the list of eigenvalues, and this
inequality is the determinant form of concavity of `det ^ (1 / n)` on
the positive semidefinite cone. It is not one of the 72 v1 targets, and
it is distinct from the Hadamard / AM–GM determinant bounds for
positive semidefinite matrices in base MathlibExt
(`MathlibExt/LinearAlgebra/Matrix/PosSemidefDeterminant.lean`).

The proof is the classical one: the key step is the eigenvalue
inequality `∏ (1 + λᵢ) ^ (1 / n) ≥ 1 + (∏ λᵢ) ^ (1 / n)` for
`λᵢ ≥ 0`, proved by weighted AM–GM applied to
`λᵢ / (1 + λᵢ)` and `1 / (1 + λᵢ)`; the invertible case follows by
conjugating with the positive square root of `A`, and the general case
by approximating `A` with the positive definite matrices `A + ε • 1`
and letting `ε → 0⁺`.

## Main declarations

* `Matrix.PosSemidef.minkowski_det` : Minkowski's determinant inequality.
* `Matrix.PosSemidef.det_le_det_add` : monotonicity of the determinant
  on the positive semidefinite cone.
-/

@[expose] public section

namespace Matrix

open Finset
open scoped ComplexOrder MatrixOrder Topology

variable {n : ℕ} {A B C : Matrix (Fin n) (Fin n) ℂ}

/-- The real part of the determinant of a positive semidefinite matrix is
the product of its eigenvalues. -/
private theorem det_re_eq_prod_eigenvalues (hA : A.PosSemidef) :
    (A.det).re = ∏ i, hA.isHermitian.eigenvalues i := by
  rw [hA.isHermitian.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  exact RCLike.ofReal_re (K := ℂ) _

/-- The real part of the determinant of a positive semidefinite matrix is
nonnegative. -/
private theorem det_re_nonneg (hA : A.PosSemidef) : 0 ≤ (A.det).re := by
  rw [det_re_eq_prod_eigenvalues hA]
  exact Finset.prod_nonneg fun i _ => hA.eigenvalues_nonneg i

/-- The determinant of `1 + C` for `C` positive semidefinite, as a
real number coerced to `ℂ`. -/
private theorem det_one_add_eq_ofReal_prod (hC : C.PosSemidef) :
    (1 + C).det =
      ((∏ i, (1 + hC.isHermitian.eigenvalues i) : ℝ) : ℂ) := by
  have hspec := hC.isHermitian.spectral_theorem
  set U := hC.isHermitian.eigenvectorUnitary with hU
  set e := hC.isHermitian.eigenvalues with he
  have hdiag : (1 : Matrix (Fin n) (Fin n) ℂ) +
      Matrix.diagonal (RCLike.ofReal ∘ e) =
      Matrix.diagonal (fun i => 1 + (((e i : ℝ)) : ℂ)) := by
    rw [← Matrix.diagonal_one, Matrix.diagonal_add]
    rfl
  have h1C : (1 : Matrix (Fin n) (Fin n) ℂ) + C =
      Unitary.conjStarAlgAut ℂ _ U
        (Matrix.diagonal (fun i => 1 + (((e i : ℝ)) : ℂ))) := by
    calc (1 : Matrix (Fin n) (Fin n) ℂ) + C
        = 1 + Unitary.conjStarAlgAut ℂ _ U
            (Matrix.diagonal (RCLike.ofReal ∘ e)) := by rw [hspec]
      _ = Unitary.conjStarAlgAut ℂ _ U
            (1 + Matrix.diagonal (RCLike.ofReal ∘ e)) := by
          rw [map_add, map_one]
      _ = Unitary.conjStarAlgAut ℂ _ U
            (Matrix.diagonal (fun i => 1 + (((e i : ℝ)) : ℂ))) := by
          rw [hdiag]
  rw [h1C, Unitary.conjStarAlgAut_apply, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal]
  have hdetU : (U : Matrix (Fin n) (Fin n) ℂ).det *
      (star (U : Matrix (Fin n) (Fin n) ℂ)).det = 1 := by
    rw [← Matrix.det_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self,
      Matrix.det_one]
  have hprod : ((U : Matrix (Fin n) (Fin n) ℂ).det *
      (∏ i, (1 + (((e i : ℝ)) : ℂ)))) *
      (star (U : Matrix (Fin n) (Fin n) ℂ)).det =
        ∏ i, (1 + (((e i : ℝ)) : ℂ)) := by
    rw [show ((U : Matrix (Fin n) (Fin n) ℂ).det *
        (∏ i, (1 + (((e i : ℝ)) : ℂ)))) *
        (star (U : Matrix (Fin n) (Fin n) ℂ)).det =
        (∏ i, (1 + (((e i : ℝ)) : ℂ))) *
        ((U : Matrix (Fin n) (Fin n) ℂ).det *
        (star (U : Matrix (Fin n) (Fin n) ℂ)).det) by ring,
      hdetU, mul_one]
  rw [hprod]
  calc ∏ i, (1 + (((e i : ℝ)) : ℂ))
      = ∏ i, (((1 + e i : ℝ)) : ℂ) := by
        apply Finset.prod_congr rfl
        intro i _
        push_cast
        ring
    _ = (((∏ i, (1 + e i) : ℝ)) : ℂ) := (Complex.ofReal_prod _ _).symm

/-- The determinant of `1 + C`, real-part form. -/
private theorem det_one_add_re_eq_prod (hC : C.PosSemidef) :
    ((1 + C).det).re = ∏ i, (1 + hC.isHermitian.eigenvalues i) := by
  rw [det_one_add_eq_ofReal_prod hC, Complex.ofReal_re]

/-- Key eigenvalue estimate: for nonnegative `wᵢ`,
`(∏ (1 + wᵢ)) ^ (1 / n) ≥ 1 + (∏ wᵢ) ^ (1 / n)`. -/
private theorem one_add_prod_rpow_ge {w : Fin n → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hn : 0 < n) :
    1 + (∏ i, w i) ^ ((n : ℝ)⁻¹) ≤ (∏ i, (1 + w i)) ^ ((n : ℝ)⁻¹) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hP : (0 : ℝ) < ∏ i, (1 + w i) :=
    Finset.prod_pos fun i _ => by linarith [hw i]
  have hwsum : ∑ _i : Fin n, ((n : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_inv_cancel₀ hn']
  have hterm : ∀ i, w i / (1 + w i) + (1 + w i)⁻¹ = 1 := by
    intro i
    have h1 : (0 : ℝ) < 1 + w i := by linarith [hw i]
    field_simp
    ring
  have hAMa := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin n))
    (fun _ => ((n : ℝ)⁻¹)) (fun i => w i / (1 + w i))
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n)) hwsum
    (fun i _ => div_nonneg (hw i) (by linarith [hw i]))
  have hAMb := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin n))
    (fun _ => ((n : ℝ)⁻¹)) (fun i => (1 + w i)⁻¹)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n)) hwsum
    (fun i _ => inv_nonneg.mpr (by linarith [hw i]))
  rw [Real.finsetProd_rpow _ _ (fun i _ => div_nonneg (hw i) (by linarith [hw i]))]
    at hAMa
  rw [Real.finsetProd_rpow _ _ (fun i _ => inv_nonneg.mpr (by linarith [hw i]))]
    at hAMb
  have hsum : (∑ i, ((n : ℝ)⁻¹) * (w i / (1 + w i))) +
      (∑ i, ((n : ℝ)⁻¹) * (1 + w i)⁻¹) = 1 := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add, ← Finset.sum_add_distrib]
    have hsum' : ∑ i : Fin n, (w i / (1 + w i) + (1 + w i)⁻¹) = (n : ℝ) := by
      simp only [hterm]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [hsum', inv_mul_cancel₀ hn']
  have hsum1 : (∏ i, w i / (1 + w i)) ^ ((n : ℝ)⁻¹) +
      (∏ i, (1 + w i)⁻¹) ^ ((n : ℝ)⁻¹) ≤ 1 := by
    have h := add_le_add hAMa hAMb
    rwa [hsum] at h
  rw [Finset.prod_div_distrib, Finset.prod_inv_distrib] at hsum1
  have hmul1 : ((∏ i, w i) / ∏ i, (1 + w i)) ^ ((n : ℝ)⁻¹) *
      (∏ i, (1 + w i)) ^ ((n : ℝ)⁻¹) = (∏ i, w i) ^ ((n : ℝ)⁻¹) := by
    rw [← Real.mul_rpow
      (div_nonneg (Finset.prod_nonneg fun i _ => hw i) hP.le) hP.le,
      div_mul_cancel₀ _ (ne_of_gt hP)]
  have hmul2 : ((∏ i, (1 + w i))⁻¹) ^ ((n : ℝ)⁻¹) *
      (∏ i, (1 + w i)) ^ ((n : ℝ)⁻¹) = 1 := by
    rw [← Real.mul_rpow (inv_nonneg.mpr hP.le) hP.le, inv_mul_cancel₀ (ne_of_gt hP),
      Real.one_rpow]
  have hle := mul_le_mul_of_nonneg_right hsum1
    (Real.rpow_nonneg hP.le ((n : ℝ)⁻¹))
  rw [add_mul, hmul1, hmul2, one_mul] at hle
  linarith [hle]

/-- The eigenvalue estimate applied to a positive semidefinite matrix. -/
private theorem one_add_det_re_rpow_ge (hC : C.PosSemidef) (hn : 0 < n) :
    1 + (C.det).re ^ ((n : ℝ)⁻¹) ≤ ((1 + C).det).re ^ ((n : ℝ)⁻¹) := by
  rw [det_one_add_re_eq_prod hC, det_re_eq_prod_eigenvalues hC]
  exact one_add_prod_rpow_ge (fun i => hC.eigenvalues_nonneg i) hn

/-- **Minkowski's determinant inequality, positive definite case**:
conjugate by the positive square root of `A`. -/
private theorem PosDef.minkowski_det_aux (hA : A.PosDef) (hB : B.PosSemidef)
    (hn : 0 < n) :
    (A.det).re ^ ((n : ℝ)⁻¹) + (B.det).re ^ ((n : ℝ)⁻¹) ≤
      ((A + B).det).re ^ ((n : ℝ)⁻¹) := by
  set S := CFC.sqrt A with hSdef
  have hS_herm : Sᴴ = S := by
    rw [← Matrix.star_eq_conjTranspose]
    exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A (ha := hA.posSemidef.nonneg)
  have hS_psd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
  have hS_det : S.det =
      ((∏ i, hS_psd.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    rw [hS_psd.isHermitian.det_eq_prod_eigenvalues]
    exact (Complex.ofReal_prod _ _).symm
  have hdS_nonneg : 0 ≤ ∏ i, hS_psd.isHermitian.eigenvalues i :=
    Finset.prod_nonneg fun i _ => hS_psd.eigenvalues_nonneg i
  have hSdet_unit : IsUnit S.det := by
    have hAunit : IsUnit A.det := (isUnit_iff_isUnit_det A).mp hA.isUnit
    rw [← hSS, Matrix.det_mul] at hAunit
    exact isUnit_of_mul_isUnit_left hAunit
  have hSinv : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hSdet_unit
  have hSinv' : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet_unit
  have hSinv_herm : (S⁻¹)ᴴ = S⁻¹ := hS_psd.isHermitian.inv
  set Ct := S⁻¹ * B * S⁻¹ with hCt
  have hCt_psd : Ct.PosSemidef := by
    have h := hB.mul_mul_conjTranspose_same S⁻¹
    rwa [hSinv_herm] at h
  have hSCS : S * Ct * S = B := by
    rw [hCt]
    have hassoc : S * (S⁻¹ * B * S⁻¹) * S = (S * S⁻¹) * B * (S⁻¹ * S) := by
      noncomm_ring
    rw [hassoc, hSinv, hSinv', one_mul, mul_one]
  have hAB : A + B = S * (1 + Ct) * S := by
    have hstep : S * (1 + Ct) * S = S * S + S * Ct * S := by
      rw [mul_add, add_mul, mul_one]
    rw [hstep, hSCS, hSS]
  have hdetA : A.det = (((∏ i, hS_psd.isHermitian.eigenvalues i) *
      (∏ i, hS_psd.isHermitian.eigenvalues i) : ℝ) : ℂ) := by
    rw [← hSS, Matrix.det_mul, hS_det, ← Complex.ofReal_mul]
  have hCt_det : Ct.det =
      ((∏ i, hCt_psd.isHermitian.eigenvalues i : ℝ) : ℂ) := by
    rw [hCt_psd.isHermitian.det_eq_prod_eigenvalues]
    exact (Complex.ofReal_prod _ _).symm
  have hdetB : B.det = ((((∏ i, hS_psd.isHermitian.eigenvalues i) *
      (∏ i, hCt_psd.isHermitian.eigenvalues i)) *
      (∏ i, hS_psd.isHermitian.eigenvalues i) : ℝ) : ℂ) := by
    rw [← hSCS, Matrix.det_mul, Matrix.det_mul, hS_det, hCt_det,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hdetAB : (A + B).det = ((((∏ i, hS_psd.isHermitian.eigenvalues i) *
      (∏ i, (1 + hCt_psd.isHermitian.eigenvalues i))) *
      (∏ i, hS_psd.isHermitian.eigenvalues i) : ℝ) : ℂ) := by
    rw [hAB, Matrix.det_mul, Matrix.det_mul, hS_det,
      det_one_add_eq_ofReal_prod hCt_psd, ← Complex.ofReal_mul,
      ← Complex.ofReal_mul]
  have hdetA_re : (A.det).re =
      (∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hS_psd.isHermitian.eigenvalues i := by
    rw [hdetA, Complex.ofReal_re]
  have hdetB_re : (B.det).re =
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        (∏ i, hCt_psd.isHermitian.eigenvalues i)) *
        ∏ i, hS_psd.isHermitian.eigenvalues i := by
    rw [hdetB, Complex.ofReal_re]
  have hdetAB_re : ((A + B).det).re =
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        (∏ i, (1 + hCt_psd.isHermitian.eigenvalues i))) *
        ∏ i, hS_psd.isHermitian.eigenvalues i := by
    rw [hdetAB, Complex.ofReal_re]
  have hkey := one_add_det_re_rpow_ge hCt_psd hn
  rw [det_re_eq_prod_eigenvalues hCt_psd, det_one_add_re_eq_prod hCt_psd] at hkey
  have hprod_eig_nonneg : 0 ≤ ∏ i, hCt_psd.isHermitian.eigenvalues i :=
    Finset.prod_nonneg fun i _ => hCt_psd.eigenvalues_nonneg i
  have hprod_one_nonneg : 0 ≤ ∏ i, (1 + hCt_psd.isHermitian.eigenvalues i) :=
    Finset.prod_nonneg fun i _ => by linarith [hCt_psd.eigenvalues_nonneg i]
  have hddS : 0 ≤ (∏ i, hS_psd.isHermitian.eigenvalues i) *
      ∏ i, hS_psd.isHermitian.eigenvalues i := mul_nonneg hdS_nonneg hdS_nonneg
  have hBfac : (((∏ i, hS_psd.isHermitian.eigenvalues i) *
      ∏ i, hS_psd.isHermitian.eigenvalues i) *
      ∏ i, hCt_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) =
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hS_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) *
      (∏ i, hCt_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) :=
    Real.mul_rpow hddS hprod_eig_nonneg
  have hABfac : (((∏ i, hS_psd.isHermitian.eigenvalues i) *
      ∏ i, hS_psd.isHermitian.eigenvalues i) *
      ∏ i, (1 + hCt_psd.isHermitian.eigenvalues i)) ^ ((n : ℝ)⁻¹) =
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hS_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) *
      (∏ i, (1 + hCt_psd.isHermitian.eigenvalues i)) ^ ((n : ℝ)⁻¹) :=
    Real.mul_rpow hddS hprod_one_nonneg
  have hfactor : ((∏ i, hS_psd.isHermitian.eigenvalues i) *
      ∏ i, hS_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) +
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hS_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) *
      (∏ i, hCt_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) =
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hS_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹) *
      (1 + (∏ i, hCt_psd.isHermitian.eigenvalues i) ^ ((n : ℝ)⁻¹)) := by
    rw [mul_add, mul_one]
  have hfacB : ((∏ i, hS_psd.isHermitian.eigenvalues i) *
      (∏ i, hCt_psd.isHermitian.eigenvalues i)) *
      ∏ i, hS_psd.isHermitian.eigenvalues i =
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hCt_psd.isHermitian.eigenvalues i := by ring
  have hfacAB : ((∏ i, hS_psd.isHermitian.eigenvalues i) *
      (∏ i, (1 + hCt_psd.isHermitian.eigenvalues i))) *
      ∏ i, hS_psd.isHermitian.eigenvalues i =
      ((∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, hS_psd.isHermitian.eigenvalues i) *
        ∏ i, (1 + hCt_psd.isHermitian.eigenvalues i) := by ring
  rw [hdetA_re, hdetB_re, hdetAB_re, hfacB, hfacAB, hBfac, hABfac, hfactor]
  exact mul_le_mul_of_nonneg_left hkey (Real.rpow_nonneg hddS _)

/-- **Minkowski's determinant inequality**: for positive semidefinite
`A` and `B`,
`(det (A + B)) ^ (1 / n) ≥ (det A) ^ (1 / n) + (det B) ^ (1 / n)`. -/
theorem PosSemidef.minkowski_det (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hn : 0 < n) :
    (A.det).re ^ ((n : ℝ)⁻¹) + (B.det).re ^ ((n : ℝ)⁻¹) ≤
      ((A + B).det).re ^ ((n : ℝ)⁻¹) := by
  have hp : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr (Nat.cast_pos.mpr hn)
  have hcont : Continuous
      (fun ε : ℝ =>
        ((((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A + B).det).re) ^
          ((n : ℝ)⁻¹) -
        ((((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A).det).re) ^
          ((n : ℝ)⁻¹)) := by
    apply Continuous.sub
    · apply Continuous.rpow
      · exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop :
          Continuous (fun ε : ℝ => ((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A + B))))
      · exact continuous_const
      · intro ε
        exact Or.inr hp
    · apply Continuous.rpow
      · exact Complex.continuous_re.comp (Continuous.matrix_det (by fun_prop :
          Continuous (fun ε : ℝ => ((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A))))
      · exact continuous_const
      · intro ε
        exact Or.inr hp
  have htend : Filter.Tendsto
      (fun ε : ℝ =>
        ((((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A + B).det).re) ^
          ((n : ℝ)⁻¹) -
        ((((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A).det).re) ^
          ((n : ℝ)⁻¹))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((A + B).det).re ^ ((n : ℝ)⁻¹) - (A.det).re ^ ((n : ℝ)⁻¹))) := by
    have h := (hcont.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa using h
  have hbound : (B.det).re ^ ((n : ℝ)⁻¹) ≤
      ((A + B).det).re ^ ((n : ℝ)⁻¹) - (A.det).re ^ ((n : ℝ)⁻¹) := by
    apply ge_of_tendsto htend
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hpos : ((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (by exact_mod_cast hε')
    have hAε : ((ε : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + A).PosDef :=
      hpos.add_posSemidef hA
    have hstep := hAε.minkowski_det_aux hB hn
    linarith [hstep]
  linarith [hbound]

/-- **Monotonicity of the determinant on the positive semidefinite cone**:
`det B ≤ det (A + B)` for `A` and `B` positive semidefinite. -/
theorem PosSemidef.det_le_det_add (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (B.det).re ≤ ((A + B).det).re := by
  by_cases hn : n = 0
  · subst n
    simp only [Matrix.det_fin_zero, le_refl]
  have hn : 0 < n := Nat.pos_of_ne_zero hn
  have hp : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr (Nat.cast_pos.mpr hn)
  have hle := hA.minkowski_det hB hn
  have hB' : 0 ≤ (B.det).re ^ ((n : ℝ)⁻¹) + (A.det).re ^ ((n : ℝ)⁻¹) := by
    exact add_nonneg (Real.rpow_nonneg (det_re_nonneg hB) _)
      (Real.rpow_nonneg (det_re_nonneg hA) _)
  have hle' : (B.det).re ^ ((n : ℝ)⁻¹) ≤ ((A + B).det).re ^ ((n : ℝ)⁻¹) := by
    linarith [hle, Real.rpow_nonneg (det_re_nonneg hA) ((n : ℝ)⁻¹)]
  exact (Real.rpow_le_rpow_iff (det_re_nonneg hB)
    (det_re_nonneg (hA.add hB)) hp).mp hle'

end Matrix
