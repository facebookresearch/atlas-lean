/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.Analysis.Matrix.Normed
import Code.Onsager.DetWalkExp
import Code.Onsager.KWSpinFourier

namespace StatMech.Onsager

theorem norm_ons_spinPhase (L : ℕ) (a : Fin 2) : ‖ons_spinPhase L a‖ = 1 := by
  unfold ons_spinPhase
  rw [Complex.norm_exp]
  simp

theorem norm_ons_turnRoot : ‖ons_turnRoot‖ = 1 := by
  unfold ons_turnRoot
  rw [Complex.norm_exp]
  simp

theorem norm_ons_turnW_turnRoot_le_one (mu nu : Fin 4) :
    ‖ons_turnW ons_turnRoot mu nu‖ ≤ 1 := by
  unfold ons_turnW
  split_ifs <;> simp [norm_ons_turnRoot]

theorem nnnorm_ons_KWmatPhase_le (L : ℕ) (x : ℝ) (a b : Fin 2)
    (d2 d1 : ons_Dart L) :
    ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖₊ ≤ ‖(x : ℂ)‖₊ := by
  unfold ons_KWmatPhase ons_KWmat
  split_ifs
  · rw [nnnorm_mul, nnnorm_mul]
    have hphase : ‖ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) d1.2‖ = 1 := by
      generalize hmu : d1.2 = mu
      fin_cases mu <;> simp [ons_dirPhase, norm_ons_spinPhase]
    have hphase' : ‖ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) d1.2‖₊ = 1 :=
      NNReal.eq hphase
    rw [hphase', one_mul]
    exact mul_le_of_le_one_right zero_le
      (by exact_mod_cast norm_ons_turnW_turnRoot_le_one d1.2 d2.2)
  · simp



theorem norm_ons_KWmatPhase_le (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2) :
    letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
      Matrix.linftyOpNormedRing
    ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)‖ ≤
        Fintype.card (ons_Dart L) * ‖x‖ := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
    Matrix.linftyOpNormedRing
  have hnn : ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)‖₊ ≤
      (Fintype.card (ons_Dart L) : ℕ) * ‖(x : ℂ)‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro d2 hd2
    calc
      (∑ d1 : ons_Dart L,
          ‖ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖₊) ≤
          ∑ _d1 : ons_Dart L, ‖(x : ℂ)‖₊ := by
            apply Finset.sum_le_sum
            intro d1 hd1
            exact nnnorm_ons_KWmatPhase_le L x a b d2 d1
      _ = (Fintype.card (ons_Dart L) : ℕ) * ‖(x : ℂ)‖₊ := by simp
  have hc := NNReal.coe_le_coe.mpr hnn
  simpa [Complex.norm_real, Real.norm_eq_abs] using hc


theorem ons_KWmatPhase_spectral_lt_one (L : ℕ) [NeZero L] (x : ℝ) (a b : Fin 2)
    (hx : Fintype.card (ons_Dart L) * ‖x‖ < 1) :
    ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1 := by
  letI : NormedRing (Matrix (ons_Dart L) (ons_Dart L) ℂ) :=
    Matrix.linftyOpNormedRing
  intro alpha halpha
  have hroot : (ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.IsRoot alpha :=
    (Polynomial.mem_roots
      (Matrix.charpoly_monic (ons_KWmatPhase L (x : ℂ) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b))).ne_zero).mp halpha
  let A := ons_KWmatPhase L (x : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  have heig : Module.End.HasEigenvalue (Matrix.toLin' A) alpha :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' A) alpha).2 <| by
      rw [Matrix.charpoly_toLin']
      exact hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hmul : ‖alpha‖ * ‖v‖ ≤ ‖A‖ * ‖v‖ := by
    rw [← norm_smul, ← hv.apply_eq_smul, Matrix.toLin'_apply]
    exact Matrix.linfty_opNorm_mulVec A v
  have halpha_le : ‖alpha‖ ≤ ‖A‖ :=
    le_of_mul_le_mul_right hmul (norm_pos_iff.mpr hv.2)
  exact lt_of_le_of_lt halpha_le
    ((norm_ons_KWmatPhase_le L x a b).trans_lt hx)




noncomputable def ons_KWconvergenceRadius (L : ℕ) [NeZero L] : ℝ :=
  (Fintype.card (ons_Dart L) : ℝ)⁻¹

theorem ons_KWconvergenceRadius_pos (L : ℕ) [NeZero L] :
    0 < ons_KWconvergenceRadius L := by
  unfold ons_KWconvergenceRadius
  positivity

theorem ons_KWmatPhase_spectral_small (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_KWconvergenceRadius L)) (a b : Fin 2) :
    ∀ alpha ∈ (ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).charpoly.roots,
      ‖alpha‖ < 1 := by
  apply ons_KWmatPhase_spectral_lt_one L x a b
  have hcard : 0 < (Fintype.card (ons_Dart L) : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_pos hx.1]
  have hxlt : x < 1 / (Fintype.card (ons_Dart L) : ℝ) := by
    simpa [ons_KWconvergenceRadius, div_eq_mul_inv] using hx.2
  exact (lt_div_iff₀' hcard).mp hxlt



theorem ons_KWmatPhase_det_eq_walk_exp (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_KWconvergenceRadius L)) (a b : Fin 2) :
    (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
      Complex.exp (- ∑' n : ℕ,
        (∑ v : Fin (n + 1) → ons_Dart L, ∏ k : Fin (n + 1),
          ons_KWmatPhase L (x : ℂ) ons_turnRoot
            (ons_spinPhase L a) (ons_spinPhase L b) (v k) (v (k + 1))) / (n + 1)) :=
  ons_det_eq_walk_exp _ (ons_KWmatPhase_spectral_small L hx a b)

end StatMech.Onsager
