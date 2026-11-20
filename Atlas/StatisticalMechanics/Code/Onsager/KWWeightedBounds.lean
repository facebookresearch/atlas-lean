/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Onsager.KWWeightedDeletion
import Code.Onsager.KWSpectral








namespace StatMech.Onsager

open Matrix BigOperators

theorem norm_ons_KWmatWeightedPhase_entry_le
    (L : ℕ) (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q)
    (d2 d1 : ons_Dart L) :
    ‖ons_KWmatWeightedPhase L weight ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b) d2 d1‖ ≤ q := by
  unfold ons_KWmatWeightedPhase ons_KWmatWeighted
  have hphase :
      ‖ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) d1.2‖ = 1 := by
    generalize hmu : d1.2 = mu
    fin_cases mu <;> simp [ons_dirPhase, norm_ons_spinPhase]
  split
  · rw [norm_mul, norm_mul, hphase, one_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _)
      (norm_ons_turnW_turnRoot_le_one d1.2 d2.2)).trans (hweight _)
  · simp [hq]

theorem ons_card_mul_lt_one_of_Sherman_small
    {E : Type*} [Fintype E] [Nonempty E]
    (q : ℝ)
    (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹) :
    (Fintype.card E : ℝ) * q < 1 := by
  let C : ℝ := Fintype.card E
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact_mod_cast Fintype.card_pos
  have hden : 0 < 2 * C ^ 2 := by positivity
  have hmul : q * (2 * C ^ 2) < 1 := by
    rw [inv_eq_one_div] at hsmall
    exact (lt_div_iff₀ hden).mp hsmall
  nlinarith

theorem ons_matrix_norm_le_of_entry
    {E : Type*} [Fintype E] [DecidableEq E]
    (A : Matrix E E ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ i j, ‖A i j‖ ≤ q) :
    letI : NormedRing (Matrix E E ℂ) := Matrix.linftyOpNormedRing
    ‖A‖ ≤ (Fintype.card E : ℝ) * q := by
  letI : NormedRing (Matrix E E ℂ) := Matrix.linftyOpNormedRing
  have hentryNN : ∀ i j, ‖A i j‖₊ ≤ Real.toNNReal q := by
    intro i j
    apply NNReal.coe_le_coe.mp
    simpa [Real.coe_toNNReal q hq] using hentry i j
  have hnn : ‖A‖₊ ≤
      (Fintype.card E : ℕ) * Real.toNNReal q := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i hi
    calc
      (∑ j : E, ‖A i j‖₊) ≤ ∑ _j : E, Real.toNNReal q := by
        apply Finset.sum_le_sum
        intro j hj
        exact hentryNN i j
      _ = (Fintype.card E : ℕ) * Real.toNNReal q := by simp
  have hc := NNReal.coe_le_coe.mpr hnn
  simpa [Real.coe_toNNReal q hq] using hc

theorem ons_spectral_lt_one_of_entry
    {E : Type*} [Fintype E] [DecidableEq E]
    (A : Matrix E E ℂ) (q : ℝ) (hq : 0 ≤ q)
    (hentry : ∀ i j, ‖A i j‖ ≤ q)
    (hcard : (Fintype.card E : ℝ) * q < 1) :
    ∀ alpha ∈ A.charpoly.roots, ‖alpha‖ < 1 := by
  letI : NormedRing (Matrix E E ℂ) := Matrix.linftyOpNormedRing
  intro alpha halpha
  have hroot : A.charpoly.IsRoot alpha :=
    (Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mp halpha
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
    ((ons_matrix_norm_le_of_entry A q hq hentry).trans_lt hcard)

theorem ons_KWmatWeightedPhase_detWalkRoot_sq
    (L : ℕ) [NeZero L]
    (weight : Sym2 (ZMod L × ZMod L) → ℂ)
    (a b : Fin 2) (q : ℝ) (hq : 0 ≤ q)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card (ons_Dart L) : ℝ) ^ 2)⁻¹) :
    ons_detWalkRoot (ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)) ^ 2 =
      (1 - ons_KWmatWeightedPhase L weight ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det := by
  let M := ons_KWmatWeightedPhase L weight ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b)
  have hentry : ∀ d2 d1, ‖M d2 d1‖ ≤ q :=
    norm_ons_KWmatWeightedPhase_entry_le L weight a b q hq hweight
  have hcard : (Fintype.card (ons_Dart L) : ℝ) * q < 1 :=
    ons_card_mul_lt_one_of_Sherman_small q hsmall
  exact ons_detWalkRoot_sq M
    (ons_spectral_lt_one_of_entry M q hq hentry hcard)

end StatMech.Onsager
