/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.BeamPlasticCollapse
import PhyslibExt.Mechanics.PlasticSection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Fixed-ended beam plastic hinge certificate checks

Concrete consumers of `PhyslibExt.Mechanics.BeamPlasticCollapse`: entry values and the
totalized-span conventions; the nonzero witnesses `L = 2, Mp = 3` (collapse intensity `12`,
hinge rotations `(-1, 2, -1)`) and `L = 4, Mp = 5` (works `10` and `2 * w`, balance exactly at
`w = 5`); composition of the static, kinematic and complementarity certificates into
`PlasticWork.loadFactor_eq_of_complementary`; the rectangular-section instance through
`Mechanics.PlasticSection.sectionMoment_fullyPlasticStress` with collapse intensity
`4 * σy * b * h ^ 2 / L ^ 2`; complementarity forcing the signed field `![-Mp, Mp, -Mp]` and
rejecting a wrongly signed field; deflection support and centre values; forced slopes;
diagram values and the `1.01` tightness control; uniqueness of the normalized mechanism;
sign-convention controls; and premise controls at `L = 0`, `Mp < 0`, `Mp = 0` and `L = -2`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

None; every declaration is a check against `PhyslibExt.Mechanics.BeamPlasticCollapse`.

## iii. Table of contents

- O. Orientation and parsing
- W. Nonzero witnesses
- C. Composition through the canonical certificate
- S. Sign-convention controls
- N. Premise controls
- U. Uniqueness and the direct bound

## iv. References

- B. G. Neal, *The Plastic Methods of Structural Analysis*, 3rd (S.I.) edition, Chapman and
  Hall, 1977, section 2.3.

-/

namespace PhyslibExtTest.Mechanics.BeamPlasticCollapse

open Matrix
open _root_.Mechanics.BeamPlasticCollapse

/-! ## O. Orientation and parsing -/

private theorem O1_entries (L : ℝ) :
    hingeRotation L 0 0 = -2 / L ∧ hingeRotation L 1 0 = 4 / L ∧ hingeRotation L 2 0 = -2 / L :=
  ⟨rfl, rfl, rfl⟩

private theorem O2_parse (L : ℝ) : (-2 / L : ℝ) = (-2) / L := rfl

private theorem O3_transpose_row (L : ℝ) (σ : Fin 3 → ℝ) :
    ((hingeRotation L)ᵀ *ᵥ σ) 0 = -2 / L * σ 0 + 4 / L * σ 1 + -2 / L * σ 2 := by
  simp [hingeRotation, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem O4_virtualWork (L δ : ℝ) (σ : Fin 3 → ℝ) :
    σ ⬝ᵥ (hingeRotation L *ᵥ ![δ]) = ((hingeRotation L)ᵀ *ᵥ σ) ⬝ᵥ ![δ] := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]

private theorem O5_hingeRotation_zero : hingeRotation 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [hingeRotation]

private theorem O6_totalized : uniformLoadWork 0 = 0 ∧ (![2 / 0] : Fin 1 → ℝ) = 0 ∧
    ∀ Mp : ℝ, 16 * Mp / (0 : ℝ) ^ 2 = 0 := by
  refine ⟨?_, ?_, fun Mp => by simp⟩
  · ext i; fin_cases i; simp [uniformLoadWork]
  · ext i; fin_cases i; simp

/-! ## W. Nonzero witnesses (L = 2, Mp = 3: collapse intensity 12; L = 4, Mp = 5: 5) -/

private theorem W1_static : (hingeRotation 2)ᵀ *ᵥ ![-3, 3, -3] = (12 : ℝ) • uniformLoadWork 2 ∧
    ∀ e : Fin 3, |(![-3, 3, -3] : Fin 3 → ℝ) e| ≤ 3 := by
  have h := collapseMoments_staticCertificate 2 (Mp := 3) (by norm_num)
  norm_num at h ⊢
  exact h

private theorem W2_kinematic : uniformLoadWork 2 ⬝ᵥ ![2 / 2] = 1 ∧
    ∑ e, (3 : ℝ) * |(hingeRotation 2 *ᵥ ![2 / 2]) e| = 12 := by
  have h := collapseMechanism_kinematicCertificate (L := 2) 3 (by norm_num)
  norm_num at h ⊢
  exact h

private theorem W2b_rotations : hingeRotation 2 *ᵥ ![1] = ![-1, 2, -1] := by
  ext i; fin_cases i <;> simp [hingeRotation, Matrix.mulVec, dotProduct]; norm_num

/-- T4 integrated with the canonical owner theorem (no binder left). -/
private theorem W3_isGreatest_integrated :
    IsGreatest {w : ℝ | ∃ σ : Fin 3 → ℝ,
        (hingeRotation 2)ᵀ *ᵥ σ = w • uniformLoadWork 2 ∧ ∀ e, |σ e| ≤ 3} 12 := by
  have h := collapseLoad_isGreatest (L := 2) (Mp := 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h

private theorem W4_unitMechanism (w : ℝ) :
    ∑ e, (5 : ℝ) * |(hingeRotation 4 *ᵥ ![1]) e| = 10 ∧
      (w • uniformLoadWork 4) ⬝ᵥ ![1] = 2 * w ∧
      (∑ e, (5 : ℝ) * |(hingeRotation 4 *ᵥ ![1]) e| = (w • uniformLoadWork 4) ⬝ᵥ ![1] ↔
        w = 5) := by
  obtain ⟨h1, h2, h3⟩ := unitMechanism_work (L := 4) 5 w (by norm_num)
  refine ⟨by rw [h1]; norm_num, by rw [h2]; ring, ?_⟩
  rw [h3]; norm_num

private theorem W4b_unbalanced : ¬ (∑ e, (5 : ℝ) * |(hingeRotation 4 *ᵥ ![1]) e| =
    ((6 : ℝ) • uniformLoadWork 4) ⬝ᵥ ![1]) := by
  rw [(W4_unitMechanism 6).2.2]; norm_num

private theorem W5_elastic : (hingeRotation 2)ᵀ *ᵥ ![-4, 2, -4] = (12 : ℝ) • uniformLoadWork 2 ∧
    ¬ ∀ e : Fin 3, |(![-4, 2, -4] : Fin 3 → ℝ) e| ≤ 3 := by
  have h := elasticMoments_not_admissible 2 (Mp := 3) (by norm_num)
  norm_num at h ⊢
  exact h

private theorem W6_statics : (hingeRotation 2)ᵀ *ᵥ ![-3, 3, -3] = (12 : ℝ) • uniformLoadWork 2 ↔
    (3 : ℝ) - (-3 + -3) / 2 = 12 * 2 ^ 2 / 8 :=
  hingeRotation_transpose_mulVec_eq_iff (L := 2) ![-3, 3, -3] 12 (by norm_num)

private theorem W7_diagram_values :
    (16 * 3 / (2 : ℝ) ^ 2 / 2) * (2 * 0 - 0 ^ 2) - 3 = -3 ∧
    (16 * 3 / (2 : ℝ) ^ 2 / 2) * (2 * 1 - 1 ^ 2) - 3 = 3 ∧
    (16 * 3 / (2 : ℝ) ^ 2 / 2) * (2 * 2 - 2 ^ 2) - 3 = -3 := by norm_num

private theorem W7b_diagram_values_general {L Mp : ℝ} (hL : 0 < L) :
    (16 * Mp / L ^ 2 / 2) * (L * 0 - 0 ^ 2) - Mp = -Mp ∧
    (16 * Mp / L ^ 2 / 2) * (L * (L / 2) - (L / 2) ^ 2) - Mp = Mp ∧
    (16 * Mp / L ^ 2 / 2) * (L * L - L ^ 2) - Mp = -Mp := by
  refine ⟨by ring, ?_, by ring⟩
  field_simp
  ring

/-- Tightness: at 1.01 times the collapse intensity the mid-span moment exceeds `Mp`. -/
private theorem W7c_tight : 3 < (16 * 3 / (2 : ℝ) ^ 2 * (101 / 100) / 2) * (2 * 1 - 1 ^ 2) - 3 := by
  norm_num

private theorem W8_deflection_values {L δ : ℝ} (hL : 0 < L) :
    mechanismDeflection L δ 0 = 0 ∧ mechanismDeflection L δ L = 0 ∧
      mechanismDeflection L δ (L / 2) = δ := by
  refine ⟨by simp [mechanismDeflection, min_eq_left hL.le], ?_, ?_⟩
  · simp [mechanismDeflection, min_eq_right hL.le]
  · simp only [mechanismDeflection]
    rw [show L - L / 2 = L / 2 by ring, min_self]
    field_simp

/-- B3's witnesses are forced for `0 < L` (derivative uniqueness at an interior point). -/
private theorem W9_slopes_unique {L δ s₁ s₂ : ℝ} (hL : 0 < L)
    (h1 : ∀ x ∈ Set.Ioo 0 (L / 2), HasDerivAt (mechanismDeflection L δ) s₁ x)
    (h2 : ∀ x ∈ Set.Ioo (L / 2) L, HasDerivAt (mechanismDeflection L δ) s₂ x) :
    s₁ = 2 * δ / L ∧ s₂ = -(2 * δ / L) := by
  obtain ⟨t₁, t₂, ht₁, ht₂, -⟩ := hingeRotation_mulVec_eq_slopeJumps L δ
  -- reconstruct the explicit slopes at interior points
  have hx1 : L / 4 ∈ Set.Ioo 0 (L / 2) := ⟨by positivity, by linarith⟩
  have hx2 : 3 * L / 4 ∈ Set.Ioo (L / 2) L := ⟨by linarith, by linarith⟩
  have e1 : s₁ = t₁ := (h1 _ hx1).unique (ht₁ _ hx1)
  have e2 : s₂ = t₂ := (h2 _ hx2).unique (ht₂ _ hx2)
  have hev1 : HasDerivAt (mechanismDeflection L δ) (2 * δ / L) (L / 4) := by
    have hmem : {y : ℝ | y < L - y} ∈ nhds (L / 4) :=
      (isOpen_lt continuous_id (continuous_const.sub continuous_id)).mem_nhds
        (by change L / 4 < L - L / 4; linarith)
    have hev : mechanismDeflection L δ =ᶠ[nhds (L / 4)] fun y => 2 * δ / L * y := by
      filter_upwards [hmem] with y hy
      simp only [mechanismDeflection, min_eq_left (le_of_lt hy)]
    exact (by simpa using (hasDerivAt_id (L / 4)).const_mul (2 * δ / L) :
      HasDerivAt (fun y => 2 * δ / L * y) (2 * δ / L) (L / 4)).congr_of_eventuallyEq hev
  have hev2 : HasDerivAt (mechanismDeflection L δ) (-(2 * δ / L)) (3 * L / 4) := by
    have hmem : {y : ℝ | L - y < y} ∈ nhds (3 * L / 4) :=
      (isOpen_lt (continuous_const.sub continuous_id) continuous_id).mem_nhds
        (by change L - 3 * L / 4 < 3 * L / 4; linarith)
    have hev : mechanismDeflection L δ =ᶠ[nhds (3 * L / 4)] fun y => 2 * δ / L * (L - y) := by
      filter_upwards [hmem] with y hy
      simp only [mechanismDeflection, min_eq_right (le_of_lt hy)]
    exact (by simpa using ((hasDerivAt_id (3 * L / 4)).const_sub L).const_mul (2 * δ / L) :
      HasDerivAt (fun y => 2 * δ / L * (L - y)) (-(2 * δ / L)) (3 * L / 4)).congr_of_eventuallyEq
        hev
  exact ⟨(h1 _ hx1).unique hev1, (h2 _ hx2).unique hev2⟩

private theorem W10_work_integral : ∫ x in (0 : ℝ)..2, 3 * mechanismDeflection 2 1 x = 3 := by
  rw [integral_mechanismDeflection (L := 2) 3 1 (by norm_num)]
  simp [uniformLoadWork, dotProduct]

/-! ## C. Complementary slackness content -/

/-- T1-T3 compose in the canonical equality theorem (owner compiled from main). -/
private theorem C1_compose {L Mp : ℝ} (hL : 0 < L) (hMp : 0 ≤ Mp) :
    16 * Mp / L ^ 2 = ∑ e, (fun _ : Fin 3 => Mp) e * |(hingeRotation L *ᵥ ![2 / L]) e| :=
  PlasticWork.loadFactor_eq_of_complementary (hingeRotation L) ![-Mp, Mp, -Mp] (fun _ => Mp)
    (uniformLoadWork L) ![2 / L] (16 * Mp / L ^ 2)
    (collapseMoments_staticCertificate L hMp).1 (collapseMoments_staticCertificate L hMp).2
    (collapseMechanism_kinematicCertificate Mp hL).1
    (collapseCertificates_complementary L Mp)

/-- Rectangular-section instance: with the fully plastic moment `σy * b * h ^ 2 / 4` of a
rectangular section, the collapse intensity is `4 * σy * b * h ^ 2 / L ^ 2`. -/
private theorem R1_rectangular {σy b h L : ℝ} (hσ : 0 < σy) (hb : 0 < b) (hh : 0 < h)
    (hL : 0 < L) :
    IsGreatest {w : ℝ | ∃ σ : Fin 3 → ℝ,
        (hingeRotation L)ᵀ *ᵥ σ = w • uniformLoadWork L ∧
        ∀ e, |σ e| ≤ _root_.Mechanics.PlasticSection.sectionMoment b h
          (_root_.Mechanics.PlasticSection.fullyPlasticStress σy)}
      (4 * σy * b * h ^ 2 / L ^ 2) := by
  rw [_root_.Mechanics.PlasticSection.sectionMoment_fullyPlasticStress b σy hh]
  have hMp : (0 : ℝ) ≤ σy * b * h ^ 2 / 4 := by positivity
  have hgreat := collapseLoad_isGreatest (L := L) (Mp := σy * b * h ^ 2 / 4) hL hMp
  have hval : 16 * (σy * b * h ^ 2 / 4) / L ^ 2 = 4 * σy * b * h ^ 2 / L ^ 2 := by ring
  rwa [hval] at hgreat

/-- Complementarity with the normalized mechanism forces the static field (signs included). -/
private theorem C2_complementarity_forces_field {L Mp : ℝ} (hL : 0 < L) (σ : Fin 3 → ℝ)
    (hc : ∀ e, Mp * |(hingeRotation L *ᵥ ![2 / L]) e| = σ e * (hingeRotation L *ᵥ ![2 / L]) e) :
    σ = ![-Mp, Mp, -Mp] := by
  have hv : hingeRotation L *ᵥ ![2 / L] = ![-(4 / L ^ 2), 8 / L ^ 2, -(4 / L ^ 2)] := by
    ext i
    fin_cases i <;> simp [hingeRotation, Matrix.mulVec, dotProduct] <;> ring
  have hp : 0 < 4 / L ^ 2 := by positivity
  have hq : 0 < 8 / L ^ 2 := by positivity
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  rw [hv] at h0 h1 h2
  simp [abs_of_pos hp, abs_of_pos hq] at h0 h1 h2
  have e0 : σ 0 = -Mp := by
    have : (σ 0 + Mp) * (4 / L ^ 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hp.ne'
  have e1 : σ 1 = Mp := (h1.resolve_right hL.ne').symm
  have e2 : σ 2 = -Mp := by
    have : (σ 2 + Mp) * (4 / L ^ 2) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hp.ne'
  ext i
  fin_cases i <;> simp [e0, e1, e2]

/-- A wrongly signed field is not complementary with the mechanism. -/
private theorem C3_wrong_sign_not_complementary :
    ¬ ∀ e, (3 : ℝ) * |(hingeRotation 2 *ᵥ ![2 / 2]) e| =
      (![3, 3, -3] : Fin 3 → ℝ) e * (hingeRotation 2 *ᵥ ![2 / 2]) e := by
  intro h
  have h0 := h 0
  simp [hingeRotation, Matrix.mulVec, dotProduct] at h0
  norm_num at h0

/-! ## S. Sign-convention controls -/

/-- Magnitude rotations `(2/L, 4/L, 2/L)` with the signed field give zero generalized force. -/
private theorem S1_magnitude_rotations_break_statics {L Mp : ℝ} :
    (!![2 / L; 4 / L; 2 / L] : Matrix (Fin 3) (Fin 1) ℝ)ᵀ *ᵥ ![-Mp, Mp, -Mp] = 0 := by
  ext i; fin_cases i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]; ring

private theorem S1b_magnitude_rotations_not_static :
    (!![2 / 2; 4 / 2; 2 / 2] : Matrix (Fin 3) (Fin 1) ℝ)ᵀ *ᵥ ![-3, 3, -3] ≠
      (12 : ℝ) • uniformLoadWork 2 := by
  rw [S1_magnitude_rotations_break_statics]
  intro h
  have := congrFun h 0
  simp [uniformLoadWork] at this

/-- The simply supported field `(0, 2Mp, 0)` is another equilibrium field at the collapse
intensity that violates capacity. -/
private theorem S2_simply_supported_field (L : ℝ) {Mp : ℝ} (hMp : 0 < Mp) :
    (hingeRotation L)ᵀ *ᵥ ![0, 2 * Mp, 0] = (16 * Mp / L ^ 2) • uniformLoadWork L ∧
      ¬ ∀ e : Fin 3, |(![0, 2 * Mp, 0] : Fin 3 → ℝ) e| ≤ Mp := by
  refine ⟨?_, ?_⟩
  · ext i; fin_cases i
    simp [hingeRotation, uniformLoadWork, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    rcases eq_or_ne L 0 with rfl | hL
    · simp
    · field_simp; ring
  · intro h; have := h 1; simp [abs_of_pos hMp] at this; linarith

/-- The admissible set is symmetric: the reversed field certifies `-16 Mp / L ^ 2`. -/
private theorem S3_lower_end {L Mp : ℝ} (hMp : 0 ≤ Mp) :
    (hingeRotation L)ᵀ *ᵥ ![Mp, -Mp, Mp] = (-(16 * Mp / L ^ 2)) • uniformLoadWork L ∧
      ∀ e : Fin 3, |(![Mp, -Mp, Mp] : Fin 3 → ℝ) e| ≤ Mp := by
  have h := collapseMoments_staticCertificate L hMp
  refine ⟨?_, fun e => by fin_cases e <;> simp [abs_of_nonneg hMp]⟩
  have : (![Mp, -Mp, Mp] : Fin 3 → ℝ) = -![-Mp, Mp, -Mp] := by
    ext i; fin_cases i <;> simp
  rw [this, Matrix.mulVec_neg, h.1, neg_smul]

/-! ## N. Premise necessity (each premise removed gives a false instance) -/

private theorem N1_T1_needs_hMp : ¬ ∀ e : Fin 3, |(![-(-1), -1, -(-1)] : Fin 3 → ℝ) e| ≤ -1 := by
  intro h; have := h 0; norm_num at this

private theorem N2_T2_needs_span : uniformLoadWork 0 ⬝ᵥ ![2 / 0] ≠ 1 := by
  simp [uniformLoadWork, dotProduct]

private theorem N2b_T2_holds_at_negative_span :
    uniformLoadWork (-3) ⬝ᵥ ![2 / (-3)] = 1 ∧
      ∑ e, (1 : ℝ) * |(hingeRotation (-3) *ᵥ ![2 / (-3)]) e| = 16 * 1 / (-3) ^ 2 := by
  refine ⟨by simp [uniformLoadWork, dotProduct], ?_⟩
  simp [Fin.sum_univ_three, hingeRotation, Matrix.mulVec, dotProduct]
  norm_num [abs_of_pos, abs_of_neg]

private theorem N3_T4_needs_span :
    ¬ IsGreatest {w : ℝ | ∃ σ : Fin 3 → ℝ,
        (hingeRotation 0)ᵀ *ᵥ σ = w • uniformLoadWork 0 ∧ ∀ e, |σ e| ≤ 1}
      (16 * 1 / (0 : ℝ) ^ 2) := by
  rintro ⟨-, hub⟩
  have h1 : (1 : ℝ) ∈ {w : ℝ | ∃ σ : Fin 3 → ℝ,
      (hingeRotation 0)ᵀ *ᵥ σ = w • uniformLoadWork 0 ∧ ∀ e, |σ e| ≤ 1} := by
    refine ⟨0, ?_, fun e => by simp⟩
    rw [O5_hingeRotation_zero]
    ext i; fin_cases i; simp [uniformLoadWork]
  have := hub h1
  norm_num at this

private theorem N4_T4_needs_hMp :
    ¬ IsGreatest {w : ℝ | ∃ σ : Fin 3 → ℝ,
        (hingeRotation 1)ᵀ *ᵥ σ = w • uniformLoadWork 1 ∧ ∀ e, |σ e| ≤ -1}
      (16 * (-1) / (1 : ℝ) ^ 2) := by
  rintro ⟨⟨σ, -, hcap⟩, -⟩
  have := hcap 0
  linarith [abs_nonneg (σ 0)]

private theorem N5_F1_needs_span_negative :
    ∑ e, (1 : ℝ) * |(hingeRotation (-2) *ᵥ ![1]) e| ≠ 8 * 1 / (-2) := by
  simp [Fin.sum_univ_three, hingeRotation, Matrix.mulVec, dotProduct]
  norm_num

private theorem N5b_F1_needs_span_zero :
    ¬ (∑ e, (1 : ℝ) * |(hingeRotation 0 *ᵥ ![1]) e| = ((1 : ℝ) • uniformLoadWork 0) ⬝ᵥ ![1] ↔
        (1 : ℝ) = 16 * 1 / (0 : ℝ) ^ 2) := by
  simp [Fin.sum_univ_three, hingeRotation, Matrix.mulVec, dotProduct, uniformLoadWork]

private theorem N6_F2_needs_hMp : ∀ e : Fin 3,
    |(![-(4 * 0 / 3), 2 * 0 / 3, -(4 * 0 / 3)] : Fin 3 → ℝ) e| ≤ 0 := by
  intro e; fin_cases e <;> simp

private theorem N6b_F2_holds_for_negative_Mp : ¬ ∀ e : Fin 3,
    |(![-(4 * (-3) / 3), 2 * (-3) / 3, -(4 * (-3) / 3)] : Fin 3 → ℝ) e| ≤ -3 := by
  intro h; have := h 0; norm_num at this

private theorem N7_B1_needs_span :
    ((hingeRotation 0)ᵀ *ᵥ ![0, 1, 0] = (0 : ℝ) • uniformLoadWork 0) ∧
      ¬ ((![0, 1, 0] : Fin 3 → ℝ) 1 - ((![0, 1, 0] : Fin 3 → ℝ) 0 +
        (![0, 1, 0] : Fin 3 → ℝ) 2) / 2 = 0 * 0 ^ 2 / 8) := by
  refine ⟨?_, by norm_num⟩
  rw [O5_hingeRotation_zero]; simp

private theorem N8_B2_needs_hMp :
    ¬ |(16 * (-1) / (1 : ℝ) ^ 2 / 2) * (1 * 0 - 0 ^ 2) - (-1)| ≤ -1 := by norm_num

private theorem N9_B4_fails_negative_span :
    ∫ x in (0 : ℝ)..(-2), 1 * mechanismDeflection (-2) 1 x = -3 ∧
      ((1 : ℝ) • uniformLoadWork (-2)) ⬝ᵥ ![1] = -1 := by
  refine ⟨?_, by simp [uniformLoadWork, dotProduct]⟩
  have hcont : Continuous fun x => 1 * mechanismDeflection (-2) 1 x := by
    unfold mechanismDeflection; fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => 1 * mechanismDeflection (-2) 1 x)
      MeasureTheory.volume a b := fun a b => hcont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (-1)) (hi (-1) (-2))]
  have h1 : ∫ x in (0 : ℝ)..(-1), 1 * mechanismDeflection (-2) 1 x =
      ∫ x in (0 : ℝ)..(-1), (-1) * (-2 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_ge (by norm_num)] at hx
    simp only [mechanismDeflection]
    rw [min_eq_right (by linarith [hx.1])]
    norm_num
  have h2 : ∫ x in (-1 : ℝ)..(-2), 1 * mechanismDeflection (-2) 1 x =
      ∫ x in (-1 : ℝ)..(-2), (-1) * x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_ge (by norm_num)] at hx
    simp only [mechanismDeflection]
    rw [min_eq_left (by linarith [hx.2])]
    norm_num
  rw [h1, h2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id, integral_id, intervalIntegral.integral_const]
  norm_num

private theorem N9b_B4_holds_at_zero_span (w δ : ℝ) :
    ∫ x in (0 : ℝ)..0, w * mechanismDeflection 0 δ x = (w • uniformLoadWork 0) ⬝ᵥ ![δ] := by
  simp [uniformLoadWork, dotProduct]

/-! ## U. Uniqueness of the normalized mechanism (one generalized coordinate) -/

private theorem U1_normalized_mechanism_unique {L : ℝ} (hL : 0 < L) (v : Fin 1 → ℝ)
    (h : uniformLoadWork L ⬝ᵥ v = 1) : v = ![2 / L] := by
  ext i; fin_cases i
  simp [uniformLoadWork, dotProduct] at h ⊢
  field_simp
  linarith

/-! ## A. Direct upper bound without the binder (the binder is not needed for truth) -/

private theorem A1_upper_bound_direct {L Mp w : ℝ} (hL : 0 < L) (σ : Fin 3 → ℝ)
    (heq : (hingeRotation L)ᵀ *ᵥ σ = w • uniformLoadWork L) (hcap : ∀ e, |σ e| ≤ Mp) :
    w ≤ 16 * Mp / L ^ 2 := by
  have hb := (hingeRotation_transpose_mulVec_eq_iff σ w hL).1 heq
  have h0 := (abs_le.1 (hcap 0)).1
  have h1 := (abs_le.1 (hcap 1)).2
  have h2 := (abs_le.1 (hcap 2)).1
  rw [le_div_iff₀ (by positivity)]
  nlinarith


end PhyslibExtTest.Mechanics.BeamPlasticCollapse

#print axioms Mechanics.BeamPlasticCollapse.collapseMoments_staticCertificate
#print axioms Mechanics.BeamPlasticCollapse.collapseMechanism_kinematicCertificate
#print axioms Mechanics.BeamPlasticCollapse.collapseCertificates_complementary
#print axioms Mechanics.BeamPlasticCollapse.collapseLoad_isGreatest
#print axioms Mechanics.BeamPlasticCollapse.unitMechanism_work
#print axioms Mechanics.BeamPlasticCollapse.elasticMoments_not_admissible
#print axioms Mechanics.BeamPlasticCollapse.hingeRotation_transpose_mulVec_eq_iff
#print axioms Mechanics.BeamPlasticCollapse.collapseMomentDiagram_abs_le
#print axioms Mechanics.BeamPlasticCollapse.hingeRotation_mulVec_eq_slopeJumps
#print axioms Mechanics.BeamPlasticCollapse.integral_mechanismDeflection
