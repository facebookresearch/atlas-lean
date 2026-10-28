/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthMarkingClasses
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftCorrectedTensor

/-! Actual full-axis fixation preserves absolute short coefficients under the literal spatial
action. Identification with the144-class candidate catalogue retains the missing octad
comparison explicitly; no projection or stabilizer order is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every genuine local fiber fixing the actual Ninth axis preserves short coefficient
magnitudes. -/
theorem generatedNinth_fixed_short_absolute (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis)
    (r : GriessShortIndex) :
    |(griessConwayEncode generatedNinthAxis).2.1 (griessShortPermutation f.val.2 r)| =
      |(griessConwayEncode generatedNinthAxis).2.1 r| := by
  have hh := congrArg (fun x => (griessConwayEncode x).2.1
    (griessShortPermutation f.val.2 r)) hfix
  rw [generatedFourth_local_short, localShortOperator_image] at hh
  have hs : |qSign (localShortPhase f r)| = 1 := by
    unfold qSign
    split_ifs <;> norm_num
  rw [← hh, abs_mul, hs, one_mul]

/-- Actual full-axis fixation transports the candidate marking labels once their exact
actual octad comparison has been supplied. -/
theorem generatedNinth_fixed_marking_label_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns)
    (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis)
    (r : GriessShortIndex) (hr : r ∈ generatedNinthShortMarkings) :
    griessShortPermutation f.val.2 r ∈ generatedNinthShortMarkings := by
  apply (generatedNinth_short_marking_iff_of_octad_comparison hoctad _).mp
  rw [generatedNinth_fixed_short_absolute f hfix]
  exact (generatedNinth_short_marking_iff_of_octad_comparison hoctad r).mpr hr

/-- The genuine spatial factor of every full-axis fixer transports all original candidate
marking classes once their exact actual octad comparison has been supplied. -/
theorem generatedNinth_fixed_marking_class_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns)
    (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis)
    (v : LeechModTwo) (hv : v ∈ generatedNinthMarkedShortClasses) :
    leechModTwoAction f.val.2 v ∈ generatedNinthMarkedShortClasses := by
  obtain ⟨r, hr, rfl⟩ := hv
  refine ⟨griessShortPermutation f.val.2 r,
    generatedNinth_fixed_marking_label_of_octad_comparison hoctad f hfix r hr, ?_⟩
  exact griessShortPermutation_class f.val.2 r

/-- The inverse of a genuine full-axis fixing fiber fixes the same actual axis. -/
theorem generatedNinth_fixed_local_inverse (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis) :
    rhoLocal (localFiberIntoH (f⁻¹)) generatedNinthAxis = generatedNinthAxis := by
  have hf : (localFiberIntoH f : H) • generatedNinthAxis = generatedNinthAxis := hfix
  change (localFiberIntoH (f⁻¹) : H) • generatedNinthAxis = generatedNinthAxis
  rw [map_inv]
  exact inv_smul_eq_iff.mpr hf.symm

/-- The exact actual spatial image of a full-axis fixing fiber preserves the entire marking
class set once the exact original octad comparison has been supplied. -/
theorem generatedNinth_fixed_marking_classes_image_of_octad_comparison
    (hoctad : ∀ (o : Fin 759) (e : Fin 64),
      |(griessConwayEncode generatedNinthAxis).2.1 (Sum.inr (Sum.inl (o, e)))| = 1 / 8 ↔
        o = 459 ∧ e ∈ generatedNinthOctadMarkedSigns)
    (f : localFiberSubgroup)
    (hfix : rhoLocal (localFiberIntoH f) generatedNinthAxis = generatedNinthAxis) :
    leechModTwoAction f.val.2 '' generatedNinthMarkedShortClasses =
      generatedNinthMarkedShortClasses := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact generatedNinth_fixed_marking_class_of_octad_comparison hoctad f hfix w hw
  · intro hv
    refine ⟨leechModTwoAction (f⁻¹).val.2 v,
      generatedNinth_fixed_marking_class_of_octad_comparison hoctad (f⁻¹)
        (generatedNinth_fixed_local_inverse f hfix) v hv, ?_⟩
    change leechModTwoAction f.val.2 (leechModTwoAction (f.val.2)⁻¹ v) = v
    rw [map_inv]
    exact LinearEquiv.apply_symm_apply _ v

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
