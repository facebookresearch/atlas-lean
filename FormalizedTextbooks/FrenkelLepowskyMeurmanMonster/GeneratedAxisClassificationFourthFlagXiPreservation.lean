/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthFlagXi
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationE8Rooted

/-! The signed actual three-bases element preserves the entire fourth coordinate section,
and hence belongs to the genuine, already counted section-short-line stabilizer. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem octad_tetrads : ∀ i j : Fin 24,
    golayEncoder (golayLabelCoefficients 14) i = 0 → i.val / 4 = j.val / 4 →
      golayEncoder (golayLabelCoefficients 14) j = 0 := by decide +kernel

private theorem xi_forward (u : leechIntegral)
    (hu : generatedOctadSupported (golayEncoder (golayLabelCoefficients 14)) u.val) :
    generatedOctadSupported (golayEncoder (golayLabelCoefficients 14))
      (leechIntegralAction co1XiIsometry u).val := by
  intro i hi
  have hn : (co1XiNumerator *ᵥ u.val) i = 0 := by
    change ∑ j, co1XiNumerator i j * u.val j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases h : i.val / 4 = j.val / 4
    · rw [hu j (octad_tetrads i j hi h), mul_zero]
    · simp only [co1XiNumerator, h, ite_false, zero_mul]
  have hd := congrFun (co1Xi_integral_double u) i
  change 2 * (leechIntegralAction co1XiIsometry u).val i = _ at hd
  rw [hn] at hd
  omega

/-- The actual Xi matrix preserves the two complete tetrads forming this genuine octad. -/
theorem generatedFourth_flag_xi_section_preserves :
    generatedOctadPreserves (golayEncoder (golayLabelCoefficients 14)) co1XiIsometry := by
  intro u
  constructor
  · intro h
    have h1 := xi_forward _ h
    have h2 := xi_forward _ h1
    have he : leechIntegralAction co1XiIsometry
        (leechIntegralAction co1XiIsometry (leechIntegralAction co1XiIsometry u)) = u := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← map_mul, ← map_mul]
      rw [show co1XiIsometry * co1XiIsometry * co1XiIsometry = co1XiIsometry ^ 3 by
        simp [pow_succ, mul_assoc], co1XiIsometry_cube, map_one]
      rfl
    rw [he] at h2
    exact h2
  · exact xi_forward u

private theorem preserves_mul (c : Fin 24 → ZMod 2) (g h : leechIsomSubgroup)
    (hg : generatedOctadPreserves c g) (hh : generatedOctadPreserves c h) :
    generatedOctadPreserves c (g * h) := by
  intro u
  rw [map_mul, LinearEquiv.mul_apply]
  exact (hg _).trans (hh u)

/-- The signed correction preserves the actual coordinate octad in both directions. -/
theorem generatedFourth_flag_normalized_xi_preserves :
    generatedOctadPreserves (golayOctadWord generatedFourthFlagOctad)
      generatedFourthFlagNormalizedXi := by
  have hc : golayOctadWord generatedFourthFlagOctad =
      golayEncoder (golayLabelCoefficients 14) := by
    unfold golayOctadWord
    rw [generatedFourthFlagOctad_label]
  rw [hc]
  have hp : generatedOctadPreserves (golayEncoder (golayLabelCoefficients 14))
      generatedFourthFlagCorrectionLeech := by
    intro u
    exact generatedOctadSupported_permutation _ _ generatedFourthFlagCorrectionGolay
      generatedFourthFlagCorrection_word u
  have hs := generatedAxisE8_sign_preserves
    (golayEncoder (golayLabelCoefficients 14)) generatedFourthFlagXiSign
  unfold generatedFourthFlagNormalizedXi
  exact preserves_mul _ _ _
    (preserves_mul _ _ _ (preserves_mul _ _ _ hs hp)
      generatedFourth_flag_xi_section_preserves) hs

/-- This genuine actual Xi-based element lies in the counted fourth flag stabilizer. -/
theorem generatedFourth_flag_normalized_xi_mem :
    generatedFourthFlagNormalizedXi ∈ generatedAxisE8ShortFlagStabilizer
      generatedFourthFlagOctad generatedFourthFlagShort := by
  rw [generatedAxisE8ShortFlagStabilizer_mem]
  exact ⟨generatedAxisE8_preserving_image _ _ generatedFourth_flag_normalized_xi_preserves,
    generatedFourth_flag_xi_short_label⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
