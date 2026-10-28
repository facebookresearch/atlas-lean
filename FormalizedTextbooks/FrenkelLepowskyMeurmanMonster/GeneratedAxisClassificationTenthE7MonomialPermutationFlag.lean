/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7MonomialProjectionRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7MonomialOutsideRecognition

/-! Every actual monomial matrix flag induces an element of the entire720 permutation flag group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Whole actual E7 projector commutation for a genuine original signed Golay permutation. -/
abbrev generatedTenthE7MonomialProjectionFixes (c : golayCode)
    (p : golayAutomorphismSubgroup) := ∀ x : Fin 24 → ℝ,
  (golayMonomialPair (c, p)).val (generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ x) =
    generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ (golayMonomialPair (c, p)).val x

/-- Whole actual unsigned norm-twelve fixation for a genuine signed Golay permutation. -/
abbrev generatedTenthE7MonomialLineFixes (c : golayCode) (p : golayAutomorphismSubgroup) :=
  leechIntegralAction (golayMonomialPair (c, p)) generatedTenthE7StandardNormTwelveLine =
      generatedTenthE7StandardNormTwelveLine ∨
    leechIntegralAction (golayMonomialPair (c, p)) generatedTenthE7StandardNormTwelveLine =
      -generatedTenthE7StandardNormTwelveLine

/-- Entire actual monomial projector fixation puts its permutation in the whole octad group. -/
theorem generatedTenth_e7_monomial_projection_octad_mem (c : golayCode)
    (p : golayAutomorphismSubgroup) (he : generatedTenthE7MonomialProjectionFixes c p) :
    p ∈ generatedTenthE7OctadPermutationGroup := by
  apply (generatedTenth_e7_octad_permutation_mem p).mpr
  funext i
  have h := (generatedTenth_e7_monomial_projection_support c p he (p.val.symm i)).1
  rw [p.val.apply_symm_apply] at h
  change golayStandardOctad (p.val.symm i) = golayStandardOctad i
  by_cases hi : i.val < 8
  · simp only [golayStandardOctad, ite_eq_left hi, ite_eq_left (h.mp hi)]
  · simp only [golayStandardOctad, ite_eq_right hi,
      ite_eq_right (fun hj => hi (h.mpr hj))]

/-- The entire actual permutation normal pair has precisely its two possible orientations. -/
theorem generatedTenth_e7_monomial_projection_normal_pair (c : golayCode)
    (p : golayAutomorphismSubgroup) (he : generatedTenthE7MonomialProjectionFixes c p) :
    (p.val 4 = 4 ∧ p.val 5 = 5) ∨ (p.val 4 = 5 ∧ p.val 5 = 4) := by
  have h4 := (generatedTenth_e7_monomial_projection_support c p he 4).2.mpr (Or.inl rfl)
  have h5 := (generatedTenth_e7_monomial_projection_support c p he 5).2.mpr (Or.inr rfl)
  rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5
  · exact False.elim ((by decide : (4 : Fin 24) ≠ 5)
      (p.val.injective (h4.trans h5.symm)))
  · exact Or.inl ⟨h4, h5⟩
  · exact Or.inr ⟨h4, h5⟩
  · exact False.elim ((by decide : (4 : Fin 24) ≠ 5)
      (p.val.injective (h4.trans h5.symm)))

/-- The actual octad-group element induced by the full original monomial projector fixer. -/
def generatedTenthE7MonomialOctadPermutation (c : golayCode) (p : golayAutomorphismSubgroup)
    (he : generatedTenthE7MonomialProjectionFixes c p) : generatedTenthE7OctadPermutationGroup :=
  ⟨p, generatedTenth_e7_monomial_projection_octad_mem c p he⟩

/-- The induced genuine whole octad permutation fixes the full unordered normal pair. -/
theorem generatedTenth_e7_monomial_projection_pair_fix (c : golayCode)
    (p : golayAutomorphismSubgroup) (he : generatedTenthE7MonomialProjectionFixes c p) :
    generatedTenthE7MonomialOctadPermutation c p he • generatedTenthE7OctadPairDataElement 22 =
      generatedTenthE7OctadPairDataElement 22 := by
  let q := generatedTenthE7MonomialOctadPermutation c p he
  rcases generatedTenth_e7_monomial_projection_normal_pair c p he with ⟨h4, h5⟩ | ⟨h4, h5⟩
  all_goals
    have hp4 := congrArg (fun i : Fin 24 => i.val) h4
    have hp5 := congrArg (fun i : Fin 24 => i.val) h5
    apply Subtype.ext
    change ({4, 5} : Finset (Fin 8)).map
      (generatedTenthE7OctadPointPermutationHom q).toEmbedding = {4, 5}
  · have hq4 : generatedTenthE7OctadPointPermutationHom q 4 = 4 := Fin.ext hp4
    have hq5 : generatedTenthE7OctadPointPermutationHom q 5 = 5 := Fin.ext hp5
    simp [hq4, hq5]
  · have hq4 : generatedTenthE7OctadPointPermutationHom q 4 = 5 := Fin.ext hp4
    have hq5 : generatedTenthE7OctadPointPermutationHom q 5 = 4 := Fin.ext hp5
    simp [hq4, hq5, Finset.pair_comm]

/-- The full actual companion source is exactly the normal pair plus the entire outside support. -/
theorem generatedTenth_e7_monomial_companion_source (i : Fin 24) :
    golayEncoder (golayLabelCoefficients 110) i =
      if (i = 4 ∨ i = 5) ∨ generatedTenthE7StandardOutside i then 1 else 0 := by
  rw [generatedTenth_e7_standard_companion_coordinate]
  fin_cases i <;> norm_num [generatedTenthE7StandardOutside]

/-- Entire original projector and unsigned-line fixation preserve
every companion-code coordinate. -/
theorem generatedTenth_e7_monomial_companion_coordinate (c : golayCode)
    (p : golayAutomorphismSubgroup) (he : generatedTenthE7MonomialProjectionFixes c p)
    (hl : generatedTenthE7MonomialLineFixes c p) (i : Fin 24) :
    golayEncoder (golayLabelCoefficients 110) (p.val i) =
      golayEncoder (golayLabelCoefficients 110) i := by
  have hp := (generatedTenth_e7_monomial_projection_support c p he i).2
  have ho := generatedTenth_e7_monomial_standard_line_support c p hl i
  rw [generatedTenth_e7_monomial_companion_source, generatedTenth_e7_monomial_companion_source]
  by_cases hn : i = 4 ∨ i = 5 <;> by_cases hout : generatedTenthE7StandardOutside i <;> simp_all

/-- The entire genuine induced permutation fixes the original companion label exactly. -/
theorem generatedTenth_e7_monomial_companion_label (c : golayCode)
    (p : golayAutomorphismSubgroup) (he : generatedTenthE7MonomialProjectionFixes c p)
    (hl : generatedTenthE7MonomialLineFixes c p) : golayLabelPermutation p 110 = 110 := by
  apply golayLabelCoefficients_injective
  apply golayEncoder_injective
  rw [golayLabelPermutation_word]
  funext i
  change golayEncoder (golayLabelCoefficients 110) (p.val.symm i) = _
  have h := generatedTenth_e7_monomial_companion_coordinate c p he hl (p.val.symm i)
  rw [p.val.apply_symm_apply] at h
  exact h.symm

/-- Every genuine original monomial matrix flag induces an actual whole720 permutation flag. -/
def generatedTenthE7MonomialFlagPermutation (c : golayCode) (p : golayAutomorphismSubgroup)
    (he : generatedTenthE7MonomialProjectionFixes c p)
    (hl : generatedTenthE7MonomialLineFixes c p) : generatedTenthE7StandardFlagPermutationGroup :=
  ⟨generatedTenthE7MonomialOctadPermutation c p he, by
    apply Prod.ext
    · exact generatedTenth_e7_monomial_projection_pair_fix c p he
    · exact generatedTenth_e7_monomial_companion_label c p he hl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
