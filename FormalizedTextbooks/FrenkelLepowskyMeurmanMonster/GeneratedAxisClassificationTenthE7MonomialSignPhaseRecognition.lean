/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7MonomialPermutationFlag
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignedFlagLineFixing

/-! Every actual original monomial matrix fixer satisfies
the complete standard Golay phase fiber. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem original_line_coefficient (c : golayCode)
    (p : generatedTenthE7StandardFlagPermutationGroup) (i : Fin 6) :
    (leechIntegralAction (golayMonomialPair (c, p.val.val))
      generatedTenthE7StandardNormTwelveLine).val (generatedTenthE7StandardOutsideCoordinates i) =
      if c.val (generatedTenthE7StandardOutsideCoordinates i) = 0 then
        4 * generatedTenthE7IntegerSign (generatedTenthE7StandardOutsideSigns
          ((generatedTenthE7StandardOutsidePermutation p).symm i))
      else -(4 * generatedTenthE7IntegerSign (generatedTenthE7StandardOutsideSigns
        ((generatedTenthE7StandardOutsidePermutation p).symm i))) := by
  have h := generatedTenth_e7_monomial_standard_line_coordinate c p.val.val
    (p.val.val.val.symm (generatedTenthE7StandardOutsideCoordinates i))
  rw [p.val.val.val.apply_symm_apply] at h
  rw [h]
  have hp := generatedTenth_e7_standard_outside_permutation_coordinate p
    ((generatedTenthE7StandardOutsidePermutation p).symm i)
  rw [Equiv.apply_symm_apply] at hp
  have hpre : p.val.val.val.symm (generatedTenthE7StandardOutsideCoordinates i) =
      generatedTenthE7StandardOutsideCoordinates
        ((generatedTenthE7StandardOutsidePermutation p).symm i) :=
    (p.val.val.val.symm_apply_eq).mpr hp
  rw [hpre, generatedTenth_e7_standard_norm_line_sign]

/-- One common actual integer orientation determines the whole original binary phase equation. -/
theorem generatedTenth_e7_monomial_flag_line_phase (c : golayCode)
    (p : generatedTenthE7StandardFlagPermutationGroup) (e : ZMod 2)
    (h : leechIntegralAction (golayMonomialPair (c, p.val.val))
      generatedTenthE7StandardNormTwelveLine =
        generatedTenthE7IntegerSign e • generatedTenthE7StandardNormTwelveLine) (i : Fin 6) :
    c.val (generatedTenthE7StandardOutsideCoordinates i) +
      generatedTenthE7SignedFlagPhase p i = e := by
  have hc := congrArg (fun u : leechIntegral =>
    u.val (generatedTenthE7StandardOutsideCoordinates i)) h
  rw [original_line_coefficient] at hc
  change _ = generatedTenthE7IntegerSign e *
    generatedTenthE7StandardNormTwelveLine.val (generatedTenthE7StandardOutsideCoordinates i) at hc
  rw [generatedTenth_e7_standard_norm_line_source,
    generatedTenth_e7_standard_norm_line_sign] at hc
  have hp := (generatedTenth_e7_four_sign_phase _ _ _ _).mp hc
  unfold generatedTenthE7SignedFlagPhase
  calc
    _ = (c.val (generatedTenthE7StandardOutsideCoordinates i) +
      generatedTenthE7StandardOutsideSigns
        ((generatedTenthE7StandardOutsidePermutation p).symm i)) +
          generatedTenthE7StandardOutsideSigns i := by abel
    _ = (e + generatedTenthE7StandardOutsideSigns i) +
        generatedTenthE7StandardOutsideSigns i := by rw [hp]
    _ = e := by rw [add_assoc, ZModModule.add_self, add_zero]

/-- Whole unsigned-line fixation forces precisely the complete128 actual correction fiber. -/
theorem generatedTenth_e7_monomial_flag_sign_condition (c : golayCode)
    (p : generatedTenthE7StandardFlagPermutationGroup)
    (he : generatedTenthE7MonomialProjectionFixes c p.val.val)
    (hl : generatedTenthE7MonomialLineFixes c p.val.val) :
    generatedTenthE7StandardTwistedSignCondition (generatedTenthE7SignedFlagPhase p) c := by
  constructor
  · exact generatedTenth_e7_monomial_projection_signs c p.val.val he
  · obtain ⟨e, he⟩ : ∃ e : ZMod 2,
        leechIntegralAction (golayMonomialPair (c, p.val.val))
          generatedTenthE7StandardNormTwelveLine =
            generatedTenthE7IntegerSign e • generatedTenthE7StandardNormTwelveLine := by
      rcases hl with hl | hl
      · exact ⟨0, by simpa [generatedTenthE7IntegerSign] using hl⟩
      · exact ⟨1, by simpa [generatedTenthE7IntegerSign] using hl⟩
    intro i
    have hi := generatedTenth_e7_monomial_flag_line_phase c p e he i
    have h0 := generatedTenth_e7_monomial_flag_line_phase c p e he 0
    change c.val 14 + generatedTenthE7SignedFlagPhase p 0 = e at h0
    exact hi.trans h0.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
