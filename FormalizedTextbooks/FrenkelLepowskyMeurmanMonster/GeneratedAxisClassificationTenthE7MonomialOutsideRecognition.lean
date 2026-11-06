/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7StandardNormLine
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Co1OrderMonomial

/-! Every genuine signed monomial line fixer preserves the complete actual outside support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The entire actual source vector has its original signed permutation coordinate action. -/
theorem generatedTenth_e7_monomial_standard_line_coordinate (c : golayCode)
    (p : golayAutomorphismSubgroup) (i : Fin 24) :
    (leechIntegralAction (golayMonomialPair (c, p))
      generatedTenthE7StandardNormTwelveLine).val (p.val i) =
      if c.val (p.val i) = 0 then generatedTenthE7XiLine i else -generatedTenthE7XiLine i := by
  unfold golayMonomialPair
  rw [map_mul, LinearEquiv.mul_apply, leechIntegralAction_golaySign,
    leechIntegralAction_golayPermutation, generatedTenth_e7_standard_norm_line_source]
  simp only [golayIntegerSign, golayIntegerPermute, p.val.symm_apply_apply]

/-- Unsigned fixation recognizes every actual outside-support membership in both directions. -/
theorem generatedTenth_e7_monomial_standard_line_support (c : golayCode)
    (p : golayAutomorphismSubgroup)
    (h : leechIntegralAction (golayMonomialPair (c, p))
      generatedTenthE7StandardNormTwelveLine = generatedTenthE7StandardNormTwelveLine ∨
      leechIntegralAction (golayMonomialPair (c, p)) generatedTenthE7StandardNormTwelveLine =
        -generatedTenthE7StandardNormTwelveLine) (i : Fin 24) :
    generatedTenthE7StandardOutside (p.val i) ↔ generatedTenthE7StandardOutside i := by
  have hz : generatedTenthE7XiLine (p.val i) = 0 ↔ generatedTenthE7XiLine i = 0 := by
    rcases h with h | h
    · have hc := congrArg (fun u : leechIntegral => u.val (p.val i)) h
      rw [generatedTenth_e7_monomial_standard_line_coordinate,
        generatedTenth_e7_standard_norm_line_source] at hc
      rw [← hc]
      split_ifs <;> simp
    · have hc := congrArg (fun u : leechIntegral => u.val (p.val i)) h
      rw [generatedTenth_e7_monomial_standard_line_coordinate] at hc
      change (if c.val (p.val i) = 0 then generatedTenthE7XiLine i
        else -generatedTenthE7XiLine i) =
          -generatedTenthE7StandardNormTwelveLine.val (p.val i) at hc
      rw [generatedTenth_e7_standard_norm_line_source] at hc
      have he : -generatedTenthE7XiLine (p.val i) = 0 ↔ generatedTenthE7XiLine i = 0 := by
        rw [← hc]
        split_ifs <;> simp
      simpa only [neg_eq_zero] using he
  rw [← generatedTenth_e7_standard_norm_line_nonzero,
    ← generatedTenth_e7_standard_norm_line_nonzero]
  exact not_congr hz

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
