/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignKernel

/-! Actual positive and unsigned line fixation by genuine Golay-sign Leech isometries. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every coordinate on the displayed line support is genuinely nonzero. -/
theorem generatedTenth_e7_line_nonzero (i : Fin 24)
    (hi : i ∈ generatedTenthE7LineSupport) : generatedTenthE7DistinguishedVector i ≠ 0 := by
  have h : ∀ j : Fin 24, j ∈ generatedTenthE7LineSupport →
      generatedTenthE7DistinguishedVector j ≠ 0 := by decide +kernel
  exact h i hi

/-- Among actual Golay signs fixing E8 pointwise, the positive line vector has trivial kernel. -/
theorem generatedTenth_e7_sign_positive_iff (c : golayCode)
    (ho : ∀ i ∈ generatedTenthE7OctadSupport, c.val i = 0) :
    leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine =
      generatedTenthE7NormTwelveLine ↔ c = 0 := by
  constructor
  · intro h
    apply generatedTenth_e7_positive_sign_code_zero c ho
    intro i hi
    have hh := congrArg (fun u : leechIntegral => u.val i) h
    change (leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine).val i =
      generatedTenthE7DistinguishedVector i at hh
    rw [leechIntegralAction_golaySign] at hh
    change (if c.val i = 0 then generatedTenthE7DistinguishedVector i
      else -generatedTenthE7DistinguishedVector i) = generatedTenthE7DistinguishedVector i at hh
    by_contra hn
    rw [ite_eq_right hn] at hh
    have hnonzero := generatedTenth_e7_line_nonzero i hi
    omega
  · rintro rfl
    apply Subtype.ext
    rw [leechIntegralAction_golaySign]
    ext i
    simp [golayIntegerSign]

/-- Among those genuine signs, reversal of the line vector is exactly the complement-octad sign. -/
theorem generatedTenth_e7_sign_negative_iff (c : golayCode)
    (ho : ∀ i ∈ generatedTenthE7OctadSupport, c.val i = 0) :
    leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine =
      -generatedTenthE7NormTwelveLine ↔ c = generatedTenthE7ComplementCode := by
  constructor
  · intro h
    have hc : c = (1 : ZMod 2) • generatedTenthE7ComplementCode := by
      apply generatedTenth_e7_constant_sign_code c 1 ho
      intro i hi
      have hh := congrArg (fun u : leechIntegral => u.val i) h
      change (leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine).val i =
        -generatedTenthE7DistinguishedVector i at hh
      rw [leechIntegralAction_golaySign] at hh
      change (if c.val i = 0 then generatedTenthE7DistinguishedVector i
        else -generatedTenthE7DistinguishedVector i) = -generatedTenthE7DistinguishedVector i at hh
      have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
      rcases hcases (c.val i) with hz | hz
      · rw [ite_eq_left hz] at hh
        have hnonzero := generatedTenth_e7_line_nonzero i hi
        omega
      · exact hz
    simpa only [one_smul] using hc
  · rintro rfl
    exact generatedTenth_e7_complement_negates_norm_twelve

/-- The entire unsigned-line kernel in the genuine Golay-sign subgroup consists of exactly
zero and the complement-octad codeword. -/
theorem generatedTenth_e7_sign_unsigned_iff (c : golayCode)
    (ho : ∀ i ∈ generatedTenthE7OctadSupport, c.val i = 0) :
    (leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine =
      generatedTenthE7NormTwelveLine ∨
    leechIntegralAction (golaySignIsometry c) generatedTenthE7NormTwelveLine =
      -generatedTenthE7NormTwelveLine) ↔
      c = 0 ∨ c = generatedTenthE7ComplementCode := by
  rw [generatedTenth_e7_sign_positive_iff c ho, generatedTenth_e7_sign_negative_iff c ho]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
