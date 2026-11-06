/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7LineIdentification

/-! The genuine complement-octad sign fixes E8 pointwise and reverses
the unsigned norm-twelve line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine codeword supported on the sixteen coordinates complementary to the octad. -/
def generatedTenthE7ComplementCode : golayCode :=
  ⟨(fun _ => 1) - generatedTenthE7OctadWord,
    golayCode.sub_mem ⟨Pi.single 11 1, golay_all_one⟩ generatedTenth_e7_octad_mem_code⟩

/-- The actual original Leech isometry defined by those complementary coordinate signs. -/
def generatedTenthE7ComplementSign : leechIsomSubgroup :=
  golaySignIsometry generatedTenthE7ComplementCode

/-- The complete original binary coordinates are zero on the octad and one elsewhere. -/
theorem generatedTenth_e7_complement_coordinates (i : Fin 24) :
    generatedTenthE7ComplementCode.val i =
      if i ∈ generatedTenthE7OctadSupport then 0 else 1 := by
  change 1 - generatedTenthE7OctadWord i = _
  rw [generatedTenth_e7_octad_coordinates]
  by_cases hi : i ∈ generatedTenthE7OctadSupport <;> simp [hi]

/-- This genuine noncentral sign change fixes the entire actual E8 coordinate section pointwise. -/
theorem generatedTenth_e7_complement_fixes_section (x : Fin 24 → ℝ)
    (hx : x ∈ generatedTenthE8CoordinateSection) :
    generatedTenthE7ComplementSign.val x = x := by
  ext i
  change qSign (generatedTenthE7ComplementCode.val i) * x i = x i
  rw [generatedTenth_e7_complement_coordinates]
  by_cases hi : i ∈ generatedTenthE7OctadSupport
  · simp [hi, qSign]
  · rw [hx i hi]
    simp

/-- It reverses the actual norm-twelve vector, while preserving its unsigned line. -/
theorem generatedTenth_e7_complement_negates_norm_twelve :
    leechIntegralAction generatedTenthE7ComplementSign generatedTenthE7NormTwelveLine =
      -generatedTenthE7NormTwelveLine := by
  change leechIntegralAction (golaySignIsometry generatedTenthE7ComplementCode) _ = _
  apply Subtype.ext
  rw [leechIntegralAction_golaySign]
  ext i
  change (if generatedTenthE7ComplementCode.val i = 0 then
      generatedTenthE7DistinguishedVector i else -generatedTenthE7DistinguishedVector i) =
        -generatedTenthE7DistinguishedVector i
  rw [generatedTenth_e7_complement_coordinates]
  by_cases hi : i ∈ generatedTenthE7OctadSupport
  · have hz : generatedTenthE7DistinguishedVector i = 0 := by
      rw [generatedTenthE7DistinguishedVector, generatedTenth_e7_line_outside i hi, mul_zero]
    simp [hi, hz]
  · simp [hi]

/-- Pointwise E8 fixation together with unsigned-line fixation does not
imply point fixation. -/
theorem generatedTenth_e7_complement_not_positive_point :
    leechIntegralAction generatedTenthE7ComplementSign generatedTenthE7NormTwelveLine ≠
      generatedTenthE7NormTwelveLine := by
  rw [generatedTenth_e7_complement_negates_norm_twelve]
  intro h
  have hh := congrArg (fun u : leechIntegral => u.val 4) h
  norm_num [generatedTenthE7NormTwelveLine, generatedTenthE7DistinguishedVector,
    generatedTenthE7LineDirection] at hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
