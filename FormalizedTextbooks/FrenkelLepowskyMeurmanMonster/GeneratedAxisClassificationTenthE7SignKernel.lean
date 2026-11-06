/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7SignRestriction

/-! Exact positive and unsigned Golay-sign kernels on the transported outside line. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The six nonzero coordinates of the actual distinguished norm-twelve vector. -/
def generatedTenthE7LineSupport : Finset (Fin 24) := {4, 7, 8, 11, 18, 20}

/-- Every certified restriction coordinate lies on the octad or the outside line. -/
theorem generatedTenth_e7_restriction_support (i : Fin 14) :
    generatedTenthE7RestrictionCoordinates i ∈ generatedTenthE7OctadSupport ∨
      generatedTenthE7RestrictionCoordinates i ∈ generatedTenthE7LineSupport := by
  revert i
  decide +kernel

/-- The actual octad and the actual outside line have disjoint supports. -/
theorem generatedTenth_e7_line_disjoint (i : Fin 24)
    (hi : i ∈ generatedTenthE7LineSupport) : i ∉ generatedTenthE7OctadSupport := by
  have h : ∀ j : Fin 24, j ∈ generatedTenthE7LineSupport →
      j ∉ generatedTenthE7OctadSupport := by decide +kernel
  exact h i hi

/-- Zero signs on E8 and on the positive outside vector force the entire original codeword to zero. -/
theorem generatedTenth_e7_positive_sign_code_zero (c : golayCode)
    (ho : ∀ i ∈ generatedTenthE7OctadSupport, c.val i = 0)
    (hs : ∀ i ∈ generatedTenthE7LineSupport, c.val i = 0) : c = 0 := by
  apply generatedTenth_e7_code_zero_of_restriction
  intro i
  rcases generatedTenth_e7_restriction_support i with hi | hi
  · exact ho _ hi
  · exact hs _ hi

/-- A constant sign on the outside line determines the whole original codeword:
it is exactly the corresponding multiple of the complement-octad word. -/
theorem generatedTenth_e7_constant_sign_code (c : golayCode) (t : ZMod 2)
    (ho : ∀ i ∈ generatedTenthE7OctadSupport, c.val i = 0)
    (hs : ∀ i ∈ generatedTenthE7LineSupport, c.val i = t) :
    c = t • generatedTenthE7ComplementCode := by
  have hz : c - t • generatedTenthE7ComplementCode = 0 := by
    apply generatedTenth_e7_positive_sign_code_zero
    · intro i hi
      change c.val i - t * generatedTenthE7ComplementCode.val i = 0
      rw [ho i hi, generatedTenth_e7_complement_coordinates, ite_eq_left hi]
      simp
    · intro i hi
      change c.val i - t * generatedTenthE7ComplementCode.val i = 0
      rw [hs i hi, generatedTenth_e7_complement_coordinates,
        ite_eq_right (generatedTenth_e7_line_disjoint i hi)]
      simp
  exact sub_eq_zero.mp hz

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
