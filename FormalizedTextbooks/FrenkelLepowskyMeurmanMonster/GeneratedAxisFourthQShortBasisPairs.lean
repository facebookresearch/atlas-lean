/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisProjection
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthMatrixCoordinates
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A nonzero literal basis character forces the actual final pair coefficient to vanish. -/
theorem generatedFourthQShortBasis_pair_zero (i : Fin 7) (s : Fin 2) (p : Fin 276)
    (hp : generatedFourthQShortBasisPairPhase i p ≠ 0) :
    (griessConwayEncode generatedFourthAxis).2.1 (Sum.inl (s, p)) = 0 := by
  obtain ⟨hM, hpair⟩ := generatedFourthQShortBasis_pair_zero_certificate i p hp
  have hs : s = 0 ∨ s = 1 := by
    fin_cases s
    · exact Or.inl rfl
    · exact Or.inr rfl
  rw [generatedFourthAxis_local_expression]
  rcases hs with rfl | rfl
  · rw [generatedFourthQShortBasis_triality_pair_minus, generatedFourthQShortBasis_middle_matrix,
      generatedFourth_local_short, generatedFourth_transported_pair_coordinate,
      generatedFourth_transported_pair_coordinate]
    simp [hM, hpair]
  · rw [generatedFourthQShortBasis_triality_pair_plus, generatedFourthQShortBasis_middle_matrix,
      generatedFourth_local_short, generatedFourth_transported_pair_coordinate,
      generatedFourth_transported_pair_coordinate]
    simp [hM, hpair]

/-- All seven genuine affine Q basis elements fix every supported actual pair-short coordinate. -/
theorem generatedFourthQShortBasis_pair_fixed (i : Fin 7) (s : Fin 2) (p : Fin 276)
    (hp : (griessConwayEncode generatedFourthAxis).2.1 (Sum.inl (s, p)) ≠ 0) :
    localAxisQPhase (Sum.inl (s, p)) (generatedFourthQAffineParameterBasis i) = 1 := by
  apply Multiplicative.toAdd.injective
  rw [generatedFourthQShortBasis_pair_character]
  change generatedFourthQShortBasisPairPhase i p = 0
  by_contra h
  exact hp (generatedFourthQShortBasis_pair_zero i s p h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
