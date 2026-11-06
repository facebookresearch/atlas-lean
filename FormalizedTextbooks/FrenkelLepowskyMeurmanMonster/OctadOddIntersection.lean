/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Physical intersection facts for actual octad/odd selectors. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddBaseSelector
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPhysicalSignSpace

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Intersecting a source codeword with an octad has no outside support. -/
theorem octadOddIntersection_supported (o : Fin 759) (f : Fin 2048) (k : Fin 24)
    (hk : k ∉ golayOctadSupport o) : octadOddIntersection o f k = 0 := by
  have hz : golayOctadWord o k = 0 := by
    by_contra hn
    exact hk ((golayOctadWord_ne_zero_iff o k).mp hn)
  simp only [octadOddIntersection, hz, zero_mul]

/-- The physical intersection is even by actual Golay self-orthogonality. -/
theorem octadOddIntersection_even (o : Fin 759) (f : Fin 2048) :
    (∑ k, octadOddIntersection o f k) = 0 := by
  have h : spinDot (golaySyndrome (golayEncoder (octadSpinLow f)))
      (golayLabelCoefficients (golayOctadLabel o)) = 0 := by
    rw [golaySyndrome_encoder]
    simp only [spinDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  rw [golaySyndrome_spinDot] at h
  simpa only [octadOddIntersection, golayOctadWord, mul_comm] using h

/-- Normalizing the actual physical intersection gives precisely the
character label of the source codeword restricted to this octad. -/
theorem octadOddIntersection_normalize (o : Fin 759) (f : Fin 2048) :
    octadPhysicalNormalize o (octadOddIntersection o f) =
      octadSignLabelEquiv (octadTensorCharacterLabel o f) := by
  simp only [octadTensorCharacterLabel, Equiv.apply_symm_apply]
  change octadSignNormalize (fun k =>
    octadOddIntersection o f (golayOctadCoordinate o k)) = _
  simp only [octadOddIntersection, golayOctadWord_local, one_mul]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
