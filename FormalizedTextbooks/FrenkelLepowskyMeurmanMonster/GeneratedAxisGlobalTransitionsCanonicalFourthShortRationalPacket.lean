/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsCanonicalFourthRationalPacket
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOdd

/-! Complete finite rational short coordinates of the genuine original Fourth axis. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The exact final original pair coordinates, including the actual middle pair flag. -/
def generatedAxisGlobalCanonicalFourthPairShortQ (s : Fin 2) (p : Fin 276) : ℚ :=
  let M := generatedAxisGlobalCanonicalFourthMiddleMatrixQ
    (griessCoordinatePair p).1 (griessCoordinatePair p).2
  let z : ℚ := if griessCoordinatePair p = (8, 11) then 1 / 2 else 0
  if s = 0 then M + z else z - M

/-- Every actual original final preferred pair coordinate has its exact rational coefficient. -/
theorem generatedAxisGlobalCanonicalFourthPairShortQ_actual (s : Fin 2) (p : Fin 276) :
    (generatedAxisGlobalCanonicalFourthPairShortQ s p : ℝ) =
      (griessConwayEncode generatedFourthAxis).2.1 (Sum.inl (s, p)) := by
  fin_cases s
  · change (generatedAxisGlobalCanonicalFourthPairShortQ 0 p : ℝ) =
      (griessConwayEncode generatedFourthAxis).2.1 (Sum.inl (0, p))
    rw [generatedFourthAxis_local_expression, generatedFourthQShortBasis_triality_pair_minus,
      generatedAxisGlobalCanonicalFourthMiddleMatrix_entry, generatedFourth_local_short,
      generatedFourth_transported_pair_coordinate, generatedFourth_transported_pair_coordinate,
      generatedFourth_pair_phase_zero, qSign_zero]
    by_cases h : griessCoordinatePair p = (8, 11) <;>
      simp [generatedAxisGlobalCanonicalFourthPairShortQ, h]
  · change (generatedAxisGlobalCanonicalFourthPairShortQ 1 p : ℝ) =
      (griessConwayEncode generatedFourthAxis).2.1 (Sum.inl (1, p))
    rw [generatedFourthAxis_local_expression, generatedFourthQShortBasis_triality_pair_plus,
      generatedAxisGlobalCanonicalFourthMiddleMatrix_entry, generatedFourth_local_short,
      generatedFourth_transported_pair_coordinate, generatedFourth_transported_pair_coordinate,
      generatedFourth_pair_phase_zero, qSign_zero]
    by_cases h : griessCoordinatePair p = (8, 11) <;>
      simp [generatedAxisGlobalCanonicalFourthPairShortQ, h]

/-- All preferred short coordinates in bounded original pair and 63-row octad formulas. -/
def generatedAxisGlobalCanonicalFourthFastShortQ : GriessShortIndex → ℚ
  | Sum.inl (s, p) => generatedAxisGlobalCanonicalFourthPairShortQ s p
  | Sum.inr (Sum.inl (o, e)) =>
      (generatedFourthQShortBasisOctadNumerator (golayOctadLabel o) e : ℚ) / 8
  | Sum.inr (Sum.inr _) => 0

/-- The complete finite short expression equals every actual original Fourth coefficient. -/
theorem generatedAxisGlobalCanonicalFourthFastShortQ_actual (r : GriessShortIndex) :
    (generatedAxisGlobalCanonicalFourthFastShortQ r : ℝ) =
      (griessConwayEncode generatedFourthAxis).2.1 r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact generatedAxisGlobalCanonicalFourthPairShortQ_actual s p
  · simp only [generatedAxisGlobalCanonicalFourthFastShortQ, Rat.cast_div,
      Rat.cast_intCast, Rat.cast_ofNat]
    exact (generatedFourthQShortBasis_octad_coordinate o e).symm
  · simp only [generatedAxisGlobalCanonicalFourthFastShortQ, Rat.cast_zero]
    exact (generatedFourthQShortBasis_odd_zero d i).symm

/-- The full canonical target packet with bounded original preferred-coordinate evaluation. -/
def generatedAxisGlobalCanonicalFourthFastRationalPacket : GeneratedAxisGlobalRationalPacket :=
  (generatedAxisGlobalCanonicalFourthMatrixQ,
    (generatedAxisGlobalCanonicalFourthFastShortQ,
      fun t i => (generatedAxisGlobalCanonicalFourthTensorInteger (generatedAxisGlobalSpinLabel t) i : ℚ)))

/-- Every bounded packet coordinate is the full genuine original target coordinate. -/
theorem generatedAxisGlobalCanonicalFourthFastRationalPacket_actual :
    griessConwayEncode generatedFourthAxis =
      generatedAxisGlobalRationalPacketReal generatedAxisGlobalCanonicalFourthFastRationalPacket := by
  apply Prod.ext
  · funext i j
    exact (generatedAxisGlobalCanonicalFourthMatrixQ_actual i j).symm
  · apply Prod.ext
    · funext r
      exact (generatedAxisGlobalCanonicalFourthFastShortQ_actual r).symm
    · rw [generatedAxisGlobalCanonicalFourthTensorInteger_eq]
      funext t i
      simp only [generatedAxisGlobalRationalPacketReal,
        generatedAxisGlobalCanonicalFourthFastRationalPacket, Rat.cast_intCast]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
