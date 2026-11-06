/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadQComparison
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Pairing
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector

/-! Unit short coefficients and idempotency for the original triality octad axes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Every nonzero short coordinate of the actual octad transition is a unit sign. -/
theorem generatedAxis_triality_octad_supported_square
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (r : GriessShortIndex)
    (hr : generatedOctadShortSupport o r) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1 r ^ 2 = 1 := by
  rcases r with ⟨s, p⟩ | (⟨q, f⟩ | ⟨d, i⟩)
  · change generatedOctadPairSupport o p at hr
    have hi := generatedAxis_octad_axial_diagonal o e (griessCoordinatePair p).1
    have hj := generatedAxis_octad_axial_diagonal o e (griessCoordinatePair p).2
    simp only [hr.1, ↓reduceIte] at hi
    simp only [hr.2, ↓reduceIte] at hj
    rw [generatedAxis_triality_octad_pair_coordinate, mul_pow]
    have hv : (2 * griessShortVector (Sum.inr (Sum.inl (o, e)))
        (griessCoordinatePair p).1 * griessShortVector (Sum.inr (Sum.inl (o, e)))
        (griessCoordinatePair p).2) ^ 2 = 1 := by
      calc
        _ = (2 * griessShortVector (Sum.inr (Sum.inl (o, e)))
            (griessCoordinatePair p).1 * griessShortVector (Sum.inr (Sum.inl (o, e)))
            (griessCoordinatePair p).1) *
          (2 * griessShortVector (Sum.inr (Sum.inl (o, e)))
            (griessCoordinatePair p).2 * griessShortVector (Sum.inr (Sum.inl (o, e)))
            (griessCoordinatePair p).2) := by ring
        _ = 1 := by rw [hi, hj, one_mul]
    rw [hv, mul_one]
    split_ifs <;> norm_num
  · change q = o at hr
    subst q
    exact generatedAxis_triality_octad_same_coordinate_square o e f c
  · exact False.elim hr

/-- Coordinates outside the actual support vanish, rather than merely being bounded. -/
theorem generatedAxis_triality_octad_unsupported_zero
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (r : GriessShortIndex)
    (hr : ¬ generatedOctadShortSupport o r) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1 r = 0 :=
  not_ne_iff.mp (mt (generatedAxis_triality_octad_support_iff o e c r).mp hr)

/-- Triality preserves the genuine scaled-idempotent equation of every short axis. -/
theorem generatedAxis_triality_short_square (r : GriessShortIndex) (c : ZMod 2) :
    griessProd (sExtra (conwayShortAxis r c)) (sExtra (conwayShortAxis r c)) =
      (64 : ℝ) • sExtra (conwayShortAxis r c) := by
  rw [← sExtra_preserves_griessProd, conwayShortAxis_square, map_smul]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
