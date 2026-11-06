/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadCoordinates

/-! Exact short-coordinate support of an actual octad transition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The two pair coordinates lie inside this actual octad. -/
def generatedOctadPairSupport (o : Fin 759) (p : Fin 276) : Prop :=
  (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).1.val = true ∧
    (golayEncodedMask (golayOctadLabel o).val).testBit (griessCoordinatePair p).2.val = true

/-- Pair lines within the octad together with its own 64 signed-octad lines. -/
def generatedOctadShortSupport (o : Fin 759) : GriessShortIndex → Prop
  | Sum.inl (_, p) => generatedOctadPairSupport o p
  | Sum.inr (Sum.inl (p, _)) => p = o
  | Sum.inr (Sum.inr _) => False

/-- A short octad vector is nonzero at exactly its eight physical coordinates. -/
theorem generatedAxis_octad_coordinate_ne_zero (o : Fin 759) (e : Fin 64) (i : Fin 24) :
    griessShortVector (Sum.inr (Sum.inl (o, e))) i ≠ 0 ↔
      (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true := by
  by_cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = true
  · simp only [griessShortVector, griessShortIntegral, hb, ite_true, div_ne_zero_iff,
      iff_true]
    split_ifs <;> norm_num
  · simp [griessShortVector, griessShortIntegral, hb]

/-- Both pair signs have a nonzero coefficient exactly for the 28 pairs
whose coordinates lie in the chosen actual octad. -/
theorem generatedAxis_triality_octad_pair_ne_zero
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1
      (Sum.inl (s, p)) ≠ 0 ↔ generatedOctadPairSupport o p := by
  rw [generatedAxis_triality_octad_pair_coordinate]
  have hsign : (if s = 0 then 1 else -1 : ℝ) ≠ 0 := by split_ifs <;> norm_num
  simp only [mul_ne_zero_iff, hsign, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    true_and, generatedAxis_octad_coordinate_ne_zero, generatedOctadPairSupport]

/-- All 120 nonzero short coefficients are precisely the actual octad's
pair lines and signed-octad lines; no odd coordinates occur. -/
theorem generatedAxis_triality_octad_support_iff
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (r : GriessShortIndex) :
    (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).2.1 r ≠ 0 ↔
      generatedOctadShortSupport o r := by
  rcases r with ⟨s, p⟩ | (⟨p, f⟩ | ⟨d, i⟩)
  · exact generatedAxis_triality_octad_pair_ne_zero o e c s p
  · change _ ↔ p = o
    by_cases hp : p = o
    · subst p
      have hs := generatedAxis_triality_octad_same_coordinate_square o e f c
      constructor
      · intro _; rfl
      · intro _ hz
        rw [hz] at hs
        norm_num at hs
    · rw [generatedAxis_triality_octad_other_coordinate o p e f c hp]
      simp only [ne_self_iff_false, hp]
  · rw [generatedAxis_triality_octad_odd_coordinate]
    simp only [ne_self_iff_false, generatedOctadShortSupport]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
