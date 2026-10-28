/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Saturation
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneralAxialVector

/-! Actual short vectors fixed by a section projection have pairing four. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- A matrix fixing an actual short vector pairs with it by its proved norm four. -/
theorem generatedAxisE8_pairing_four_of_fixed
    (P : Matrix (Fin 24) (Fin 24) ℝ) (r : GriessShortIndex)
    (h : P *ᵥ griessShortVector r = griessShortVector r) :
    conwayShortPairing P r = 4 := by
  calc
    conwayShortPairing P r =
        ∑ i, griessShortVector r i * (P *ᵥ griessShortVector r) i := by
      unfold conwayShortPairing Matrix.mulVec dotProduct
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, griessShortVector r i * griessShortVector r i := by rw [h]
    _ = 4 := griessShortVector_norm_sq r

/-- Literal support makes the genuine coordinate section projection fix a short vector. -/
theorem generatedAxisE8_coordinate_projection_fixed (o : Fin 759) (r : GriessShortIndex)
    (h : ∀ i : Fin 24, (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false →
      griessShortVector r i = 0) :
    Matrix.diagonal (fun i : Fin 24 =>
      if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then (1 : ℝ) else 0)
      *ᵥ griessShortVector r = griessShortVector r := by
  funext i
  rw [Matrix.mulVec_diagonal]
  cases hb : (golayEncodedMask (golayOctadLabel o).val).testBit i.val with
  | false => simp [h i hb]
  | true => simp

/-- Every actual short vector supported on this octad has pairing four with its axis matrix. -/
theorem generatedAxisE8_coordinate_pairing_four
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (r : GriessShortIndex)
    (h : ∀ i : Fin 24, (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false →
      griessShortVector r i = 0) :
    conwayShortPairing
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 r = 4 := by
  rw [generatedAxis_triality_octad_matrix]
  exact generatedAxisE8_pairing_four_of_fixed _ r
    (generatedAxisE8_coordinate_projection_fixed o r h)

/-- Every label in the actual 120-coordinate support has literal physical octad support. -/
theorem generatedAxisE8_short_support_zero (o : Fin 759) (r : GriessShortIndex)
    (hr : generatedOctadShortSupport o r) (i : Fin 24)
    (hi : (golayEncodedMask (golayOctadLabel o).val).testBit i.val = false) :
    griessShortVector r i = 0 := by
  rcases r with ⟨s, p⟩ | (⟨p, f⟩ | ⟨d, j⟩)
  · change generatedOctadPairSupport o p at hr
    rcases hr with ⟨ha, hb⟩
    have hia : i ≠ (griessCoordinatePair p).1 := by
      intro he
      subst i
      rw [hi] at ha
      contradiction
    have hib : i ≠ (griessCoordinatePair p).2 := by
      intro he
      subst i
      rw [hi] at hb
      contradiction
    simp [griessShortVector, griessShortIntegral, hia, hib]
  · change p = o at hr
    subst p
    by_contra hn
    have hb := (generatedAxis_octad_coordinate_ne_zero o f i).mp hn
    rw [hi] at hb
    contradiction
  · exact False.elim hr

/-- Each of the genuine 120 supported labels has pairing four with the actual axis matrix. -/
theorem generatedAxisE8_supported_pairing_four
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (r : GriessShortIndex)
    (hr : generatedOctadShortSupport o r) :
    conwayShortPairing
      (griessConwayEncode (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))).1 r = 4 :=
  generatedAxisE8_coordinate_pairing_four o e c r (generatedAxisE8_short_support_zero o r hr)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
