/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The preferred octad product phase is the common-tetrad Fourier character. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCosetShift

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Multiplication by the own octad word fixes a supported sign coordinate. -/
theorem octadPhysicalSignMap_word_mul (o : Fin 759) (x : OctadSignSpace) (i : Fin 24) :
    golayOctadWord o i * octadPhysicalSignMap o x i = octadPhysicalSignMap o x i := by
  by_cases hi : i ∈ golayOctadSupport o
  · simp only [golayOctadWord_indicator, hi, ite_true, one_mul]
  · rw [octadPhysicalSignMap_supported o x i hi, mul_zero]

/-- The middle sign coordinate retains its own binary intersection form. -/
theorem octadTripleForm_middle (a : OctadSignSpace) (w : OctadTripleSignSpace) :
    octadTripleForm (Pi.single 1 a) w = octadSignForm a (w 1) := by
  change (∑ s : Fin 3, octadSignForm ((Pi.single 1 a : OctadTripleSignSpace) s) (w s)) = _
  rw [Fin.sum_univ_three]
  simp

/-- The actual triple intersection form is alternating. -/
theorem octadTripleForm_alternating (w : OctadTripleSignSpace) :
    octadTripleForm w w = 0 := by
  change (∑ s, octadSignForm (w s) (w s)) = 0
  simp only [octadSignForm_alternating, Finset.sum_const_zero]

/-- The affine shift pairs with the middle sign vector by common-tetrad parity. -/
theorem octadTripleCosetShift_pairing (o p : Fin 759) (w : OctadTripleSignSpace)
    (hfour : (golayOctadIntersection o p).card = 4) :
    octadTripleForm (octadTripleCosetShift o p) w =
      ∑ i, octadIntersectionPattern o p i * octadPhysicalSignMap p (w 1) i := by
  rw [octadTripleCosetShift, octadTripleForm_middle, ← octadPhysicalSignMap_pairing,
    octadPhysicalSignMap_normalize p _ (octadIntersectionPattern_supported o p)
      (octadIntersectionPattern_even o p hfour)]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc,
    octadPhysicalSignMap_word_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, octadPhysicalSignMap_even, mul_zero, add_zero]

/-- The common-tetrad character is the actual cross-product sign parity. -/
theorem octadTripleCosetShift_cross_character (o p : Fin 759) (w : OctadTripleSignSpace)
    (hfour : (golayOctadIntersection o p).card = 4) :
    octadTripleForm (octadTripleCosetShift o p) w =
      ∑ i, octadPhysicalSignMap p (w 1) i * golayOctadWord o i := by
  rw [octadTripleCosetShift_pairing o p w hfour]
  simp only [octadIntersectionPattern, mul_assoc, octadPhysicalSignMap_word_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
