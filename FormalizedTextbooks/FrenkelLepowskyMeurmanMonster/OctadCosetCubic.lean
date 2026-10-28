/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual octad cubic is a character on the common-tetrad affine coset. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadCosetCharacter
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadTripleQuadratic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The three actual sign labels in the canonical triple sign space. -/
noncomputable def octadTripleSignLabel (e f g : Fin 64) : OctadTripleSignSpace :=
  ![octadSignLabelEquiv e, octadSignLabelEquiv f, octadSignLabelEquiv g]

/-- Actual physical sums agree with the three preferred-Q negative patterns. -/
theorem octadTriplePhysicalSum_label (o p u : Fin 759) (e f g : Fin 64) :
    octadTriplePhysicalSum o p u (octadTripleSignLabel e f g) =
      integerParity (griessOctadNegativeInteger o e) +
      integerParity (griessOctadNegativeInteger p f) +
      integerParity (griessOctadNegativeInteger u g) := by
  change octadPhysicalSignMap o (octadSignLabelEquiv e) +
    octadPhysicalSignMap p (octadSignLabelEquiv f) +
    octadPhysicalSignMap u (octadSignLabelEquiv g) = _
  rw [octadPhysicalSignMap_label, octadPhysicalSignMap_label, octadPhysicalSignMap_label]

/-- The actual preferred-Q cubic is exactly the affine-coset intersection character,
times the source codeword character independent of all three sign labels. -/
theorem griessForm_octad_cubic_four_coset (o p u : Fin 759) (e f g : Fin 64)
    (hfour : (golayOctadIntersection o p).card = 4)
    (hu : golayOctadWord u = golayOctadWord o + golayOctadWord p) :
    griessForm (griessProd (trialityOctadBasis o e) (trialityOctadBasis p f))
      (trialityOctadBasis u g) =
        qSign (spinDot (sourceWordTheta (golayOctadLabel p))
          (golayLabelCoefficients (golayOctadLabel o))) *
        if octadTripleCosetShift o p + octadTripleSignLabel e f g ∈
            octadTripleSyndromeKernel o p u then
          qSign (octadTripleForm (octadTripleCosetShift o p) (octadTripleSignLabel e f g))
        else 0 := by
  rw [griessForm_octad_cubic_four_syndrome o p u e f g hfour hu]
  simp only [octadTripleCosetShift_mem_iff o p u _ hfour,
    octadTriplePhysicalSum_label]
  rw [octadTripleCosetShift_cross_character o p _ hfour]
  change (if _ then qSign (_ + ∑ i,
    integerParity (griessOctadNegativeInteger p f) i * golayOctadWord o i) else 0) = _
  simp only [octadTripleSignLabel, Matrix.cons_val_one, Matrix.cons_val_zero,
    octadPhysicalSignMap_label,
    qSign_add, mul_ite, mul_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
