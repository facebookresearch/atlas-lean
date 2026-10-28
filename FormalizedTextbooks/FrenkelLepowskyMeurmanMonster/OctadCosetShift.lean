/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual common tetrad provides the affine shift in the octad cubic. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadPhysicalSignSpace

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual octad word is the binary indicator of its support. -/
theorem golayOctadWord_indicator (o : Fin 759) (i : Fin 24) :
    golayOctadWord o i = if i ∈ golayOctadSupport o then 1 else 0 := by
  simp only [golayOctadWord, golayLabelEncoder_boolean, golayOctadSupport,
    golayMaskSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  cases (golayEncodedMask (golayOctadLabel o).val).testBit i.val <;> rfl

/-- Binary characteristic vector of the physical common tetrad. -/
def octadIntersectionPattern (o p : Fin 759) (i : Fin 24) : ZMod 2 :=
  golayOctadWord o i * golayOctadWord p i

/-- The intersection pattern is supported on either parent octad. -/
theorem octadIntersectionPattern_supported (o p : Fin 759) (i : Fin 24)
    (hi : i ∉ golayOctadSupport p) : octadIntersectionPattern o p i = 0 := by
  simp [octadIntersectionPattern, golayOctadWord_supported p i hi]

/-- A four-coordinate intersection is an even binary pattern. -/
theorem octadIntersectionPattern_even (o p : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    (∑ i, octadIntersectionPattern o p i) = 0 := by
  have hi (i : Fin 24) : octadIntersectionPattern o p i =
      if i ∈ golayOctadIntersection o p then 1 else 0 := by
    simp only [octadIntersectionPattern, golayOctadWord_indicator,
      golayOctadIntersection_support, Finset.mem_inter]
    split_ifs <;> simp_all
  simp_rw [hi]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    hfour]
  decide +kernel

/-- Put the normalized common tetrad in the middle octad sign space. -/
def octadTripleCosetShift (o p : Fin 759) : OctadTripleSignSpace :=
  Pi.single 1 (octadPhysicalNormalize p (octadIntersectionPattern o p))

/-- Physical sums retain the middle coordinate of a single sign vector. -/
theorem octadTriplePhysicalSum_middle (o p u : Fin 759) (a : OctadSignSpace) :
    octadTriplePhysicalSum o p u (Pi.single 1 a) = octadPhysicalSignMap p a := by
  change octadPhysicalSignMap o ((Pi.single 1 a : OctadTripleSignSpace) 0) +
    octadPhysicalSignMap p ((Pi.single 1 a : OctadTripleSignSpace) 1) +
    octadPhysicalSignMap u ((Pi.single 1 a : OctadTripleSignSpace) 2) = _
  simp

/-- The chosen sign-space shift has precisely the common-tetrad syndrome. -/
theorem octadTripleCosetShift_syndrome (o p u : Fin 759)
    (hfour : (golayOctadIntersection o p).card = 4) :
    golaySyndrome (octadTriplePhysicalSum o p u (octadTripleCosetShift o p)) =
      golaySyndrome (octadIntersectionPattern o p) := by
  rw [octadTripleCosetShift, octadTriplePhysicalSum_middle,
    octadPhysicalSignMap_normalize p _ (octadIntersectionPattern_supported o p)
      (octadIntersectionPattern_even o p hfour), map_add, map_smul]
  rw [golayOctadWord, golaySyndrome_encoder, smul_zero, add_zero]

/-- The actual syndrome support is the affine coset of the homogeneous kernel. -/
theorem octadTripleCosetShift_mem_iff (o p u : Fin 759) (w : OctadTripleSignSpace)
    (hfour : (golayOctadIntersection o p).card = 4) :
    octadTripleCosetShift o p + w ∈ octadTripleSyndromeKernel o p u ↔
      golaySyndrome (octadTriplePhysicalSum o p u w) =
        golaySyndrome (octadIntersectionPattern o p) := by
  change golaySyndrome (octadTriplePhysicalSum o p u (octadTripleCosetShift o p+w)) = 0 ↔ _
  rw [map_add, map_add, octadTripleCosetShift_syndrome o p u hfour]
  have hzero (a b : SpinIndex) : a+b = 0 ↔ b=a := by
    constructor
    · intro h
      have hz := congrArg (fun z => a+z) h
      simpa only [← add_assoc, ZModModule.add_self, zero_add, add_zero] using hz
    · intro h
      rw [h, ZModModule.add_self]
  exact hzero _ _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
