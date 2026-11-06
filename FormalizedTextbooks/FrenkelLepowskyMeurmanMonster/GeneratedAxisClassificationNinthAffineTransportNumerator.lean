/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthAffineTransportData

/-! Original physical and integral coordinate certificates for the literal Ninth affine
section transport. Every numerator is derived from the original Xi, code sign and permutations. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- Both finite coordinate arrays are exactly the original nine-letter Golay word. -/
theorem generatedNinth_affine_octad_permutation_coordinates : ∀ j : Fin 24,
    generatedNinthAffineOctadPermutation.val j = generatedNinthAffineOctadForward j ∧
    generatedNinthAffineOctadPermutation.val.symm j = generatedNinthAffineOctadInverse j := by
  decide +kernel

/-- The original permutation word genuinely carries the two specified Golay encoder words. -/
theorem generatedNinth_affine_octad_word :
    golayPermute generatedNinthAffineOctadPermutation.val
      (golayEncoder (golayLabelCoefficients 2396)) =
        golayEncoder (golayLabelCoefficients 2052) := by
  decide +kernel

/-- Twice the physical column matrix of the genuine complete transport word. -/
def generatedNinthAffineTransportNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
  fun i j =>
    co1XiNumerator (generatedNinthSectionPermutationForward j)
      (generatedNinthAffineOctadInverse i) *
        (if generatedNinthSectionSign.val j = 0 then 1 else -1)

set_option maxHeartbeats 12000000 in
-- Check the576 original integral basis-action equations rather than an independent binary table.
/-- The original physical numerator acts on the actual Leech basis by twice the displayed matrix. -/
theorem generatedNinth_affine_transport_integral_certificate :
    generatedNinthAffineTransportNumerator * leechBasisMatrix =
      (2 : ℤ) • (leechBasisMatrix * generatedNinthAffineTransportBasisMatrix) := by
  decide +kernel

set_option maxHeartbeats 12000000 in
-- Bind576 actual binary bits through the original integral basis action and change of basis.
/-- Packed binary columns agree with the original integral-to-hyperbolic coordinate change. -/
theorem generatedNinth_affine_transport_binary_certificate :
    sixthFrameOrbitColumnMatrix generatedNinthAffineTransportBinaryColumns =
      leechHyperbolicInverse *
        generatedNinthAffineTransportBasisMatrix.map (Int.castRingHom (ZMod 2)) *
          leechHyperbolicMatrix := by
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
