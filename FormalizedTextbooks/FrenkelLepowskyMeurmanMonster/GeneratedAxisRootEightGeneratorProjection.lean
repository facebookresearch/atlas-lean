/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightGeneratorCandidates

/-! Genuine Conway projections of all twelve original corrected local candidates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- The ten genuine Mathieu permutations, the concrete flag mover, and the concrete mate. -/
def generatedRootEightGeneratorSpatial (j : Fin 12) : leechIsomSubgroup :=
  if h : j.val < 10 then
    golayPermutationIsometry (leechNormSixHS100MathieuOriginalGenerator ⟨j.val, h⟩)
  else if j.val = 10 then leechNormSixHS100PointMover else leechNormSixHS100MateOrientation

private theorem source_sign_code (d : Fin 4096) :
    sourceGeneratedSignCode d = golayCodeLabelEquiv d := by
  apply Subtype.ext
  exact (golayCodeLabelEquiv_val d).symm

private theorem fiber_sign_projection (d : Fin 4096) :
    projH (localFiberIntoH (generatedFifthSignFiber d 0)) =
      QuotientGroup.mk' signsSubgroup (golaySignIsometry (golayCodeLabelEquiv d)) := by
  rw [generatedFifth_sign_fiber_local, generatedFifth_sign_local_projection, source_sign_code]
  rfl

private theorem permutation_fiber_projection (w : List (Fin 4)) :
    projH (localFiberIntoH (generatedRootEightPermutationWordFiber w)) =
      QuotientGroup.mk' signsSubgroup (golayPermutationIsometry (golayGeneratingWord w)) :=
  generatedRootEight_permutation_word_local_projection w

private theorem mover_sign_code (d : Fin 4096) :
    golayCodeLabelEquiv d = leechNormSixHS100PointMoverSign d := by
  apply Subtype.ext
  exact golayCodeLabelEquiv_val d

/-- The whole original point-moving fiber projects to the literal genuine Conway mover. -/
theorem generatedRootEight_point_mover_fiber_projection :
    projH (localFiberIntoH generatedRootEightPointMoverFiber) =
      QuotientGroup.mk' signsSubgroup leechNormSixHS100PointMover := by
  rw [leechNormSixHS100PointMover_literal_word]
  simp only [generatedRootEightPointMoverFiber, map_mul,
    permutation_fiber_projection, fiber_sign_projection, mover_sign_code]
  rfl

/-- The whole original orientation fiber projects to the literal genuine Conway mate word. -/
theorem generatedRootEight_mate_fiber_projection :
    projH (localFiberIntoH generatedRootEightMateFiber) =
      QuotientGroup.mk' signsSubgroup leechNormSixHS100MateOrientation := by
  simp only [generatedRootEightMateFiber, map_mul,
    permutation_fiber_projection, fiber_sign_projection,
    leechNormSixHS100MateOrientation, leechRootNegationCode,
    leechNormSixHS100MatePermutation]

/-- All twelve complete primitive source words have the prescribed actual spatial projections. -/
theorem generatedRootEight_generator_primitive_projection (j : Fin 12) :
    projH (generatedRootEightGeneratorPrimitiveLocal j) =
      QuotientGroup.mk' signsSubgroup (generatedRootEightGeneratorSpatial j) := by
  unfold generatedRootEightGeneratorPrimitiveLocal generatedRootEightGeneratorPrimitiveFiber
    generatedRootEightGeneratorSpatial
  split_ifs with h h10
  · exact generatedRootEight_permutation_word_local_projection _
  · exact generatedRootEight_point_mover_fiber_projection
  · exact generatedRootEight_mate_fiber_projection

/-- Explicit correction by actual Q elements changes no original Conway projection. -/
theorem generatedRootEight_generator_canonical_projection (j : Fin 12) :
    projH (generatedRootEightGeneratorCanonicalLocal j) =
      QuotientGroup.mk' signsSubgroup (generatedRootEightGeneratorSpatial j) := by
  rw [generatedRootEightGeneratorCanonicalLocal, map_mul, projH_inclQ, one_mul,
    generatedRootEight_generator_primitive_projection]

/-- Conjugation to the original flag coordinates followed by the genuine Conway quotient. -/
def generatedRootEightCanonicalQuotientConjugation : leechIsomSubgroup →* Co1 where
  toFun g := (projH generatedFifthRootEightCanonicalLocal)⁻¹ *
    QuotientGroup.mk' signsSubgroup g * projH generatedFifthRootEightCanonicalLocal
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul]
    group

/-- The quotient homomorphism is the literal original Conway conjugation of the canonical word. -/
theorem generatedRootEight_canonical_quotient_conjugation (g : leechIsomSubgroup) :
    generatedRootEightCanonicalQuotientConjugation g =
      QuotientGroup.mk' signsSubgroup
        (generatedFifthRootEightCanonicalTransport⁻¹ * g * generatedFifthRootEightCanonicalTransport) := by
  simp only [generatedRootEightCanonicalQuotientConjugation,
    generatedFifthRootEight_canonical_local_projection, map_mul, map_inv]
  rfl

/-- Every complete original corrected candidate has its actual conjugated Conway projection. -/
theorem generatedRootEight_generator_candidate_projection (j : Fin 12) :
    projH (generatedRootEightGeneratorCandidate j) =
      generatedRootEightCanonicalQuotientConjugation (generatedRootEightGeneratorSpatial j) := by
  simp only [generatedRootEightGeneratorCandidate, map_mul, map_inv,
    generatedRootEight_generator_canonical_projection,
    generatedRootEightCanonicalQuotientConjugation]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
