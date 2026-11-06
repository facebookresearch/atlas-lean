/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthXiTensorUnits

/-! Literal extraspecial corrections of the six original spatial monomial fibers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Actual translation labels of the six phase corrections. -/
def generatedFifthMonomialPermutationTranslation : Fin 6 → Fin 4096 :=
  ![9, 704, 801, 821, 1021, 917]

/-- Actual modulation labels of the same corrections. -/
def generatedFifthMonomialPermutationModulation : Fin 6 → Fin 4096 :=
  ![526, 13, 1162, 266, 1411, 647]

/-- Each correction is an actual Q element with central coordinate zero. -/
def generatedFifthMonomialPermutationCorrection (k : Fin 6) : Q :=
  generatedAxisFourthQFromSpin
    (golayLabelCoefficients (generatedFifthMonomialPermutationTranslation k))
    (golayLabelCoefficients (generatedFifthMonomialPermutationModulation k)) 0

/-- The actual corrected original fiber; fixation requires separate coordinate proofs. -/
def generatedFifthMonomialPermutationCorrectedFiber (k : Fin 6) : localFiberSubgroup :=
  localFiberIncl (generatedFifthMonomialPermutationCorrection k) *
    generatedFifthMonomialSpatialFiber k

/-- Extraspecial correction preserves the original genuine physical projection. -/
theorem generatedFifth_monomial_permutation_corrected_spatial (k : Fin 6) :
    (generatedFifthMonomialPermutationCorrectedFiber k).val.2 =
      (generatedFifthMonomialSpatialFiber k).val.2 :=
  one_mul _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
