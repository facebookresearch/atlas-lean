/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFifthQStageActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalReductionFifthGenerators
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthShortInputs

/-! Binary matching of the inverse Odd root-three comparison word with Fifth root thirteen.

The inverse of the first complete Odd-to-Fifth comparison word is a Fifth-family transition
representative. Its actual binary root is read off from the kernel-checked comparison Q images,
and an explicit product of three genuine full Fifth-axis fixers carries the binary root of the
Fifth forest root thirteen to it. No central sign is computed here. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The inverse first comparison word: a Fifth coset landing back in the Odd family. -/
def generatedAxisGlobalTwelveFifthBindRoot13Coset : H :=
  (generatedAxisGlobalOddFifthComparisonLocal 0)⁻¹

/-- The exact binary root of that Fifth coset. -/
theorem generatedAxisGlobalTwelveFifthBindRoot13Coset_root :
    (generatedAxisGlobalBinaryRoot generatedAxisGlobalTwelveFifthBindRoot13Coset).val =
      monsterCo1GeometryBinaryMaskDecode 2994176 := by
  change co1BinaryAction (projH generatedAxisGlobalTwelveFifthBindRoot13Coset⁻¹)
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [generatedAxisGlobalTwelveFifthBindRoot13Coset, inv_inv]
  change leechBinaryAction (generatedAxisGlobalOddFifthComparisonFiber 0).val.2
    (toAdd (qQuotHom sourceOmegaQ)) = _
  rw [← (generatedAxisGlobalOddFifthComparisonFiber 0).property]
  have hΩ : toAdd (qQuotHom sourceOmegaQ) = toAdd (qQuotHom (qCoordinateGenerator 11)) := by
    funext i
    revert i
    decide +kernel
  rw [hΩ]
  change qBinaryAction (spinConjugation (generatedAxisGlobalOddFifthComparisonFiber 0).val.1)
    (toAdd (qQuotHom (qCoordinateGenerator 11))) = _
  rw [qBinaryAction_apply, generatedAxisGlobalOddFifthQImage_actual,
    generatedAxisGlobalOddFifthQStageFinal_actual]
  rfl

/-- Three genuine full Fifth-axis fixers: apply generator 4, then 12, then 18. -/
def generatedAxisGlobalTwelveFifthBindRoot13Transport : generatedFifthLocalAxisStabilizer :=
  generatedAxisGlobalFifthGenerator 18 * generatedAxisGlobalFifthGenerator 12 *
    generatedAxisGlobalFifthGenerator 4

set_option maxHeartbeats 10000000 in
-- Three actual binary matrix actions, checked on the complete 24-coordinate point.
/-- The three-letter fixer word carries the binary root of Fifth root thirteen to that coset. -/
theorem generatedAxisGlobalTwelveFifthBindRoot13Transport_actual :
    generatedAxisGlobalBinaryAct generatedAxisGlobalTwelveFifthBindRoot13Transport.val
      (generatedAxisGlobalBinaryRoot (generatedAxisGlobalFifthShortLocalWord 13)) =
        generatedAxisGlobalBinaryRoot generatedAxisGlobalTwelveFifthBindRoot13Coset := by
  rw [generatedAxisGlobalFifthShortLocalWord_root]
  apply Subtype.ext
  rw [generatedAxisGlobalTwelveFifthBindRoot13Coset_root]
  change (generatedAxisGlobalBinaryAct
    ((generatedAxisGlobalFifthGenerator 18).val * (generatedAxisGlobalFifthGenerator 12).val *
      (generatedAxisGlobalFifthGenerator 4).val) (generatedAxisGlobalFifthRoot 13)).val = _
  simp only [generatedAxisGlobalBinaryAct_mul]
  simp_rw [generatedAxisGlobalFifthGenerator_binary]
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
