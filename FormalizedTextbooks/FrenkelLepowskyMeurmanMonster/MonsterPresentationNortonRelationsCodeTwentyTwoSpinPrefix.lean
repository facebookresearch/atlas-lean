/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The complete actual code-twenty-two monomial prefix before its forward Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsCodeTwentyTwoSpinPrefixData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The full actual integer word before the forward Gaussian. -/
def monsterNortonCodeTwentyTwoSpinPrefix (k : Fin 16) : NortonUIntegerVector :=
  monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 1)
    (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 1)
      (monsterNortonCodeTwentyTwoForwardSpinInteger k))

private theorem diagonal_embed (M : Fin 12 → Fin 12 → ZMod 2)
    (v : NortonUIntegerVector) :
    monsterMonomialDiagonalEquiv M (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (monsterNortonUCompactIntegerDiagonal M v) := by
  ext t
  change qSign (monsterMonomialQuadratic M t) * (v (nortonUIntegerLabel t) : ℝ) = _
  simp only [nortonUIntegerEmbed, monsterNortonUCompactIntegerDiagonal,
    nortonUIntegerLabel_inverse, Int.cast_mul, nortonUIntegerSign_real]

private theorem permutation_embed (P : SpinIndex ≃ₗ[ZMod 2] SpinIndex)
    (v : NortonUIntegerVector) :
    monsterMonomialPermutation P (nortonUIntegerEmbed v) =
      nortonUIntegerEmbed (monsterNortonUCompactIntegerPermutation P v) := by
  ext t
  simp only [monsterMonomialPermutation_apply, nortonUIntegerEmbed,
    monsterNortonUCompactIntegerPermutation, nortonUIntegerLabel_inverse]

/-- The integer prefix is the actual product of two orthogonal monomial factors. -/
theorem monsterNortonCodeTwentyTwoSpinPrefix_actual (k : Fin 16) :
    (monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 1) *
      monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 1)).val
        (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k)) =
      nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefix k) := by
  simp only [nortonUIntegerSpin_mul_apply]
  change monsterMonomialPermutation (monsterNortonUCompactPermutation 1)
    (monsterMonomialDiagonalEquiv (monsterNortonUCompactDiagonal 1)
      (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k))) = _
  rw [diagonal_embed, permutation_embed]
  rfl

/-- Orthogonality gives the full actual monomial prefix norm independently of its support. -/
theorem monsterNortonCodeTwentyTwoSpinPrefix_norm (k : Fin 16) :
    spinPairing (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefix k))
      (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoSpinPrefix k)) = 64 := by
  let e : SpinHolomorph :=
    monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 1) *
      monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 1)
  have h := e.property.2 (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k))
    (nortonUIntegerEmbed (monsterNortonCodeTwentyTwoForwardSpinInteger k))
  dsimp only [e] at h
  rw [(monsterNortonCodeTwentyTwoSpinPrefix_actual k), (monsterNortonCodeTwentyTwoForwardSpin_norm
    k)] at h
  exact h

set_option maxHeartbeats 16000000 in
-- Check all sixty-four actual prefix entries before substituting the full cached vector.
/-- Each supported prefix sign comes from the complete genuine monomial input word. -/
theorem monsterNortonCodeTwentyTwoSpinPrefix_coefficient (k : Fin 16) (i : Fin 64) :
    (monsterNortonCodeTwentyTwoSpinPrefix k) (monsterNortonCodeTwentyTwoSpinPrefixLabel i) =
      (monsterNortonCodeTwentyTwoSpinPrefixCoefficient k) i := by
  fin_cases k <;> revert i <;> decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
