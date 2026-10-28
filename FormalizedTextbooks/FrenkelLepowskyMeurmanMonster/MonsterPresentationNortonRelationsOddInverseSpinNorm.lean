/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Full actual norm of the phase-complete odd inverse-U spin numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSpinSparsePairings

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- The exact phase-complete integer numerator with the two actual V factors. -/
def monsterNortonOddInverseSpinNumerator (d : Fin 2048) : NortonUIntegerVector :=
  nortonUIntegerQ y555NortonVQ
    (monsterNortonUCompactInverseNumerator (nortonUIntegerQ y555NortonVQ
      (monsterNortonSourceZInteger d)))

private theorem incl_apply (q : Q) (x : SpinSpace) :
    (spinHolomorphIncl q).val x = spinRepresentation q x := rfl

/-- Both actual V factors and inverse U embed with their full scalar and central corrections. -/
theorem monsterNortonOddInverseSpinNumerator_actual (d : Fin 2048) :
    (spinHolomorphIncl y555NortonVQ * monsterNortonUFiber.val.1⁻¹ *
      spinHolomorphIncl y555NortonVQ).val
        (nortonUIntegerEmbed (monsterNortonSourceZInteger d)) =
      (-1 / 8 : ℝ) • nortonUIntegerEmbed (monsterNortonOddInverseSpinNumerator d) := by
  rw [nortonUIntegerSpin_mul_apply, nortonUIntegerSpin_mul_apply,
    incl_apply, incl_apply, nortonUIntegerQ_embed,
    monsterNortonUCompactInverseSpin_actual_embed, map_smul, nortonUIntegerQ_embed]
  rfl

/-- Orthogonality forces the complete integer numerator's squared norm to be 128. -/
theorem monsterNortonOddInverseSpinNumerator_norm (d : Fin 2048) :
    spinPairing (nortonUIntegerEmbed (monsterNortonOddInverseSpinNumerator d))
      (nortonUIntegerEmbed (monsterNortonOddInverseSpinNumerator d)) = 128 := by
  let e : SpinHolomorph := spinHolomorphIncl y555NortonVQ * monsterNortonUFiber.val.1⁻¹ *
    spinHolomorphIncl y555NortonVQ
  have he : ∀ f g, spinPairing (e.val f) (e.val g) = spinPairing f g := e.property.2
  have h := he (nortonUIntegerEmbed (monsterNortonSourceZInteger d))
    (nortonUIntegerEmbed (monsterNortonSourceZInteger d))
  change spinPairing
    ((spinHolomorphIncl y555NortonVQ * monsterNortonUFiber.val.1⁻¹ *
      spinHolomorphIncl y555NortonVQ).val
        (nortonUIntegerEmbed (monsterNortonSourceZInteger d)))
    ((spinHolomorphIncl y555NortonVQ * monsterNortonUFiber.val.1⁻¹ *
      spinHolomorphIncl y555NortonVQ).val
        (nortonUIntegerEmbed (monsterNortonSourceZInteger d))) = _ at h
  rw [monsterNortonOddInverseSpinNumerator_actual, monsterNortonSpinPairing_smul,
    monsterNortonSourceZInteger_spin_norm] at h
  norm_num at h
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
