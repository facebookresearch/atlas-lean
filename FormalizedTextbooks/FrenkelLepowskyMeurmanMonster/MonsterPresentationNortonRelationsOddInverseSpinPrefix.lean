/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual two-term monomial input to the inverse compact spin Gaussian. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsIntegerSpinNorm

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

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

private theorem incl_apply (q : Q) (x : SpinSpace) :
    (spinHolomorphIncl q).val x = spinRepresentation q x := rfl

/-- The full integer monomial prefix before the actual inverse Gaussian sum. -/
def monsterNortonOddInverseSpinPrefix (d : Fin 2048) : NortonUIntegerVector :=
  monsterNortonUCompactIntegerPermutation (monsterNortonUCompactPermutation 0).symm
    (monsterNortonUCompactIntegerDiagonal (monsterNortonUCompactDiagonal 0)
      (nortonUIntegerQ monsterNortonUCompactCorrection⁻¹
        (nortonUIntegerQ y555NortonVQ (monsterNortonSourceZInteger d))))

/-- The integer prefix embeds as its complete actual orthogonal monomial word. -/
theorem monsterNortonOddInverseSpinPrefix_actual (d : Fin 2048) :
    (monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 0).symm *
      monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 0) *
        spinHolomorphIncl monsterNortonUCompactCorrection⁻¹ *
          spinHolomorphIncl y555NortonVQ).val
            (nortonUIntegerEmbed (monsterNortonSourceZInteger d)) =
      nortonUIntegerEmbed (monsterNortonOddInverseSpinPrefix d) := by
  simp only [nortonUIntegerSpin_mul_apply]
  rw [incl_apply, incl_apply, nortonUIntegerQ_embed, nortonUIntegerQ_embed]
  change monsterMonomialPermutation (monsterNortonUCompactPermutation 0).symm
    (monsterMonomialDiagonalEquiv (monsterNortonUCompactDiagonal 0)
      (nortonUIntegerEmbed (nortonUIntegerQ monsterNortonUCompactCorrection⁻¹
        (nortonUIntegerQ y555NortonVQ (monsterNortonSourceZInteger d))))) = _
  rw [diagonal_embed, permutation_embed]
  rfl

/-- The complete prefix has actual squared norm two because all its factors are orthogonal. -/
theorem monsterNortonOddInverseSpinPrefix_norm (d : Fin 2048) :
    spinPairing (nortonUIntegerEmbed (monsterNortonOddInverseSpinPrefix d))
      (nortonUIntegerEmbed (monsterNortonOddInverseSpinPrefix d)) = 2 := by
  let e : SpinHolomorph :=
    monsterMonomialPermutationHolomorph (monsterNortonUCompactPermutation 0).symm *
      monsterMonomialDiagonalHolomorph (monsterNortonUCompactDiagonal 0) *
        spinHolomorphIncl monsterNortonUCompactCorrection⁻¹ * spinHolomorphIncl y555NortonVQ
  have he : ∀ f g, spinPairing (e.val f) (e.val g) = spinPairing f g := e.property.2
  have h := he (nortonUIntegerEmbed (monsterNortonSourceZInteger d))
    (nortonUIntegerEmbed (monsterNortonSourceZInteger d))
  dsimp only [e] at h
  rw [monsterNortonOddInverseSpinPrefix_actual, monsterNortonSourceZInteger_spin_norm] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
