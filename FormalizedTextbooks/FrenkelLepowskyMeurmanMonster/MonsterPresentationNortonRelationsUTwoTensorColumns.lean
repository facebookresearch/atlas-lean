/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Whole Griess tensor-column transport by literal squared and inverse-squared Norton elements. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUTwoSourceInverse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsTensorColumnAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonConjugation

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem generated_fiber_apply (f : localFiberSubgroup) (x : GriessSpace) :
    (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f)).val x =
      localGriessRepresentation f x := rfl

private theorem fiber_square_spin (f : localFiberSubgroup) :
    (f ^ 2).val.1 = f.val.1 ^ 2 := rfl

private theorem fiber_inverse_square_spin (f : localFiberSubgroup) :
    ((f⁻¹) ^ 2).val.1 = (f.val.1 ^ 2)⁻¹ := by
  change (f.val.1⁻¹) ^ 2 = (f.val.1 ^ 2)⁻¹
  rw [inv_pow]

/-- A literal squared Norton element transports an entire column by its actual two factors. -/
theorem monsterNortonUTwo_tensor_column (a : SpinSpace) (j : Fin 24) :
    (y555NortonActualU ^ 2).val (monsterNortonTensorLift (conwaySpinColumn a j)) =
      monsterNortonTensorRankOne ((monsterNortonUFiber ^ 2).val.2.val (Pi.single j 1))
        ((monsterNortonUFiber.val.1 ^ 2).val a) := by
  have h := monsterNortonLocalTensor_column (monsterNortonUFiber ^ 2) a j
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      (monsterNortonUFiber ^ 2)) = y555NortonActualU ^ 2 := by
    simpa only [zpow_ofNat] using monsterNortonUFiber_generated_zpow (2 : ℤ)
  rw [← generated_fiber_apply, hg, fiber_square_spin] at h
  exact h

/-- Literal inverse-squared Norton transport of every whole column keeps both inverse factors. -/
theorem monsterNortonUTwoInverse_tensor_column (a : SpinSpace) (j : Fin 24) :
    ((y555NortonActualU ^ 2)⁻¹).val (monsterNortonTensorLift (conwaySpinColumn a j)) =
      monsterNortonTensorRankOne (((monsterNortonUFiber⁻¹) ^ 2).val.2.val (Pi.single j 1))
        (((monsterNortonUFiber.val.1 ^ 2)⁻¹).val a) := by
  have h := monsterNortonLocalTensor_column ((monsterNortonUFiber⁻¹) ^ 2) a j
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      ((monsterNortonUFiber⁻¹) ^ 2)) = (y555NortonActualU ^ 2)⁻¹ := by
    simpa only [zpow_neg, zpow_ofNat, inv_pow] using
      monsterNortonUFiber_generated_zpow (-2 : ℤ)
  rw [← generated_fiber_apply, hg, fiber_inverse_square_spin] at h
  exact h

/-- The entire translated source Z column has an exact sixteen-term inverse-squared numerator. -/
theorem monsterNortonUTwoInverse_source_ZQ_column (q : Q) (d : Fin 2048) (j : Fin 24) :
    ((y555NortonActualU ^ 2)⁻¹).val
      (monsterNortonTensorLift (conwaySpinColumn (monsterNortonSourceZQSpinImage q d) j)) =
    monsterNortonTensorRankOne (((monsterNortonUFiber⁻¹) ^ 2).val.2.val (Pi.single j 1))
      ((qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
        ((1 / 4 : ℝ) • nortonUIntegerEmbed (monsterNortonUTwoCompactInverseNumerator
          (nortonUIntegerQ q (monsterNortonSourceZInteger d))))) := by
  rw [monsterNortonUTwoInverse_tensor_column, monsterNortonUTwoSourceZQSpin_inverse]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
