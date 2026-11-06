/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual Norton powers on arbitrary shortest-vector coordinates, using full-phase finite caches. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsQFastOrbit

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Every actual positive Norton matrix power preserves shortest-vector norm. -/
theorem monsterNortonUFastPower_short_norm (n : ℕ) (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    leechSquareSum (leechBasisMatrix *ᵥ ((monsterNortonUIntegralAction ^ n) *ᵥ z)) = 32 :=
  monsterNortonIntegralAction_short_norm (monsterNortonUFiber ^ n) _
    (monsterNortonUIntegralAction_power_basis n) z hn

/-- Every actual inverse Norton matrix power preserves shortest-vector norm. -/
theorem monsterNortonUInverseFastPower_short_norm (n : ℕ) (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    leechSquareSum (leechBasisMatrix *ᵥ ((monsterNortonUInverseIntegralAction ^ n) *ᵥ z)) =
      32 :=
  monsterNortonIntegralAction_short_norm ((monsterNortonUFiber⁻¹) ^ n) _
    (monsterNortonUInverseIntegralAction_power_basis n) z hn

private theorem actual_positive_power (n : ℕ) :
    localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup (monsterNortonUFiber ^ n)) =
      y555NortonActualU ^ n := by
  rw [map_pow, map_pow]
  change (localIntoGenerated monsterNortonULocal) ^ n = _
  rw [monsterNortonULocal_generated]

private theorem actual_inverse_power (n : ℕ) :
    localIntoGenerated
      (QuotientGroup.mk' localDiagonalSubgroup ((monsterNortonUFiber⁻¹) ^ n)) =
        (y555NortonActualU⁻¹) ^ n := by
  rw [map_pow, map_inv, map_pow, map_inv]
  change ((localIntoGenerated monsterNortonULocal)⁻¹) ^ n = _
  rw [monsterNortonULocal_generated]

/-- The literal actual Norton word to any positive power has this exact signed short image. -/
theorem monsterNortonUFastPower_short_basis (n : ℕ) (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    (y555NortonActualU ^ n).val
      (griessConwayDecode (0, (Pi.single (monsterNortonShortIndexOfCoordinates z hn) 1, 0))) =
    griessConwayDecode (0, (qSign (toAdd
      (monsterNortonUQFastOrbit n (monsterNortonCoordinateQ z)).coeff) •
        Pi.single (monsterNortonShortIndexOfCoordinates ((monsterNortonUIntegralAction ^ n) *ᵥ z)
          (monsterNortonUFastPower_short_norm n z hn)) (1 : ℝ), 0)) := by
  rw [← actual_positive_power n]
  change localGriessRepresentation (monsterNortonUFiber ^ n) _ = _
  have h := monsterNortonIntegralAction_short_basis (monsterNortonUFiber ^ n)
    (monsterNortonUIntegralAction ^ n) (monsterNortonUIntegralAction_power_basis n) z hn
  rw [monsterNortonUQFastOrbit_short_phase] at h
  exact h

/-- Literal inverse Norton powers have signed short images without using an order relation. -/
theorem monsterNortonUInverseFastPower_short_basis (n : ℕ) (z : Fin 24 → ℤ)
    (hn : leechSquareSum (leechBasisMatrix *ᵥ z) = 32) :
    ((y555NortonActualU⁻¹) ^ n).val
      (griessConwayDecode (0, (Pi.single (monsterNortonShortIndexOfCoordinates z hn) 1, 0))) =
    griessConwayDecode (0, (qSign (toAdd
      (monsterNortonUQInverseFastOrbit n (monsterNortonCoordinateQ z)).coeff) •
        Pi.single (monsterNortonShortIndexOfCoordinates
          ((monsterNortonUInverseIntegralAction ^ n) *ᵥ z)
          (monsterNortonUInverseFastPower_short_norm n z hn)) (1 : ℝ), 0)) := by
  rw [← actual_inverse_power n]
  change localGriessRepresentation ((monsterNortonUFiber⁻¹) ^ n) _ = _
  have h := monsterNortonIntegralAction_short_basis ((monsterNortonUFiber⁻¹) ^ n)
    (monsterNortonUInverseIntegralAction ^ n)
    (monsterNortonUInverseIntegralAction_power_basis n) z hn
  rw [monsterNortonUQInverseFastOrbit_short_phase] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
