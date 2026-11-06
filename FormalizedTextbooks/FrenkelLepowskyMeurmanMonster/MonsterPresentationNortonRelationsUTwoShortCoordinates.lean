/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact inverse-squared Norton action on actual preferred short units. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortUFastPowers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortIdentity

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual integral basis coordinates of a preferred Conway short-vector representative. -/
def monsterNortonShortIntegralCoordinates (r : GriessShortIndex) : Fin 24 → ℤ :=
  monsterNortonLeechCoordinates (griessShortIntegral r)

/-- The finite computation is exactly the genuine lattice coordinate equivalence. -/
theorem monsterNortonShortIntegralCoordinates_eq (r : GriessShortIndex) :
    monsterNortonShortIntegralCoordinates r =
      leechExplicitCoordinates (griessShortLatticeVector r) :=
  monsterNortonLeechCoordinates_eq (griessShortLatticeVector r)

/-- The complete physical vector is recovered from these actual coordinates. -/
theorem monsterNortonShortIntegralCoordinates_vector (r : GriessShortIndex) :
    leechBasisMatrix *ᵥ monsterNortonShortIntegralCoordinates r = griessShortIntegral r := by
  rw [monsterNortonShortIntegralCoordinates_eq]
  exact leechExplicitCoordinates_vector (griessShortLatticeVector r)

/-- Every actual preferred short representative has the required physical squared norm32. -/
theorem monsterNortonShortIntegralCoordinates_norm (r : GriessShortIndex) :
    leechSquareSum (leechBasisMatrix *ᵥ monsterNortonShortIntegralCoordinates r) = 32 := by
  rw [monsterNortonShortIntegralCoordinates_vector]
  exact griessShortIntegral_squareSum r

/-- The coordinate-to-class dictionary returns precisely the original preferred label. -/
theorem monsterNortonShortIntegralCoordinates_index (r : GriessShortIndex) :
    monsterNortonShortIndexOfCoordinates (monsterNortonShortIntegralCoordinates r)
      (monsterNortonShortIntegralCoordinates_norm r) = r := by
  apply griessShortClass_injective
  rw [monsterNortonShortIndexOfCoordinates_class]
  have he : leechExplicitCoordinateMap (monsterNortonShortIntegralCoordinates r) =
      griessShortLatticeVector r := by
    apply leechExplicitCoordinates.injective
    change leechExplicitCoordinates (leechExplicitCoordinates.symm
      (monsterNortonShortIntegralCoordinates r)) = _
    rw [leechExplicitCoordinates.apply_symm_apply, monsterNortonShortIntegralCoordinates_eq]
  rw [he]
  rfl

/-- The preferred output label of the genuine inverse-squared integral basis action. -/
noncomputable def monsterNortonUTwoInverseShortOutput (r : GriessShortIndex) :
    GriessShortIndex :=
  monsterNortonShortIndexOfCoordinates
    ((monsterNortonUInverseIntegralAction ^ 2) *ᵥ monsterNortonShortIntegralCoordinates r)
      (monsterNortonUInverseFastPower_short_norm 2 _
        (monsterNortonShortIntegralCoordinates_norm r))

/-- Full central phase of the two actual inverse Norton conjugations on the preferred lift. -/
def monsterNortonUTwoInverseShortPhase (r : GriessShortIndex) : ZMod 2 :=
  Multiplicative.toAdd (monsterNortonUQInverseFastOrbit 2
    (monsterNortonCoordinateQ (monsterNortonShortIntegralCoordinates r))).coeff

set_option maxRecDepth 10000 in
/-- The literal inverse-squared Norton element has this complete signed short image. -/
theorem monsterNortonUTwoInverse_pure_short (r : GriessShortIndex) :
    ((y555NortonActualU ^ 2)⁻¹).val (monsterNortonPureShort r) =
      qSign (monsterNortonUTwoInverseShortPhase r) •
        monsterNortonPureShort (monsterNortonUTwoInverseShortOutput r) := by
  have h := monsterNortonUInverseFastPower_short_basis 2
    (monsterNortonShortIntegralCoordinates r) (monsterNortonShortIntegralCoordinates_norm r)
  rw [monsterNortonShortIntegralCoordinates_index, inv_pow] at h
  have hs (s : GriessShortIndex) (c : ℝ) :
      griessConwayDecode (0, (c • Pi.single s 1, 0)) =
        c • monsterNortonPureShort s := by
    let L : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
      griessConwayDecodeLinear.comp
        ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))
    exact L.map_smul c (Pi.single s 1)
  rw [hs] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
