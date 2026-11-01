/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual inverse-squared short images from the complete finite middle Q certificates. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortQCertificate0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortQCertificate1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortQCertificate2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine02MiddleShortQCertificate3

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- All 512 actual full Q images agree with their source dictionary and central phase. -/
theorem monsterNortonLine02MiddleShortQ_certificate (a : Fin 8) (e : Fin 64) :
    monsterNortonLine02QFastImage (monsterNortonLine02MiddleOutputQ a e) =
      qCentral (monsterNortonLine02MiddlePhase a e) * monsterNortonLine02MiddleInputQ a e := by
  fin_cases a
  · exact monsterNortonLine02MiddleShortQ_certificate0 0 e
  · exact monsterNortonLine02MiddleShortQ_certificate0 1 e
  · exact monsterNortonLine02MiddleShortQ_certificate1 0 e
  · exact monsterNortonLine02MiddleShortQ_certificate1 1 e
  · exact monsterNortonLine02MiddleShortQ_certificate2 0 e
  · exact monsterNortonLine02MiddleShortQ_certificate2 1 e
  · exact monsterNortonLine02MiddleShortQ_certificate3 0 e
  · exact monsterNortonLine02MiddleShortQ_certificate3 1 e

private theorem fiber_square_spin (f : localFiberSubgroup) :
    (f ^ 2).val.1 = f.val.1 ^ 2 := rfl

private theorem generated_fiber_apply (f : localFiberSubgroup) (x : GriessSpace) :
    (localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup f)).val x =
      localGriessRepresentation f x := rfl

private noncomputable def shortLift : (GriessShortIndex → ℝ) →ₗ[ℝ] GriessSpace :=
  griessConwayDecodeLinear.comp
    ((LinearMap.inr ℝ _ _).comp (LinearMap.inl ℝ _ _))

set_option maxRecDepth 10000 in
/-- Genuine squared Norton transport reverses the stated full middle short dictionary. -/
theorem monsterNortonLine02MiddleShort_forward (a : Fin 8) (e : Fin 64) :
    (y555NortonActualU ^ 2).val (monsterNortonPureShort (monsterNortonLine02MiddleOutput a e)) =
      qSign (monsterNortonLine02MiddlePhase a e) •
        monsterNortonPureShort (monsterNortonLine02MiddleInput a e) := by
  have hq : spinConjugation (monsterNortonUFiber ^ 2).val.1
      (monsterNortonShortQ (monsterNortonLine02MiddleOutput a e)) =
        qCentral (monsterNortonLine02MiddlePhase a e) *
          monsterNortonShortQ (monsterNortonLine02MiddleInput a e) := by
    rw [fiber_square_spin, monsterNortonLine02QFastImage_actual,
      monsterNortonLine02MiddleOutputQ_actual, monsterNortonLine02MiddleInputQ_actual]
    exact monsterNortonLine02MiddleShortQ_certificate a e
  have h := monsterNortonGriessShortBasis_of_Q_image (monsterNortonUFiber ^ 2)
    (monsterNortonLine02MiddleOutput a e) (monsterNortonLine02MiddleInput a e)
      (monsterNortonLine02MiddlePhase a e) hq
  have hg : localIntoGenerated (QuotientGroup.mk' localDiagonalSubgroup
      (monsterNortonUFiber ^ 2)) = y555NortonActualU ^ 2 := by
    simpa only [zpow_ofNat] using monsterNortonUFiber_generated_zpow (2 : ℤ)
  rw [← generated_fiber_apply, hg] at h
  exact h.trans (shortLift.map_smul _ _)

private theorem inverse_short_of_image (g : G) (r s : GriessShortIndex) (c : ZMod 2)
    (h : g.val (monsterNortonPureShort s) = qSign c • monsterNortonPureShort r) :
    (g⁻¹).val (monsterNortonPureShort r) = qSign c • monsterNortonPureShort s := by
  apply g.val.injective
  have hg : g.val ((g⁻¹).val (monsterNortonPureShort r)) = monsterNortonPureShort r :=
    LinearEquiv.apply_symm_apply _ _
  rw [hg, map_smul, h, smul_smul, qSign_sq, one_smul]

/-- Every actual inverse-squared middle image has precisely the certified pair or octad label. -/
theorem monsterNortonLine02MiddleShort_inverse (a : Fin 8) (e : Fin 64) :
    ((y555NortonActualU ^ 2)⁻¹).val
      (monsterNortonPureShort (monsterNortonLine02MiddleInput a e)) =
      qSign (monsterNortonLine02MiddlePhase a e) •
        monsterNortonPureShort (monsterNortonLine02MiddleOutput a e) :=
  inverse_short_of_image _ _ _ _ (monsterNortonLine02MiddleShort_forward a e)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
