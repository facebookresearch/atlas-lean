/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact source transport of the five odd cocode Norton point reflections. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationWreathLocalGenerationTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedNormalTrialityReflection

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Each of the five cocode point parameters is precisely its literal source cocode lift. -/
theorem monsterNortonPoint_succ_literal_cocode (j : Fin 5) :
    y555NortonPointQ j.succ =
      cocodeQ (golayLabelCoefficients (y555NortonPointCocodeLabel j)) := rfl

/-- All five actual source cocode labels have odd last coefficient. -/
theorem monsterNortonPoint_cocode_last (j : Fin 5) :
    golayLabelCoefficients (y555NortonPointCocodeLabel j) 11 = 1 := by
  fin_cases j <;> decide +kernel

/-- The complete source block dictionary applies to all five actual point reflections. -/
theorem monsterNortonPoint_succ_blocks (j : Fin 5) (x : GriessSpace) :
    trialityBlocksEquiv (rhoLocal (inclQ (y555NortonPointQ j.succ)) x) =
      cocodeDictionaryAction (golayLabelCoefficients (y555NortonPointCocodeLabel j))
        (trialityBlocksEquiv x) := by
  rw [monsterNortonPoint_succ_literal_cocode]
  exact cocodeQ_blocks _ (monsterNortonPoint_cocode_last j) x

/-- Each genuine odd cocode point inverts the actual generated extra operator. -/
theorem monsterNortonPoint_succ_inverts_extra (j : Fin 5) :
    y555NortonPoint j.succ * extraIntoGenerated * (y555NortonPoint j.succ)⁻¹ =
      extraIntoGenerated⁻¹ := by
  apply Subtype.ext
  change rhoLocal (inclQ (y555NortonPointQ j.succ)) * sExtra *
    (rhoLocal (inclQ (y555NortonPointQ j.succ)))⁻¹ = sExtra⁻¹
  rw [monsterNortonPoint_succ_literal_cocode]
  exact cocodeQ_conjugates_sExtra_inverse _ (monsterNortonPoint_cocode_last j)

/-- Inversion also holds for the precise inverse-triality assignment used by Norton. -/
theorem monsterNortonPoint_succ_inverts_sourceTriality (j : Fin 5) :
    y555NortonPoint j.succ * monsterSourceTriality * (y555NortonPoint j.succ)⁻¹ =
      monsterSourceTriality⁻¹ := by
  have h := congrArg (fun g : G => g⁻¹) (monsterNortonPoint_succ_inverts_extra j)
  simpa only [mul_inv_rev, inv_inv, monsterSourceTriality, mul_assoc] using h

/-- The order-three inverse-triality word has the expected two-inverse product. -/
theorem monsterNortonSourceTriality_inv_mul_inv :
    monsterSourceTriality⁻¹ * monsterSourceTriality⁻¹ = monsterSourceTriality := by
  change extraIntoGenerated * extraIntoGenerated = extraIntoGenerated⁻¹
  apply eq_inv_iff_mul_eq_one.mpr
  simpa only [pow_succ, pow_zero, one_mul] using extraIntoGenerated_pow_three

/-- Actual triality transport sends an odd point to point times triality. -/
theorem monsterNortonPoint_succ_sourceTriality_transport (j : Fin 5) :
    monsterSourceTriality * y555NortonPoint j.succ * monsterSourceTriality⁻¹ =
      y555NortonPoint j.succ * monsterSourceTriality := by
  have hi : (y555NortonPoint j.succ)⁻¹ = y555NortonPoint j.succ := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_two, y555NortonPoint_sq]
  have h := monsterNortonPoint_succ_inverts_sourceTriality j
  rw [hi] at h
  have ht : monsterSourceTriality * y555NortonPoint j.succ =
      y555NortonPoint j.succ * monsterSourceTriality⁻¹ := by
    calc
      _ = y555NortonPoint j.succ *
          (y555NortonPoint j.succ * monsterSourceTriality *
            y555NortonPoint j.succ) := by
        simp only [← mul_assoc]
        rw [← pow_two, y555NortonPoint_sq, one_mul]
      _ = _ := by rw [h]
  rw [ht, mul_assoc, monsterNortonSourceTriality_inv_mul_inv]

/-- Source triality genuinely lies outside the actual local subgroup H. -/
theorem monsterNortonSourceTriality_not_mem_local :
    monsterSourceTriality ∉ localIntoGenerated.range := by
  intro ht
  rw [← generatedCentralizer_eq_local_range] at ht
  have hc := Subgroup.mem_centralizer_singleton_iff.mp ht
  have he : monsterSourceTriality * qIntoGenerated qCentralInvolution *
      monsterSourceTriality⁻¹ = qIntoGenerated qCentralInvolution := by
    rw [hc]
    group
  have hs : centralSignIntoGenerated 2 = qIntoGenerated qCentralInvolution := by
    exact monsterSourceY_inverse_central_sign.trans he
  have h := congrArg (fun g : G => g.val) hs
  change trialityCentralSign 2 = localCentralGriess at h
  rw [localCentralGriess_eq_trialityCentralSign] at h
  have hi := trialityCentralSign_injective h
  norm_num at hi

/-- The transported five odd points are outside H; their source transport is not a local lift. -/
theorem monsterNortonPoint_succ_sourceTriality_transport_not_mem_local (j : Fin 5) :
    monsterSourceTriality * y555NortonPoint j.succ * monsterSourceTriality⁻¹ ∉
      localIntoGenerated.range := by
  rw [monsterNortonPoint_succ_sourceTriality_transport]
  intro hm
  apply monsterNortonSourceTriality_not_mem_local
  have hp : y555NortonPoint j.succ ∈ localIntoGenerated.range :=
    ⟨inclQ (y555NortonPointQ j.succ), rfl⟩
  have h := localIntoGenerated.range.mul_mem (localIntoGenerated.range.inv_mem hp) hm
  simpa only [inv_mul_cancel_left] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
