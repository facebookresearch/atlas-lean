/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact binding of the explicit spin/Leech y82 lift to its literal word in the actual group G. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationLocalTensorFaithfulness
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555NortonActualCandidates

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The inverse triality conjugate of z is the actual second central sign. -/
theorem monsterSourceY_inverse_central_sign :
    centralSignIntoGenerated 2 =
      extraIntoGenerated⁻¹ * qIntoGenerated qCentralInvolution * extraIntoGenerated := by
  have hi : extraIntoGenerated ^ 2 = extraIntoGenerated⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ, extraIntoGenerated_pow_three]
  have h : centralSignIntoGenerated 2 = extraIntoGenerated ^ 2 *
      qIntoGenerated qCentralInvolution * (extraIntoGenerated ^ 2)⁻¹ := by
    apply Subtype.ext
    exact localCentralGriess_conjugate_square.symm
  rw [hi, inv_inv] at h
  exact h

/-- The literal source y word centralizes the actual central Q involution. -/
theorem monsterSourceY_word_commute_central (d : Fin 4096) (ε : ZMod 2) :
    y555NortonActualY d ε * qIntoGenerated qCentralInvolution =
      qIntoGenerated qCentralInvolution * y555NortonActualY d ε := by
  have hc := sourceGeneratedCode_commute_sign_two d ε
  rw [monsterSourceY_inverse_central_sign] at hc
  rw [y555NortonActualY_word]
  calc
    _ = extraIntoGenerated *
      (sourceGeneratedCode d ε * (extraIntoGenerated⁻¹ *
        qIntoGenerated qCentralInvolution * extraIntoGenerated)) * extraIntoGenerated⁻¹ := by group
    _ = extraIntoGenerated *
      ((extraIntoGenerated⁻¹ * qIntoGenerated qCentralInvolution * extraIntoGenerated) *
        sourceGeneratedCode d ε) * extraIntoGenerated⁻¹ := by rw [hc]
    _ = _ := by group

/-- The literal source word lies in the genuine local image by the proved full centralizer. -/
theorem monsterSourceY_word_mem_local (d : Fin 4096) (ε : ZMod 2) :
    y555NortonActualY d ε ∈ localIntoGenerated.range := by
  rw [← generatedCentralizer_eq_local_range]
  exact Subgroup.mem_centralizer_singleton_iff.mpr (monsterSourceY_word_commute_central d ε)

/-- The actual source y82 word is exactly the constructed spin/Leech candidate in G.
This uses the proved full centralizer and faithful genuine local tensor constituent. -/
theorem monsterSourceY82Generated_eq_actualWord :
    monsterSourceY82Generated = y555NortonActualY 82 0 := by
  obtain ⟨h, hh⟩ := monsterSourceY_word_mem_local 82 0
  have hρ : rhoLocal h = sExtra * rhoLocal (inclQ (sourceQCode 82 0)) * sExtra⁻¹ := by
    rw [y555NortonActualY_word] at hh
    exact congrArg Subtype.val hh
  have he : monsterSourceY82Local = h := by
    apply monsterLocalTensor_identifies
    intro x
    rw [hρ]
    exact monsterSourceY82_tensor_match x
  change localIntoGenerated monsterSourceY82Local = y555NortonActualY 82 0
  rw [he]
  exact hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
