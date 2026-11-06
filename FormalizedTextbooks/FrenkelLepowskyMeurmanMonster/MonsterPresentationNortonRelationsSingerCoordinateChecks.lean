/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- All twenty-three genuine coordinate checks from the source Singer Y dictionary. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerYWord
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsSingerCoordinateSources

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem low_code_commute (a : Fin 11) :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated (sourceQCode (monsterNortonSingerCoordinateCode a) 0)) := by
  have hx := monsterNortonSingerLocal_generated_conjugate_Q
    (sourceQCode ⟨(monsterNortonSingerYBasisSource a).val, by omega⟩ 0)
  rw [monsterNortonSingerImage_basis_code] at hx
  have hy := mul_inv_eq_iff_eq_mul.mpr (monsterNortonSingerLocal_generated_Y_basis a)
  rw [y555NortonActualY_word, y555NortonActualY_word] at hy
  have hd : (⟨(monsterNortonSingerYBasisSource a).val, by omega⟩ : Fin 4096) =
      monsterNortonSingerCoordinateCode a := by
    apply Fin.ext
    rfl
  simpa only [map_inv, hd] using
    monsterNortonSinger_commutator_commutes_of_covariance
      (localIntoGenerated monsterNortonSingerLocal) extraIntoGenerated
      (qIntoGenerated (sourceQCode ⟨(monsterNortonSingerYBasisSource a).val, by omega⟩ 0))
      (qIntoGenerated (sourceQCode (monsterNortonSingerYBasisFull a) 0)) hx hy

private theorem central_commute (c : ZMod 2) :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated (qCentral c)) := by
  have hc : ∀ c : ZMod 2, qCentral c = qCentralInvolution ^ c.val := by
    intro c
    fin_cases c <;> rfl
  rw [hc, map_pow]
  exact monsterNortonSinger_commutator_central.pow_right _

private theorem low_coordinate_commute (a : Fin 11) :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated (qCoordinateGenerator (Fin.castAdd 13 a))) := by
  rw [monsterNortonSingerCoordinateCode_decomposition, map_mul, map_mul]
  exact ((low_code_commute a).mul_right
    (monsterNortonSinger_commutator_even _ (monsterNortonSingerCoordinateCode_even a))).mul_right
      (central_commute _)

private theorem high_coordinate_commute (a : Fin 11) :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated (qCoordinateGenerator (Fin.natAdd 12 (Fin.castAdd 1 a)))) := by
  rw [monsterNortonSingerCoordinateCocode_decomposition]
  apply monsterNortonSinger_commutator_even
  have h : ∀ a : Fin 11,
      (Pi.single (Fin.castAdd 1 a) (1 : ZMod 2) : SpinIndex) 11 = 0 := by
    decide +kernel
  exact h a

/-- Every original coordinate except the final odd cocode centralizes the genuine commutator. -/
theorem monsterNortonSinger_commutator_coordinates (i : Fin 24) (hi : i ≠ 23) :
    Commute (localIntoGenerated monsterNortonSingerLocal⁻¹ * extraIntoGenerated⁻¹ *
      localIntoGenerated monsterNortonSingerLocal * extraIntoGenerated)
        (qIntoGenerated (qCoordinateGenerator i)) := by
  by_cases hl : i.val < 11
  · let a : Fin 11 := ⟨i.val, hl⟩
    have he : i = Fin.castAdd 13 a := Fin.ext rfl
    rw [he]
    exact low_coordinate_commute a
  · by_cases hm : i.val = 11
    · have he : i = 11 := Fin.ext hm
      rw [he, monsterNortonSingerCoordinateOmega_decomposition]
      exact monsterNortonSinger_commutator_omega
    · have hh : 12 ≤ i.val ∧ i.val < 23 := by
        have hlast : i.val ≠ 23 := by
          intro h
          exact hi (Fin.ext h)
        omega
      let a : Fin 11 := ⟨i.val - 12, by omega⟩
      have he : i = Fin.natAdd 12 (Fin.castAdd 1 a) := by
        apply Fin.ext
        change i.val = 12 + (i.val - 12)
        omega
      rw [he]
      exact high_coordinate_commute a

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
