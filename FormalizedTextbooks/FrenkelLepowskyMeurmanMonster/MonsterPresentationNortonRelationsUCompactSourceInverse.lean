/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact integral two-delta source columns for the actual inverse Norton spin word. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSourceSpin
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsUCompactSpinInverse

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem delta_embed (d : Fin 4096) :
    nortonUIntegerEmbed (Pi.single d 1) =
      (Pi.single (golayLabelCoefficients d) 1 : SpinSpace) := by
  ext t
  have he : nortonUIntegerLabel t = d ↔ t = golayLabelCoefficients d := by
    constructor
    · intro h
      rw [← nortonUIntegerLabel_inverse t, h]
    · intro h
      rw [h, nortonUIntegerLabel_coeff]
  simp only [nortonUIntegerEmbed, Pi.single_apply, he]
  split_ifs <;> norm_num

/-- The source Y spin column's exact integral difference of its two dictionary deltas. -/
def monsterNortonSourceYInteger (d : Fin 2048) : NortonUIntegerVector :=
  Pi.single ⟨d.val, by omega⟩ 1 - Pi.single ⟨d.val + 2048, by omega⟩ 1

/-- The source Z spin column's exact integral sum of its two dictionary deltas. -/
def monsterNortonSourceZInteger (d : Fin 2048) : NortonUIntegerVector :=
  Pi.single ⟨d.val, by omega⟩ 1 + Pi.single ⟨d.val + 2048, by omega⟩ 1

private theorem integer_y_embed (d : Fin 2048) :
    nortonUIntegerEmbed (monsterNortonSourceYInteger d) =
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) -
        Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 := by
  have h : nortonUIntegerEmbed (monsterNortonSourceYInteger d) =
      nortonUIntegerEmbed (Pi.single ⟨d.val, by omega⟩ 1) -
        nortonUIntegerEmbed (Pi.single ⟨d.val + 2048, by omega⟩ 1) := by
    ext t
    simp [monsterNortonSourceYInteger, nortonUIntegerEmbed]
  rw [h, delta_embed, delta_embed]

private theorem integer_z_embed (d : Fin 2048) :
    nortonUIntegerEmbed (monsterNortonSourceZInteger d) =
      (Pi.single (golayLabelCoefficients ⟨d.val, by omega⟩) 1 : SpinSpace) +
        Pi.single (golayLabelCoefficients ⟨d.val + 2048, by omega⟩) 1 := by
  have h : nortonUIntegerEmbed (monsterNortonSourceZInteger d) =
      nortonUIntegerEmbed (Pi.single ⟨d.val, by omega⟩ 1) +
        nortonUIntegerEmbed (Pi.single ⟨d.val + 2048, by omega⟩ 1) := by
    ext t
    simp [monsterNortonSourceZInteger, nortonUIntegerEmbed]
  rw [h, delta_embed, delta_embed]

/-- The actual inverse Norton word transports source Y by one exact integer Gaussian numerator. -/
theorem monsterNortonUCompactSourceYSpin_inverse (d : Fin 2048) (j : Fin 24) :
    (monsterNortonUFiber.val.1⁻¹).val (trialityYSpin d j) =
      ((if (golayEncodedMask d.val).testBit j.val then (-1 : ℝ) else 1) / Real.sqrt 2) •
        ((-1 / 8 : ℝ) • nortonUIntegerEmbed
          (monsterNortonUCompactInverseNumerator (monsterNortonSourceYInteger d))) := by
  rw [monsterNortonSourceYSpin_basis, ← integer_y_embed, map_smul,
    monsterNortonUCompactInverseSpin_actual_embed]

/-- The actual inverse Norton word transports source Z with the exact central sign retained. -/
theorem monsterNortonUCompactSourceZSpin_inverse (d : Fin 2048) :
    (monsterNortonUFiber.val.1⁻¹).val (trialityZSpin d) =
      (qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) / Real.sqrt 2) •
        ((-1 / 8 : ℝ) • nortonUIntegerEmbed
          (monsterNortonUCompactInverseNumerator (monsterNortonSourceZInteger d))) := by
  rw [monsterNortonSourceZSpin_basis, ← integer_z_embed, map_smul,
    monsterNortonUCompactInverseSpin_actual_embed]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
