/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- General actual odd-cocode reflection relation used by Norton point/line normal forms. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsFirstLine
@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every positive odd cocode inverts the genuine source triality element. -/
theorem monsterNortonOddCocode_conjugates_triality (h : SpinIndex) (hh : h 11 = 1) :
    qIntoGenerated (cocodeQ h) * monsterSourceTriality *
      (qIntoGenerated (cocodeQ h))⁻¹ = monsterSourceTriality⁻¹ := by
  have he : qIntoGenerated (cocodeQ h) * extraIntoGenerated *
      (qIntoGenerated (cocodeQ h))⁻¹ = extraIntoGenerated⁻¹ := by
    apply Subtype.ext
    exact cocodeQ_conjugates_sExtra_inverse h hh
  have hi := congrArg Inv.inv he
  simpa only [monsterSourceTriality, mul_inv_rev, inv_inv, mul_assoc] using hi

/-- Consequently every actual odd-cocode-times-source-triality word has square one. -/
theorem monsterNortonOddCocode_triality_square (h : SpinIndex) (hh : h 11 = 1) :
    (qIntoGenerated (cocodeQ h) * monsterSourceTriality) ^ 2 = 1 := by
  have hp : (qIntoGenerated (cocodeQ h))⁻¹ = qIntoGenerated (cocodeQ h) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← map_mul, cocodeQ_square, map_one]
  have hi := monsterNortonOddCocode_conjugates_triality h hh
  rw [hp] at hi
  calc
    _ = (qIntoGenerated (cocodeQ h) * monsterSourceTriality *
      qIntoGenerated (cocodeQ h)) * monsterSourceTriality := by rw [pow_two]; group
    _ = 1 := by rw [hi, inv_mul_cancel]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
