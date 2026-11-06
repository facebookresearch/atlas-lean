/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete finite spin packets of the actual seventh first-line tensor state. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01TensorSeventhCoefficients

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem xor_cancel (a b : Fin 4096) :
    monsterNortonBitXor (monsterNortonBitXor a b) b = a := by
  apply Fin.ext
  simp [monsterNortonBitXor, Nat.xor_assoc]

/-- The full integer spin packet in one of the sixteen reached physical coordinates. -/
def monsterNortonLine01TensorSeventhPacket (i : Fin 16) : NortonUIntegerVector :=
  fun n => if monsterNortonLine01SpinSupport n then
    monsterNortonLine01TensorSeventhCoefficientLookup i
      (monsterNortonLine01CompactOutputLookup (monsterNortonBitXor n 1038)) else 0

/-- The finite packet agrees with the entire actual seventh tensor numerator, including zeros. -/
theorem monsterNortonLine01TensorSeventhPacket_actual (i : Fin 16) (n : Fin 4096) :
    monsterNortonLine01TensorSeventhIntegerNumerator n (Fin.castLE (by omega) i) =
      monsterNortonLine01TensorSeventhPacket i n := by
  by_cases hn : monsterNortonLine01SpinSupport n
  · have he : monsterNortonLine01TensorSpinLabel
        (monsterNortonLine01CompactOutputLookup (monsterNortonBitXor n 1038)) = n := by
      unfold monsterNortonLine01TensorSpinLabel
      change monsterNortonBitXor _ 1038 = n
      rw [hn, xor_cancel]
    unfold monsterNortonLine01TensorSeventhPacket
    rw [ite_eq_left hn]
    conv_lhs => rw [← he]
    exact monsterNortonLine01TensorSeventh_coefficients _ _
  · unfold monsterNortonLine01TensorSeventhPacket
    rw [ite_eq_right hn]
    exact monsterNortonLine01TensorSeventhInteger_spin_zero _ _ hn

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
