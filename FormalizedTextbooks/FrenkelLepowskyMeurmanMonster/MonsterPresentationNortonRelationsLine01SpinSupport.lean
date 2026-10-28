/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual vanishing outside the finite first-line tensor spin-label support. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SpinSupportData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem q_output_zero (k : Fin 16) (n : Fin 4096)
    (hn : ¬ monsterNortonLine01SpinSupport n) :
    nortonUIntegerQ y555NortonVQ (monsterNortonLine01CompactOutputVector k) n = 0 := by
  simp only [nortonUIntegerQ, monsterNortonLine01SpinSupport_v_translation,
    monsterNortonBitXor_label,
    nortonUIntegerLabel_coeff, monsterNortonLine01CompactOutputVector]
  have ho : ¬ monsterNortonLine01CompactOutputSupport (monsterNortonBitXor n 1038) := hn
  rw [ite_eq_right ho, mul_zero]

/-- The complete actual sixth tensor numerator vanishes outside the 128-label support. -/
theorem monsterNortonLine01TensorSixthInteger_spin_zero (n : Fin 4096) (i : Fin 24)
    (hn : ¬ monsterNortonLine01SpinSupport n) :
    monsterNortonLine01TensorSixthIntegerNumerator n i = 0 := by
  unfold monsterNortonLine01TensorSixthIntegerNumerator
  apply Finset.sum_eq_zero
  intro k _
  rw [q_output_zero k n hn, mul_zero, zero_mul]

private theorem odd_numerator_outside (d : Fin 2048) (i : Fin 24)
    (hd : ¬ monsterNortonLine01SpinSupport ⟨d.val, by omega⟩) :
    monsterNortonLine01OddSixthNumerator d i = 0 := by
  unfold monsterNortonLine01OddSixthNumerator
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro k _
  rw [ite_eq_right]
  rintro ⟨ha, he, _⟩
  have h := (monsterNortonLine01OddSource_spinSupport a k ha).1
  exact hd (by simpa only [he] using h)

private theorem vanish_mix (s p l a b x : ℤ) (ha : a = 0) (hb : b = 0) (hx : x = 0) :
    s * (-p * (a - b) + 64 * l * x) = 0 := by
  rw [ha, hb, hx]
  ring

/-- The complete actual seventh tensor numerator vanishes outside the same 128 spin labels. -/
theorem monsterNortonLine01TensorSeventhInteger_spin_zero (n : Fin 4096) (i : Fin 24)
    (hn : ¬ monsterNortonLine01SpinSupport n) :
    monsterNortonLine01TensorSeventhIntegerNumerator n i = 0 := by
  have hl : ¬ monsterNortonLine01SpinSupport ⟨n.val % 2048, by omega⟩ :=
    fun h => hn ((monsterNortonLine01SpinSupport_low_high n).1.mpr h)
  have hh : ¬ monsterNortonLine01SpinSupport ⟨n.val % 2048 + 2048, by omega⟩ :=
    fun h => hn ((monsterNortonLine01SpinSupport_low_high n).2.mpr h)
  exact vanish_mix _ _ _ _ _ _
    (monsterNortonLine01TensorSixthInteger_spin_zero _ i hl)
    (monsterNortonLine01TensorSixthInteger_spin_zero _ i hh)
    (odd_numerator_outside _ i hl)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
