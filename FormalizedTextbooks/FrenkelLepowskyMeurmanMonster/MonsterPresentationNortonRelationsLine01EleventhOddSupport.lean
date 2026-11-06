/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete support of the actual eleventh inverse-triality odd-short numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01SourceCoordinateSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual tenth-state tensor numerator vanishes outside the genuine input support. -/
theorem monsterNortonLine01SeventhUTensorInteger_spin_zero (n : Fin 4096) (j : Fin 24)
    (hn : ¬ monsterNortonLine01CompactInputSupport n) :
    monsterNortonLine01SeventhUTensorIntegerNumerator n j = 0 := by
  unfold monsterNortonLine01SeventhUTensorIntegerNumerator
  apply Finset.sum_eq_zero
  intro i _
  unfold monsterNortonLine01SeventhForwardPacket
  rw [ite_eq_right hn, zero_mul]

/-- The actual eleventh odd-short numerator vanishes outside the sixty-four source codes. -/
theorem monsterNortonLine01EleventhOddInteger_source_zero (d : Fin 2048) (i : Fin 24)
    (hd : ¬ monsterNortonLine01SourceCodeSupport d) :
    monsterNortonLine01EleventhOddIntegerNumerator d i = 0 := by
  have hl : ¬ monsterNortonLine01CompactInputSupport ⟨d.val, by omega⟩ := by
    intro h
    have hc := (monsterNortonLine01SourceCodeSupport_spin ⟨d.val, by omega⟩).mp h
    exact hd (by simpa only [Nat.mod_eq_of_lt d.isLt] using hc)
  have hh : ¬ monsterNortonLine01CompactInputSupport ⟨d.val + 2048, by omega⟩ := by
    intro h
    have hc := (monsterNortonLine01SourceCodeSupport_spin ⟨d.val + 2048, by omega⟩).mp h
    exact hd (by simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt d.isLt] using hc)
  unfold monsterNortonLine01EleventhOddIntegerNumerator
  rw [monsterNortonLine01SeventhUTensorInteger_spin_zero _ _ hl,
    monsterNortonLine01SeventhUTensorInteger_spin_zero _ _ hh, sub_self, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
