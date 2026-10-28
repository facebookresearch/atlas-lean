/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Exact high/low spin symmetry of the verified first-line compact output catalogue. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01CompactColumnData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Interchange the actual low and high twelve-bit spin labels. -/
def monsterNortonLine01CompactHighFlip (n : Fin 4096) : Fin 4096 :=
  ⟨if n.val < 2048 then n.val + 2048 else n.val - 2048, by split_ifs <;> omega⟩

/-- Interchange the two halves of the displayed output catalogue. -/
def monsterNortonLine01CompactOutputFlip (p : Fin 128) : Fin 128 :=
  ⟨if p.val < 64 then p.val + 64 else p.val - 64, by split_ifs <;> omega⟩

/-- The actual high/low label interchange is involutive. -/
theorem monsterNortonLine01CompactHighFlip_involutive :
    Function.Involutive monsterNortonLine01CompactHighFlip := by
  intro n
  apply Fin.ext
  simp only [monsterNortonLine01CompactHighFlip]
  split_ifs <;> omega

set_option maxRecDepth 10000 in
/-- The output catalogue records the actual high/low spin-label pairing. -/
theorem monsterNortonLine01CompactOutputFlip_label (p : Fin 128) :
    monsterNortonLine01CompactOutputLabel (monsterNortonLine01CompactOutputFlip p) =
      monsterNortonLine01CompactHighFlip (monsterNortonLine01CompactOutputLabel p) := by
  revert p
  decide +kernel

set_option maxRecDepth 10000 in
/-- All output coefficients agree across their actual high/low label pairs. -/
theorem monsterNortonLine01CompactOutputFlip_coefficient (k : Fin 16) (p : Fin 128) :
    monsterNortonLine01CompactOutputCoefficient k (monsterNortonLine01CompactOutputFlip p) =
      monsterNortonLine01CompactOutputCoefficient k p := by
  revert k p
  decide +kernel

/-- The entire output integer vector is invariant under actual high/low spin-label interchange. -/
theorem monsterNortonLine01CompactOutputVector_high (k : Fin 16) (n : Fin 4096) :
    monsterNortonLine01CompactOutputVector k (monsterNortonLine01CompactHighFlip n) =
      monsterNortonLine01CompactOutputVector k n := by
  by_cases hn : monsterNortonLine01CompactOutputSupport n
  · have he : monsterNortonLine01CompactOutputLabel
        (monsterNortonLine01CompactOutputLookup n) = n := hn
    have hp := monsterNortonLine01CompactOutputFlip_label
      (monsterNortonLine01CompactOutputLookup n)
    rw [he] at hp
    have hf : monsterNortonLine01CompactOutputSupport
        (monsterNortonLine01CompactHighFlip n) := by
      rw [← hp]
      exact monsterNortonLine01CompactOutputLabel_support _
    simp only [monsterNortonLine01CompactOutputVector, ite_eq_left hn, ite_eq_left hf]
    rw [← hp, monsterNortonLine01CompactOutputLookup_label,
      monsterNortonLine01CompactOutputFlip_coefficient]
  · have hf : ¬ monsterNortonLine01CompactOutputSupport
        (monsterNortonLine01CompactHighFlip n) := by
      intro hf
      have he : monsterNortonLine01CompactOutputLabel
          (monsterNortonLine01CompactOutputLookup (monsterNortonLine01CompactHighFlip n)) =
            monsterNortonLine01CompactHighFlip n := hf
      have hp := monsterNortonLine01CompactOutputFlip_label
        (monsterNortonLine01CompactOutputLookup (monsterNortonLine01CompactHighFlip n))
      rw [he, monsterNortonLine01CompactHighFlip_involutive] at hp
      apply hn
      rw [← hp]
      exact monsterNortonLine01CompactOutputLabel_support _
    simp only [monsterNortonLine01CompactOutputVector, ite_eq_right hn, ite_eq_right hf]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
