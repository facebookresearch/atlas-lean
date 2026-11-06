/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Complete genuine source support of the eleventh integer tensor numerator. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhTensorInteger
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsLine01EleventhOddSupport

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The true tenth-state short numerator vanishes outside the actual source-code catalogue. -/
theorem monsterNortonLine01SeventhUShortInteger_source_zero (d : Fin 2048) (i : Fin 24)
    (hd : ¬ monsterNortonLine01SourceCodeSupport d) :
    monsterNortonLine01SeventhUShortIntegerNumerator (Sum.inr (Sum.inr (d, i))) = 0 := by
  have hs : ¬ monsterNortonLine01SeventhUShortSupport (Sum.inr (Sum.inr (d, i))) := by
    intro hs
    have hc := congrArg (fun r : GriessShortIndex => match r with
      | Sum.inr (Sum.inr (d, _)) => d
      | _ => (0 : Fin 2048)) hs
    change monsterNortonLine01ShortInputCode (monsterNortonLine01OctadSourceA
      (monsterNortonLine01SeventhUShortLookup (Sum.inr (Sum.inr (d, i)))).1
      (monsterNortonLine01SeventhUShortLookup (Sum.inr (Sum.inr (d, i)))).2) = d at hc
    exact hd (hc ▸ monsterNortonLine01SourceCodeSupport_label _)
  exact ite_eq_right hs

private theorem vanish_mix (p s a x u v : ℤ) (hx : x = 0) (hu : u = 0) (hv : v = 0) :
    p * (x + s * a * (u + v)) = 0 := by
  rw [hx, hu, hv]
  ring

/-- The entire actual eleventh tensor numerator vanishes outside the source-code catalogue. -/
theorem monsterNortonLine01EleventhTensorInteger_source_zero (n : Fin 4096) (i : Fin 24)
    (hn : ¬ monsterNortonLine01SourceCodeSupport ⟨n.val % 2048, by omega⟩) :
    monsterNortonLine01EleventhTensorIntegerNumerator n i = 0 := by
  let d : Fin 2048 := ⟨n.val % 2048, by omega⟩
  have hd : ¬ monsterNortonLine01SourceCodeSupport d := hn
  have hl : ¬ monsterNortonLine01CompactInputSupport ⟨d.val, by omega⟩ := by
    intro h
    have hc := (monsterNortonLine01SourceCodeSupport_spin ⟨d.val, by omega⟩).mp h
    exact hd (by simpa only [Nat.mod_eq_of_lt d.isLt] using hc)
  have hh : ¬ monsterNortonLine01CompactInputSupport ⟨d.val + 2048, by omega⟩ := by
    intro h
    have hc := (monsterNortonLine01SourceCodeSupport_spin ⟨d.val + 2048, by omega⟩).mp h
    exact hd (by simpa only [Nat.add_mod, Nat.mod_self, Nat.add_zero,
      Nat.mod_eq_of_lt d.isLt] using hc)
  exact vanish_mix _ _ _ _ _ _
    (monsterNortonLine01SeventhUShortInteger_source_zero d i hd)
    (monsterNortonLine01SeventhUTensorInteger_spin_zero _ _ hl)
    (monsterNortonLine01SeventhUTensorInteger_spin_zero _ _ hh)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
