/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.PenultsOfTak.TicParity

namespace MetaMathlibExt

example : ¬ placementFirstPlayerWins (ticEnded 0) ∅ := by
  rw [impartialTic_firstPlayerWins_iff_odd]
  decide

example : placementFirstPlayerWins (ticEnded 1) ∅ := by
  rw [impartialTic_firstPlayerWins_iff_odd]
  decide

-- Independently of the parity theorem, a second player can always complete the
-- first player's row on a two-by-two board.
example : ¬ placementFirstPlayerWins (ticEnded 2) ∅ := by
  have rev_ne (i : Fin 2) : i.rev ≠ i := by
    intro he
    have hval := congrArg Fin.val he
    have hi := i.isLt
    simp only [Fin.val_rev] at hval
    omega
  intro hw
  obtain ⟨_, p, _, hl⟩ := (placementFirstPlayerWins_iff (ticEnded 2) ∅).mp hw
  let q : Fin 2 × Fin 2 := (p.1, p.2.rev)
  have hq : q ∉ insert p (∅ : Finset (Fin 2 × Fin 2)) := by
    intro h
    rcases Finset.mem_insert.mp h with he | hempty
    · exact rev_ne p.2 (congrArg Prod.snd he)
    · exact Finset.notMem_empty _ hempty
  have hsingle : ¬ ticEnded 2 (insert p ∅) := by
    rintro (⟨r, hr⟩ | ⟨c, hc⟩)
    · rcases Finset.mem_insert.mp (hr p.2.rev) with he | hempty
      · exact rev_ne p.2 (congrArg Prod.snd he)
      · exact Finset.notMem_empty _ hempty
    · rcases Finset.mem_insert.mp (hc p.1.rev) with he | hempty
      · exact rev_ne p.1 (congrArg Prod.fst he)
      · exact Finset.notMem_empty _ hempty
  have hwin : ticEnded 2 (insert q (insert p ∅)) := by
    refine Or.inl ⟨p.1, fun c => ?_⟩
    by_cases hc : c = p.2
    · rw [hc]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    · have he : c = p.2.rev := by
        apply Fin.ext
        have hne : c.val ≠ p.2.val := fun h => hc (Fin.ext h)
        have hc' := c.isLt
        have hp := p.2.isLt
        simp only [Fin.val_rev]
        omega
      rw [he]
      exact Finset.mem_insert_self _ _
  exact hl ((placementFirstPlayerWins_iff (ticEnded 2) (insert p ∅)).mpr
    ⟨hsingle, q, hq, fun h => ((placementFirstPlayerWins_iff (ticEnded 2) _).mp h).1 hwin⟩)

example : placementFirstPlayerWins (ticEnded 3) ∅ := by
  rw [impartialTic_firstPlayerWins_iff_odd]
  decide

end MetaMathlibExt
