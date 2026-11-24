/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.SnortOppositionBlocks

open MetaMathlibExt

-- Two independent pairs are joined by two matching edges. The index `none` has an empty block.
example : IsOpposable ({
    Adj := fun u w => u.1 ≠ w.1 ∧ u.2 = w.2
    symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ } : SimpleGraph (Bool × Bool)) := by
  let p (v : Bool × Bool) : Option Bool := some v.1
  let f (v : Bool × Bool) : Bool × Bool := (v.1, !v.2)
  refine isOpposable_of_blocks _ p f ?_ ?_
  · intro i
    let flip (v : {w // p w = i}) : {w // p w = i} := ⟨f v, v.property⟩
    have hinv : Function.Involutive flip := by
      rintro ⟨⟨a, b⟩, hb⟩
      apply Subtype.ext
      simp [flip, f]
    refine ⟨⟨hinv.toPerm flip, ?_⟩, ?_, fun _ => rfl⟩
    · intro u w
      have h : u.val.1 = w.val.1 := Option.some.inj (u.property.trans w.property.symm)
      exact iff_of_false (fun hadj => hadj.1 h) (fun hadj => hadj.1 h)
    · intro v
      refine ⟨hinv v, ?_, fun hadj => hadj.1 rfl⟩
      intro h
      exact Bool.not_ne_self _ (congrArg (fun x => x.val.2) h)
  · rintro ⟨a, b⟩ ⟨c, d⟩ _
    change ((a ≠ c ∧ b = d) ↔ (a ≠ c ∧ (!b) = (!d))) ∧
      ((a ≠ c ∧ b = (!d)) ↔ (a ≠ c ∧ (!b) = d))
    cases b <;> cases d <;> simp
