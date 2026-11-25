/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.PalindromicRecurrentOutsideP

namespace MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted.Tests

private def erasing : Morphism := fun a => if a = 0 then [0, 1] else []

example : extend erasing [2, 0, 1, 0] = [0, 1, 0, 1] := by decide

example : extendIter erasing 0 [0, 2, 1] = [0, 2, 1] := by decide

example : extendIter erasing 2 [0, 2, 1] = [0, 1] := by decide

example (u : InfWord) (k : Nat) : OccursAt [] u k := by
  intro i
  exact Fin.elim0 i

example (u : InfWord) : ¬ IsFixedPoint (fun a => [a]) u := by
  rintro ⟨a, _, hg, _⟩
  have h (n : Nat) : extendIter (fun a => [a]) n [a] = [a] := by
    induction n with
    | zero => rfl
    | succ n ih => simp [extendIter, Function.comp_apply, ih, extend]
  obtain ⟨n, hn⟩ := hg 2
  rw [h] at hn
  exact (by decide : ¬ (2 ≤ 1)) hn

example : InClassP (fun a => [a]) :=
  ⟨[], rfl, fun a => ⟨[a], rfl, rfl⟩⟩

example : MorphConjugate (fun a => [0, a]) (fun a => [a, 0]) :=
  Or.inl ⟨[0], fun _ => rfl⟩

example : MorphConjugate (fun a => [a, 0]) (fun a => [0, a]) :=
  Or.inr ⟨[0], fun _ => rfl⟩

example : conjecture := conjecture_holds

end MathlibExt.Combinatorics.PalindromicRecurrentOutsidePWanted.Tests
