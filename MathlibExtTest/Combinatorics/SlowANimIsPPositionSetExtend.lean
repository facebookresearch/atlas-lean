/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SlowANimIsPPositionSetExtend

/-!
# Tests for P-positions after adding moves

These tests apply `isPPositionSet_extend` to a finite move relation and to
adding moves already present in the original relation.

Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite
Families of Slow`A`-Nim*, INTEGERS 26 (2026), Article G3 (arXiv:2404.06608v3),
Proposition 7.
-/

namespace MathlibExtTest.Combinatorics.SlowANimIsPPositionSetExtend

open MetaMathlibExt

example : IsPPositionSet
    (fun x y : Fin 3 => (x = 2 ∧ y = 1) ∨ (x ≠ 0 ∧ y = 0)) ({0, 1} \ {1}) := by
  apply isPPositionSet_extend (fun x y => x = 2 ∧ y = 1)
    (fun x y => x ≠ 0 ∧ y = 0) {0, 1} {1}
  · unfold IsPPositionSet
    decide
  · intro x hx
    exact Or.inr hx
  · decide
  · decide
  · decide

example {α : Type*} (M : α → α → Prop) (P : Set α) (hP : IsPPositionSet M P) :
    IsPPositionSet (fun x y => M x y ∨ M x y) P := by
  have h := isPPositionSet_extend M M P ∅ hP (Set.empty_subset P)
    (by
      intro x y hx hy hM
      exact hP.1 x y hx.1 hM hy.1)
    (by
      rintro x _ ⟨y, hy, _⟩
      exact False.elim hy)
    (by
      intro x hx
      exact False.elim hx)
  simpa only [Set.sdiff_empty] using h

end MathlibExtTest.Combinatorics.SlowANimIsPPositionSetExtend
