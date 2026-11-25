/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Combinatorics.Enumerative.NColorCompositionThreeFibonacci

/-! # Tests for the Fibonacci identity for compositions with colors 3 and 4 -/

open MathlibExt.Combinatorics.Enumerative.NColorCompositionsWanted

example : ccoAllowed 3 3 + ccoAllowed 3 1 = 1 := by
  exact ccoAllowed_three_add (n := 3) (hn := by decide)

-- At total 4, shortening `(4, 3)` and removing `(4, 4)` both contribute.
example : ccoAllowed 3 4 + ccoAllowed 3 2 = 2 := by
  exact ccoAllowed_three_add (n := 4) (hn := by decide)

-- At total 7, all three branches contribute, including a leading `(3, 3)`.
example : ccoAllowed 3 7 + ccoAllowed 3 5 = 8 := by
  exact ccoAllowed_three_add (n := 7) (hn := by decide)

example : ccoAllowed 3 8 + ccoAllowed 3 6 = 13 := by
  exact ccoAllowed_three_add (n := 8) (hn := by decide)

example : ∃ p : ColorCompAllowed 3 7, p.val = [(3, 3), (4, 4)] :=
  ⟨⟨[(3, 3), (4, 4)], by simp⟩, rfl⟩

example : ∃ p : ColorCompAllowed 3 7, p.val = [(4, 4), (3, 3)] :=
  ⟨⟨[(4, 4), (3, 3)], by simp⟩, rfl⟩

example : ∃ p : ColorCompAllowed 3 7, p.val = [(7, 3)] :=
  ⟨⟨[(7, 3)], by simp⟩, rfl⟩
