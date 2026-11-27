/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.JosephusJosephusAddEqOfLe

/-!
# Tests for linear growth of the Josephus function

These tests apply `josephus_add_eq_of_le` with strict and equality bounds and
check that a further increment can wrap around.
-/

namespace MathlibExtTest.NumberTheory.JosephusJosephusAddEqOfLe

open MetaMathlibExt MathlibExt.NumberTheory.JosephusWanted

example : josephus 3 25 = 14 :=
  josephus_add_eq_of_le 3 21 4 (by decide) (by decide) (by decide)

example : josephus 2 15 = 15 :=
  josephus_add_eq_of_le 2 8 7 (by decide) (by decide) (by decide)

example : josephus 3 30 = 29 ∧ josephus 3 31 = 1 :=
  ⟨josephus_add_eq_of_le 3 21 9 (by decide) (by decide) (by decide), by decide⟩

end MathlibExtTest.NumberTheory.JosephusJosephusAddEqOfLe
