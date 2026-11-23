/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Nominal.Abstraction

/-!
# Nominal sets: atom-abstraction tests

Spot checks on `ℕ` atoms: abstraction is trivially equal at the same atom,
injective at the same atom, has the expected support, and a genuine
α-renaming: `abs 5 0 = abs 6 0`, since `0` is fixed by `swap 5 6` and `5`
is fresh for `0`. Axiom audit follows.
-/

namespace CSLibExtTest.Foundations.Nominal.Abstraction

open Cslib.Nominal

example (x : ℕ) : abs (0 : ℕ) x = abs 0 x := rfl

example (x y : ℕ) (h : abs (0 : ℕ) x = abs 0 y) : x = y := abs_eq_of_same_atom h

example (x : ℕ) : supp (abs (0 : ℕ) x) = (supp x).erase 0 := supp_abs 0 x

example : abs (5 : ℕ) (0 : ℕ) = abs 6 (0 : ℕ) := by
  rw [abs_eq_iff]
  refine Or.inr ⟨by decide, ?_, ?_⟩
  · exact ⟨{0}, fun π h => h 0 (Finset.mem_singleton_self 0), by decide⟩
  · exact swap_smul_of_ne_of_ne (by decide) (by decide)

#print axioms supp_abs
#print axioms abs_eq_of_same_atom

end CSLibExtTest.Foundations.Nominal.Abstraction
