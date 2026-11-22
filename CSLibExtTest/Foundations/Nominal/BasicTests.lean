/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Foundations.Nominal.Basic

/-!
# Nominal sets: basic tests

Spot checks on `ℕ` atoms: transpositions compute, an atom's support is its
singleton, fresh atoms exist, and swapping two fresh atoms fixes an element.
Axiom audit follows.
-/

namespace CSLibExtTest.Foundations.Nominal.Basic

open Cslib.Nominal

example : (swap (0 : ℕ) 1 : FinPerm ℕ) • (0 : ℕ) = 1 := by
  rw [swap_smul, Equiv.swap_apply_left]

example : (swap (0 : ℕ) 1 : FinPerm ℕ) • (2 : ℕ) = 2 :=
  swap_smul_of_ne_of_ne (by decide) (by decide)

example : supp (0 : ℕ) = {0} := supp_atom 0

example : Fresh (5 : ℕ) (0 : ℕ) :=
  ⟨{0}, fun π h => h 0 (Finset.mem_singleton_self 0), by decide⟩

example : ∃ a : ℕ, Fresh a (0 : ℕ) := exists_fresh 0

example : (swap (5 : ℕ) 6 : FinPerm ℕ) • (0 : ℕ) = 0 :=
  swap_smul_of_fresh_fresh
    ⟨{0}, fun π h => h 0 (Finset.mem_singleton_self 0), by decide⟩
    ⟨{0}, fun π h => h 0 (Finset.mem_singleton_self 0), by decide⟩

#print axioms supp_atom
#print axioms swap_smul_of_fresh_fresh
#print axioms exists_least_support

end CSLibExtTest.Foundations.Nominal.Basic
