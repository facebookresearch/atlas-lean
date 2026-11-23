/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.Satisfiability

/-!
# Tests for LTL satisfiability by Büchi nonemptiness

Kernel-checked runs of the executable test on satisfiable and unsatisfiable formulas over the
alphabet `Bool`, with infinitely many atoms, and a validity consequence.
-/

@[expose] public section

namespace Cslib.LTL.SatisfiabilityTests

/-- Atom 0 holds on `true`, atom 1 on `false`, and all other atoms are false. -/
def val (x : Bool) (a : ℕ) : Prop :=
  if a = 0 then x = true else if a = 1 then x = false else False

instance : ∀ x a, Decidable (val x a) := fun x a =>
  inferInstanceAs (Decidable (if a = 0 then x = true else if a = 1 then x = false else False))

example : satB val (.atom 0 : Formula ℕ) = true := by decide +kernel

example : satB val (.and (.atom 0) (.not (.atom 0)) : Formula ℕ) = false := by decide +kernel

/-- Atom 2 is false on every letter, so `F (atom 2)` is unsatisfiable. -/
example : satB val (Formula.eventually (.atom 2) : Formula ℕ) = false := by decide +kernel

example : satB val (.until (.atom 0) (.atom 1) : Formula ℕ) = true := by decide +kernel

example : Satisfiable val (.until (.atom 0) (.atom 1) : Formula ℕ) :=
  (satB_iff val _).mp (by decide +kernel)

/-- `¬(atom 2)` is valid for this valuation. -/
example : Valid val (.not (.atom 2) : Formula ℕ) := by
  rw [valid_iff_not_satisfiable_not, ← satB_iff]
  decide +kernel

end Cslib.LTL.SatisfiabilityTests
