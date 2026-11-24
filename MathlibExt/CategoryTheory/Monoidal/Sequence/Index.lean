/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# The additive natural-number monoidal index

This file packages the natural numbers under addition as a small discrete
symmetric monoidal category.  The `Multiplicative` tag makes addition the
multiplication used by the existing discrete monoidal structure and avoids
the competing multiplicative grading on raw `Discrete ℕ`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Sequence

/-- The small discrete monoidal category of natural degrees under addition. -/
abbrev Index := Discrete (Multiplicative ℕ)

/-- Regard a natural number as an object of the sequence index. -/
def index (n : ℕ) : Index := ⟨Multiplicative.ofAdd n⟩

/-- Recover the natural degree of an index object. -/
def degree (i : Index) : ℕ := i.as.toAdd

@[simp]
theorem degree_index (n : ℕ) : degree (index n) = n := rfl

@[simp]
theorem index_degree (i : Index) : index (degree i) = i := by
  cases i
  rfl

@[simp]
theorem tensorUnit_eq_index_zero : (𝟙_ Index) = index 0 := rfl

@[simp]
theorem tensorObj_index (m n : ℕ) :
    index m ⊗ index n = index (m + n) := rfl

/-- The unique discrete braiding is symmetric.  The instance is scoped so
importing the additive index does not alter unrelated instance search. -/
noncomputable scoped instance instSymmetricCategory : SymmetricCategory Index where
  symmetry _ _ := Subsingleton.elim _ _

end CategoryTheory.Sequence
