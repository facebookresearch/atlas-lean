/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Preference.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Ordinal utility representation of a finite preference (Atlas EC01.T02)

Source: J. Levin and P. Milgrom, *Introduction to Choice Theory*, Stanford Econ 202 notes (2004),
§4 (Utility): Definition 5 (`u` represents `≿` iff `x ≿ y ↔ u(x) ≥ u(y)`) and Proposition 3
(if `X` is finite, every complete and transitive preference relation on `X` is represented by
some `u : X → ℝ`).
-/

namespace MathlibExt.Economics

namespace Preference

/-- `u` represents `P` (Levin–Milgrom, Definition 5): `x ≿ y ↔ u x ≥ u y`. A representation is an
equivalence, not one direction of monotonicity. -/
def Represents {α : Type*} (P : Preference α) (u : α → ℝ) : Prop :=
  ∀ x y, P.R x y ↔ u y ≤ u x

/-- Levin–Milgrom, Proposition 3: every complete transitive preference on a finite set of
alternatives has a real-valued utility representation. -/
theorem exists_represents {α : Type*} [Finite α] (P : Preference α) :
    ∃ u : α → ℝ, P.Represents u := by
  classical
  letI : Preorder α :=
    { le := fun a b => P.R b a
      le_refl := fun a => (P.complete a a).elim id id
      le_trans := fun a b c hab hbc => P.trans hbc hab }
  haveI : Std.Total (· ≤ · : α → α → Prop) := ⟨fun a b => P.complete b a⟩
  letI : Fintype α := Fintype.ofFinite α
  haveI : Fintype (Antisymmetrization α (· ≤ ·)) := Quotient.fintype _
  let e := (Fintype.orderIsoFinOfCardEq (Antisymmetrization α (· ≤ ·)) rfl).symm
  refine ⟨fun x => ((e (toAntisymmetrization _ x)).val : ℝ), ?_⟩
  intro x y
  have h : (((e (toAntisymmetrization _ y)).val : ℝ) ≤
      ((e (toAntisymmetrization _ x)).val : ℝ)) ↔ y ≤ x :=
    Nat.cast_le.trans (Fin.le_iff_val_le_val.symm.trans
      (e.le_iff_le.trans toAntisymmetrization_le_toAntisymmetrization_iff))
  exact h.symm

end Preference

end MathlibExt.Economics
