/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Preference.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Sort

@[expose] public section

/-!
# Ordinal utility representation of a finite preference (Atlas EC01.T02)

Source: J. Levin and P. Milgrom, *Introduction to Choice Theory*, Stanford Econ 202 notes (2004),
§4 (Utility): Definition 5 (`u` represents `≿` iff `x ≿ y ↔ u(x) ≥ u(y)`) and Proposition 3
(if `X` is finite, every complete and transitive preference relation on `X` is represented by
some `u : X → ℝ`).

On a finite set of alternatives, the cardinalities of weak lower contours give a direct
non-inductive construction of an ordinal utility representation with natural-number values.
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

/-- For a preference `P` on a finite set of alternatives, the weak lower-contour count at `x`
is the number of alternatives `y` such that `P.R x y`. It includes `x` itself and every
alternative indifferent to `x`. -/
noncomputable def lowerContourCount {α : Type*} [Finite α] (P : Preference α) (x : α) : ℕ :=
  (Set.toFinite {y | P.R x y}).toFinset.card

/-- The weak lower-contour count, cast from `ℕ` to `ℝ`, represents a finite preference:
`P.R x y` if and only if the count at `y` is at most the count at `x`.
In particular, indifferent alternatives have equal counts.

This is a direct, non-inductive construction of the finite representation result of
Levin–Milgrom, *Introduction to Choice Theory* (2004), Proposition 3. -/
theorem represents_lowerContourCount {α : Type*} [Finite α] (P : Preference α) :
    P.Represents (fun x => (P.lowerContourCount x : ℝ)) := by
  intro x y
  refine Iff.trans ?_ (Nat.cast_le (α := ℝ)).symm
  let lower (x : α) : Set α := {y | P.R x y}
  have lower_mono {x y : α} (h : P.R x y) : lower y ⊆ lower x := fun _ hz => P.trans h hz
  refine ⟨fun h => Finset.card_le_card (Set.Finite.toFinset_mono (lower_mono h)), ?_⟩
  intro hcard
  by_contra hxy
  have hyx := (P.complete x y).resolve_left hxy
  have hy : y ∈ lower y := (P.complete y y).elim id id
  have hproper : lower x ⊂ lower y :=
    lt_of_le_not_ge (lower_mono hyx) (fun hsub => hxy (hsub hy))
  exact (Finset.card_lt_card (Set.Finite.toFinset_strictMono hproper)).not_ge hcard

end Preference

end MathlibExt.Economics
