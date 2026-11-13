/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Preorder.Finite

@[expose] public section

/-!
# Preferences, choice, and greatest elements (Atlas EC01.T01)

Source: J. Levin and P. Milgrom, *Introduction to Choice Theory*, Stanford Econ 202 notes (2004),
§2: Definitions 1–2 (completeness, transitivity), strict preference and indifference, the choice
rule `C(B; ≿)`, and Proposition 1(1): for every finite nonempty `B`, `C(B; ≿) ≠ ∅`.

Atlas's `ExpectedUtility.IsPreferenceRelation` and `ExpectedUtility.StrictPref`
(`MathlibExt/Economics/ExpectedUtility/VonNeumannMorgenstern.lean`) are the same two notions
specialized to relations on lotteries `StdSimplex ℝ X`. Unifying them as instances of the generic
`Preference` here is future work; it would make the lottery file import this one, not conversely.
-/

namespace MathlibExt.Economics

namespace PreferenceRelation

/-- The strict part of an arbitrary weak preference relation. -/
def StrictPref {α : Type*} (R : α → α → Prop) (x y : α) : Prop :=
  R x y ∧ ¬ R y x

/-- The greatest elements of a menu under an arbitrary weak preference relation. -/
abbrev choice {α : Type*} (R : α → α → Prop) (B : Set α) : Set α :=
  {x | x ∈ B ∧ ∀ y ∈ B, R x y}

/-- The menu elements with no strictly preferred alternative in the menu. -/
def maximal {α : Type*} (R : α → α → Prop) (B : Set α) : Set α :=
  {x | x ∈ B ∧ ∀ y ∈ B, ¬ StrictPref R y x}

/-- Completeness alone makes maximal and greatest menu elements coincide. -/
theorem maximal_eq_choice {α : Type*} (R : α → α → Prop)
    (hcomplete : ∀ x y, R x y ∨ R y x) (B : Set α) :
    maximal R B = choice R B := by
  ext x
  simp only [maximal, choice, StrictPref, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hxB, hmax⟩
    refine ⟨hxB, fun y hyB => ?_⟩
    rcases hcomplete x y with h | h
    · exact h
    · by_contra hnx
      exact hmax y hyB ⟨h, hnx⟩
  · rintro ⟨hxB, hg⟩
    refine ⟨hxB, fun y hyB hstrict => ?_⟩
    exact hstrict.2 (hg y hyB)

end PreferenceRelation

/-- A rational preference relation on a set of alternatives `α` (Levin–Milgrom, *Introduction to
Choice Theory*, §2): `R x y` reads "`x` is at least as good as `y`" (`x ≿ y`). The relation is
complete (Definition 1) and transitive (Definition 2). -/
structure Preference (α : Type*) where
  /-- `R x y` means `x ≿ y`: `x` is at least as good as `y`. -/
  R : α → α → Prop
  /-- Completeness (Definition 1): for all `x y`, `x ≿ y` or `y ≿ x`, or both. -/
  complete : ∀ x y, R x y ∨ R y x
  /-- Transitivity (Definition 2): `x ≿ y` and `y ≿ z` imply `x ≿ z`. -/
  trans : ∀ {x y z}, R x y → R y z → R x z

namespace Preference

/-- Strict preference `x ≻ y`: `x ≿ y` but not `y ≿ x` (§2). -/
def StrictPref {α : Type*} (P : Preference α) (x y : α) : Prop :=
  PreferenceRelation.StrictPref P.R x y

/-- Indifference `x ∼ y`: `x ≿ y` and `y ≿ x` (§2). -/
def Indiff {α : Type*} (P : Preference α) (x y : α) : Prop :=
  P.R x y ∧ P.R y x

/-- The choice rule `C(B; ≿) = {x ∈ B | x ≿ y for all y ∈ B}` (§2): the greatest elements of the
menu `B`. -/
def choice {α : Type*} (P : Preference α) (B : Set α) : Set α :=
  PreferenceRelation.choice P.R B

/-- The maximal elements of the menu `B`: elements of `B` to which no element of `B` is strictly
preferred. For an arbitrary relation this is weaker than being greatest. -/
def maximal {α : Type*} (P : Preference α) (B : Set α) : Set α :=
  PreferenceRelation.maximal P.R B

/-- For a complete preference, maximal and greatest elements of a menu coincide. -/
theorem maximal_eq_choice {α : Type*} (P : Preference α) (B : Set α) :
    P.maximal B = P.choice B :=
  PreferenceRelation.maximal_eq_choice P.R P.complete B

/-- Levin–Milgrom, Proposition 1(1): a complete transitive preference has a greatest element on
every finite nonempty menu. -/
theorem choice_nonempty {α : Type*} (P : Preference α) {B : Set α} (hfin : B.Finite)
    (hne : B.Nonempty) : (P.choice B).Nonempty := by
  letI : LE α := ⟨fun a b => P.R b a⟩
  haveI : IsTrans α (· ≤ ·) := ⟨fun a b c h1 h2 => P.trans h2 h1⟩
  obtain ⟨x, hxB, hmax⟩ := hfin.exists_maximal hne
  exact ⟨x, hxB, fun y hyB => by
    rcases P.complete x y with h | h
    · exact h
    · exact hmax hyB h⟩

end Preference

end MathlibExt.Economics
