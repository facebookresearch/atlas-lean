/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Elementary consequences of the independent Y₅₅₅ presentation.
These do not assume the Ivanov–Norton recognition theorem.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every tree generator is an involution, directly from its defining relator. -/
theorem y555_generator_sq (v : Y555Vertex) :
    (PresentedGroup.of v : BimonsterPresentation) ^ 2 = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y555Relations)
    (show FreeGroup.of v ^ 2 ∈ y555Relations from Or.inl ⟨v, rfl⟩)
  simpa only [map_pow, PresentedGroup.of] using h

/-- The defining Coxeter relation for distinct vertices. -/
theorem y555_coxeter_relation (u v : Y555Vertex) (huv : u ≠ v) :
    ((PresentedGroup.of u : BimonsterPresentation) * PresentedGroup.of v) ^
      (if y555Adjacent u v then 3 else 2 : ℕ) = 1 := by
  have h := PresentedGroup.one_of_mem (rels := y555Relations)
    (show (FreeGroup.of u * FreeGroup.of v) ^
        (if y555Adjacent u v then 3 else 2 : ℕ) ∈ y555Relations from
      Or.inr (Or.inl ⟨u, v, huv, rfl⟩))
  simpa only [map_pow, map_mul, PresentedGroup.of] using h

/-- Send each generator to the nonzero element of the two-element group. -/
def y555GeneratorParity (_ : Y555Vertex) : Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd 1

theorem y555Parity_relations (r : FreeGroup Y555Vertex) (hr : r ∈ y555Relations) :
    FreeGroup.lift y555GeneratorParity r = 1 := by
  rcases hr with ⟨v, rfl⟩ | ⟨u, v, _, rfl⟩ | rfl
  · simp only [map_pow, FreeGroup.lift_apply_of, y555GeneratorParity]
    decide
  · simp only [map_pow, map_mul, FreeGroup.lift_apply_of, y555GeneratorParity]
    have h : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by
      decide
    rw [h, one_pow]
  · simp only [map_pow, y555Spider, map_mul, FreeGroup.lift_apply_of,
      y555GeneratorParity]
    decide

/-- The parity quotient of the presented group, obtained without recognition. -/
def bimonsterParity : BimonsterPresentation →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup y555Parity_relations

@[simp] theorem bimonsterParity_generator (v : Y555Vertex) :
    bimonsterParity (PresentedGroup.of v) = Multiplicative.ofAdd 1 :=
  PresentedGroup.toGroup.of y555Parity_relations

@[simp] theorem bimonsterSwap_sq : bimonsterSwap ^ 2 = 1 :=
  y555_generator_sq none

@[simp] theorem bimonsterParity_swap :
    bimonsterParity bimonsterSwap = Multiplicative.ofAdd 1 :=
  bimonsterParity_generator none

/-- The parity quotient is onto; it is not the trivial homomorphism. -/
theorem bimonsterParity_surjective : Function.Surjective bimonsterParity := by
  intro x
  have h : Multiplicative.toAdd x = 0 ∨ Multiplicative.toAdd x = 1 := by
    generalize Multiplicative.toAdd x = z
    fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
  rcases h with h | h
  · refine ⟨1, ?_⟩
    rw [map_one]
    exact (Multiplicative.toAdd.injective h).symm
  · refine ⟨bimonsterSwap, ?_⟩
    rw [bimonsterParity_swap]
    exact (Multiplicative.toAdd.injective h).symm

/-- The distinguished involution is nonidentity in the actual quotient presentation. -/
theorem bimonsterSwap_ne_one : bimonsterSwap ≠ 1 := by
  intro h
  have hp := congrArg bimonsterParity h
  simp only [bimonsterParity_swap, map_one] at hp
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 2) ≠ 1) hp

/-- The distinguished generator has order exactly two, without identifying the group. -/
theorem bimonsterSwap_orderOf : orderOf bimonsterSwap = 2 :=
  orderOf_eq_prime bimonsterSwap_sq bimonsterSwap_ne_one

/-- The subgroup removed from the centralizer really has two elements. -/
theorem bimonsterSwapPowers_card : Nat.card bimonsterSwapPowers = 2 := by
  rw [bimonsterSwapPowers, Nat.card_zpowers]
  apply orderOf_eq_prime
  · apply Subtype.ext
    exact bimonsterSwap_sq
  · intro h
    exact bimonsterSwap_ne_one (congrArg Subtype.val h)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
