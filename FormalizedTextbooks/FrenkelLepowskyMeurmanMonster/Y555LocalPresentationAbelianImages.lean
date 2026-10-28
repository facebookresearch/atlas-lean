/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The literal connected odd Coxeter diagram has only two values in every abelian image. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationCoxeterRewrites
public import Mathlib.GroupTheory.Abelianization.Defs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- An adjacent braid and the defining squares identify generators in every abelian image. -/
theorem y322AbelianImage_adjacent {A : Type*} [CommGroup A] (f : Y322Presentation →* A)
    (u v : Fin 8) (h : y555Adjacent (y322Vertex u) (y322Vertex v)) :
    f (PresentedGroup.of u) = f (PresentedGroup.of v) := by
  have hu := congrArg f (y322Positive_generator_square u)
  have hv := congrArg f (y322Positive_generator_square v)
  have hb := congrArg f (y322Positive_generator_braid u v h)
  simp only [map_mul, map_one] at hu hv hb
  symm
  calc
    f (PresentedGroup.of v) = (f (PresentedGroup.of u) * f (PresentedGroup.of u)) *
        f (PresentedGroup.of v) := by rw [hu, one_mul]
    _ = f (PresentedGroup.of u) * f (PresentedGroup.of v) * f (PresentedGroup.of u) := by
      ac_rfl
    _ = f (PresentedGroup.of v) * f (PresentedGroup.of u) * f (PresentedGroup.of v) := hb
    _ = (f (PresentedGroup.of v) * f (PresentedGroup.of v)) * f (PresentedGroup.of u) := by
      ac_rfl
    _ = f (PresentedGroup.of u) := by rw [hv, one_mul]

/-- All eight literal local generators have the same image in an abelian group. -/
theorem y322AbelianImage_generator {A : Type*} [CommGroup A] (f : Y322Presentation →* A)
    (v : Fin 8) : f (PresentedGroup.of v) = f (PresentedGroup.of 0) := by
  have h10 := y322AbelianImage_adjacent f 1 0 (by decide)
  have h21 := y322AbelianImage_adjacent f 2 1 (by decide)
  have h32 := y322AbelianImage_adjacent f 3 2 (by decide)
  have h40 := y322AbelianImage_adjacent f 4 0 (by decide)
  have h54 := y322AbelianImage_adjacent f 5 4 (by decide)
  have h60 := y322AbelianImage_adjacent f 6 0 (by decide)
  have h76 := y322AbelianImage_adjacent f 7 6 (by decide)
  fin_cases v
  · rfl
  · exact h10
  · exact h21.trans h10
  · exact h32.trans (h21.trans h10)
  · exact h40
  · exact h54.trans h40
  · exact h60
  · exact h76.trans h60

/-- The literal presentation has at most two values under any homomorphism to an abelian group. -/
theorem y322AbelianImage_two_values {A : Type*} [CommGroup A] (f : Y322Presentation →* A)
    (x : Y322Presentation) : f x = 1 ∨ f x = f (PresentedGroup.of 0) := by
  have hs := congrArg f (y322Positive_generator_square 0)
  simp only [map_mul, map_one] at hs
  have hi : (f (PresentedGroup.of 0))⁻¹ = f (PresentedGroup.of 0) :=
    inv_eq_of_mul_eq_one_right hs
  induction x using PresentedGroup.induction_on with
  | H w =>
    induction w using FreeGroup.induction_on with
    | one => exact Or.inl (by simp)
    | of i => exact Or.inr (y322AbelianImage_generator f i)
    | inv_of i _ =>
      right
      change f ((PresentedGroup.of i : Y322Presentation)⁻¹) = f (PresentedGroup.of 0)
      rw [map_inv, y322AbelianImage_generator, hi]
    | mul a b ha hb =>
      simp only [map_mul]
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact Or.inl (by rw [ha, hb, one_mul])
      · exact Or.inr (by rw [ha, hb, one_mul])
      · exact Or.inr (by rw [ha, hb, mul_one])
      · exact Or.inl (by rw [ha, hb, hs])

/-- The abelianization of the actual original local presentation is finite of order at most two. -/
theorem y322Abelianization_finite_card :
    Finite (Abelianization Y322Presentation) ∧ Nat.card (Abelianization Y322Presentation) ≤ 2 := by
  let g : Bool → Abelianization Y322Presentation := fun b =>
    if b then Abelianization.of (PresentedGroup.of 0) else 1
  have hs : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H x =>
      rcases y322AbelianImage_two_values Abelianization.of x with h | h
      · exact ⟨false, h.symm⟩
      · exact ⟨true, h.symm⟩
  refine ⟨Finite.of_surjective g hs, ?_⟩
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_surjective g hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
