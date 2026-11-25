/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidAdmissibleWords

/-!
# Native free-group reduction preserves every original endpoint word

Every label contains its SAME original source, target and full arrow.
Deleting a native adjacent inverse-label pair preserves literal full
endpoint admissibility. Native reflexive-transitive reduction retains
those exact original endpoints, and the native reduced label word
therefore reconstructs an actual original signed path.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V]

/-- Complete original endpoint words split at every supplied native list boundary. -/
lemma Admissible.append_iff {x z : V} (A B : List (Labels V × Bool)) :
    Admissible V x (A ++ B) z ↔ ∃ y, Admissible V x A y ∧ Admissible V y B z := by
  induction A generalizing x with
  | nil =>
    constructor
    · intro h
      exact ⟨x, Admissible.nil x, h⟩
    · rintro ⟨y, hxy, h⟩
      cases hxy
      exact h
  | cons a A ih =>
    constructor
    · intro h
      cases h with
      | cons a L z h =>
        obtain ⟨y, hy, hz⟩ := ih.mp h
        exact ⟨y, Admissible.cons a A y hy, hz⟩
    · rintro ⟨y, hxy, hyz⟩
      cases hxy with
      | cons a A y h => exact Admissible.cons a (A ++ B) z (ih.mpr ⟨y, h, hyz⟩)

/-- Full endpoint admissibility at an original first label retains its source and remaining
target. -/
lemma Admissible.cons_iff {x y : V} (a : Labels V × Bool) (L : List (Labels V × Bool)) :
    Admissible V x (a :: L) y ↔ x = labelSource V a ∧ Admissible V (labelTarget V a) L y := by
  constructor
  · intro h
    cases h with
    | cons a L y h => exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact Admissible.cons a L y h

/-- Full endpoint admissibility at the empty original word retains its exact endpoint equality. -/
lemma Admissible.nil_iff (x y : V) : Admissible V x [] y ↔ x = y := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact Admissible.nil x

/-- Each original native inverse-label pair preserves its SAME literal source after full
traversal. -/
lemma admissible_inverse_pair_endpoint (a : Labels V) (b : Bool) {x y : V}
    (h : Admissible V x [(a, b), (a, !b)] y) : x = y := by
  have h₁ := (Admissible.cons_iff V (a, b) [(a, !b)]).mp h
  have h₂ := (Admissible.cons_iff V (a, !b) []).mp h₁.2
  have h₃ := (Admissible.nil_iff V _ _).mp h₂.2
  have he : labelSource V (a, b) = labelTarget V (a, !b) := by
    rcases a with ⟨s, t, f⟩
    cases b <;> rfl
  exact h₁.1.trans (he.trans h₃)

/-- EVERY actual native reduction step preserves full original source/target admissibility. -/
lemma admissible_of_redStep {x y : V} {L M : List (Labels V × Bool)}
    (hL : Admissible V x L y) (h : FreeGroup.Red.Step L M) : Admissible V x M y := by
  cases h with
  | @not A B a b =>
    obtain ⟨s, hs, ht⟩ := (Admissible.append_iff V A ((a, b) :: (a, !b) :: B)).mp hL
    obtain ⟨t, hst, hty⟩ := (Admissible.append_iff V [(a, b), (a, !b)] B).mp ht
    have he := admissible_inverse_pair_endpoint V a b hst
    subst t
    exact Admissible.append V hs hty

/-- The complete actual native reduction relation retains the SAME original endpoints. -/
lemma admissible_of_red {x y : V} {L M : List (Labels V × Bool)}
    (hL : Admissible V x L y) (h : FreeGroup.Red L M) : Admissible V x M y := by
  induction h with
  | refl => exact hL
  | tail h hs ih => exact admissible_of_redStep V ih hs

/-- The actual native reduced label word has a complete original signed path
with the SAME original individual source and target vertices. -/
theorem reducedWord_admissible {x y : V} {L : List (Labels V × Bool)} (h : Admissible V x L y) :
    Admissible V x (@FreeGroup.reduce (Labels V) (Classical.decEq _) L) y := by
  classical
  exact admissible_of_red V h (@FreeGroup.reduce.red (Labels V) L (Classical.decEq _))

end Quiver.FreeGroupoid.OriginalWords
