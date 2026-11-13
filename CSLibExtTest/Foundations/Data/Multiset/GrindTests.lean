/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

/-
Copied from CslibTests/MultisetGrind.lean, leanprover/cslib PR944,
a69a43dca61ead87b6a631854de017ddaa310e08.
Import and module visibility are adapted; the test proofs are unchanged.
-/

module

public import CSLibExt.Foundations.Data.Multiset.Grind

/-! # Tests for the multiset grind set

These examples use arbitrary element types, without decidable equality or CLL-specific rules.
-/

@[expose] public section

variable {α : Type*} {a b : α} {Γ Δ Θ : Multiset α}

-- The AC solver handles addition without any theorem-matching rules.
example : (Γ + Δ) + (Γ + Θ) = Γ + Γ + (Δ + Θ) := by grind only

example (h : Θ = Γ + Δ) : Δ + Γ + 0 = Θ := by grind only

-- Exchange and cancellation, with the common occurrence in different positions.
example (h : a ::ₘ Γ = Δ + {a}) : Γ = Δ := by grind only [multiset]

-- Combining context equations while preserving repeated occurrences.
example (hΓ : Γ = a ::ₘ Θ) (hΔ : Δ = b ::ₘ Θ) :
    Γ + Δ = a ::ₘ b ::ₘ (Θ + Θ) := by grind only [multiset]

-- Mixed list and multiset representations, including appended lists.
example (Γ Δ : List α) :
    ((a :: Γ ++ b :: Δ : List α) : Multiset α) = b ::ₘ a ::ₘ ((Γ : Multiset α) + Δ) := by
  grind only [multiset]

-- A remaining singleton after removing an empty tail.
example (hΓ : Γ = a ::ₘ Δ) (hΔ : Δ = 0) : Γ = {a} := by grind only [multiset]

-- Selected copies and the residual context can have different representations.
example (n : ℕ) (Γ Δ : List α)
    (h : (Δ : Multiset α) = Multiset.replicate n a + Γ) :
    (Δ : Multiset α) = (List.replicate n a ++ Γ : List α) := by grind only [multiset]
