/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EvenFibonacciAccessibility

open MetaMathlibExt

-- The definition also excludes a palette of size zero.
example (r : ℕ) : IsRAccessible r evenFibonacciSet ↔ r = 1 := by
  obtain ⟨hone, hmany⟩ := evenFibonacciSet_degreeOfAccessibility_eq_one
  constructor
  · intro h
    have := h.2.1
    by_contra hne
    exact hmany r (by omega) h
  · rintro rfl
    exact hone

-- At the first excluded palette size there is a coloring and a positive forbidden length.
example : ∃ (c : ℕ+ → Fin 2) (k : ℕ), 1 ≤ k ∧ ¬ ∃ x : Fin k → ℕ+,
    IsMonochromatic c x ∧ IsDDiffSequence evenFibonacciSet (fun i => ((x i : ℕ) : ℤ)) := by
  obtain ⟨hone, hmany⟩ := evenFibonacciSet_degreeOfAccessibility_eq_one
  by_contra! hall
  exact hmany 2 le_rfl ⟨hone.1, by decide, hall⟩

-- Two colors already block arbitrarily long monochromatic even Fibonacci diffsequences.
example : ¬ IsAccessible evenFibonacciSet :=
  fun h => even_fibonacci_not_two_accessible (h 2 (by decide))

-- Every set of gaps inside the even Fibonacci set, such as the single gap two, inherits the
-- obstruction.
example (D : Set ℕ) (hD : D ⊆ evenFibonacciSet) : ¬ IsRAccessible 2 D := by
  rintro ⟨-, -, h⟩
  refine even_fibonacci_not_two_accessible ⟨?_, by decide, fun c k hk => ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact Nat.fib_pos.mpr (by omega)
  · obtain ⟨x, hx, hdiff⟩ := h c k hk
    exact ⟨x, hx, fun i hi => (hdiff i hi).imp fun d hd => ⟨hD hd.1, hd.2⟩⟩

-- The obstruction applies at the four-color boundary and to larger palettes.
example : ¬ IsRAccessible 4 positiveFibonacciSet :=
  fibonacciSet_degreeOfAccessibility_le_three.1 4 le_rfl

example : ¬ IsRAccessible 7 positiveFibonacciSet :=
  fibonacciSet_degreeOfAccessibility_le_three.1 7 (by decide)

-- A single coloring works for all four-term progressions of step two, of either parity.
example : ∃ c : ℕ+ → Fin 4, ∀ a : ℕ+, ¬ IsMonochromatic c
    (fun i : Fin 4 => ⟨(a : ℕ) + 2 * (i : ℕ), Nat.add_pos_left a.pos _⟩) := by
  obtain ⟨c, hc⟩ := fibonacciSet_degreeOfAccessibility_le_three.2
  refine ⟨c, fun a hmono => hc ⟨_, hmono, ?_⟩⟩
  intro i hi
  refine ⟨2, ⟨3, by decide, by decide⟩, ?_⟩
  simp only [PNat.mk_coe, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega
