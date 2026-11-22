/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Complexity.FoolingSet

/-!
# Tests for fooling sets

* The empty set is a 1-fooling set for any `f`.
* For equality on `Fin 2`, the diagonal `{(0, 0), (1, 1)}` is a 1-fooling set, the two
  singleton diagonal rectangles are monochromatic-1 and cover it, and `fooling_card_le`
  gives `2 ≤ 2`: the bound is attained.
* `eq_of_mem_rect` rules out a monochromatic-1 rectangle containing both diagonal elements.
* For the constant `true` function the diagonal is not a 1-fooling set.
-/

@[expose] public section

namespace Cslib.Complexity.FoolingSetTests

open Cslib.Complexity.FoolingSet

/-- The empty set is a 1-fooling set for any `f`. -/
example (f : Fin 2 × Fin 2 → Bool) : IsFooling f ∅ := by
  constructor
  · intro p hp
    simp at hp
  · intro p hp
    simp at hp

/-- Equality on `Fin 2`. -/
def eqFn : Fin 2 × Fin 2 → Bool := fun p => decide (p.1 = p.2)

/-- The diagonal of `Fin 2 × Fin 2`. -/
def diag : Finset (Fin 2 × Fin 2) := {(0, 0), (1, 1)}

/-- The two singleton rectangles on the diagonal, as side pairs. -/
def diagRects : List (Finset (Fin 2) × Finset (Fin 2)) := [({0}, {0}), ({1}, {1})]

/-- The diagonal is a 1-fooling set for equality: both crossed inputs `(0, 1)` and `(1, 0)`
have value `false`. -/
theorem diag_isFooling : IsFooling eqFn diag := by
  unfold IsFooling eqFn diag
  decide

/-- Each diagonal rectangle is monochromatic-1 for equality. -/
theorem diagRects_mono : ∀ r ∈ diagRects, RectMono eqFn r.1 r.2 := by
  unfold RectMono eqFn diagRects
  decide

/-- The diagonal rectangles cover the diagonal. -/
theorem diagRects_cover : ∀ p ∈ diag, ∃ r ∈ diagRects, p.1 ∈ r.1 ∧ p.2 ∈ r.2 := by
  unfold diag diagRects
  decide

/-- The fooling-set bound for the diagonal and the diagonal rectangles. -/
example : diag.card ≤ diagRects.length :=
  fooling_card_le eqFn diag diag_isFooling diagRects diagRects_mono diagRects_cover

/-- The bound is attained: both sides are `2`. -/
example : diag.card = 2 ∧ diagRects.length = 2 := by
  decide

/-- No monochromatic-1 rectangle for equality contains both diagonal elements, so
`eq_of_mem_rect` rules out `{0, 1} ×ˢ {0, 1}`. -/
example : ¬ RectMono eqFn {0, 1} {0, 1} := fun h =>
  absurd (diag_isFooling.eq_of_mem_rect h (p := (0, 0)) (q := (1, 1)) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) (by decide)

/-- For the constant `true` function the diagonal is not a 1-fooling set: its crossed
inputs `(0, 1)` and `(1, 0)` have value `true`. -/
example : ¬ IsFooling (fun _ : Fin 2 × Fin 2 => true) diag := by
  unfold IsFooling diag
  decide

end Cslib.Complexity.FoolingSetTests
