/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Shannon counting for Boolean functions

There are `2 ^ (2 ^ n)` Boolean functions of `n` variables, so any descriptor
class with fewer members fails to compute some function. This is the counting
step of Shannon's circuit lower bound (C. E. Shannon, "The synthesis of
two-terminal switching circuits", Bell System Technical Journal 28 (1949),
59-98). Circuits are not formalized here: a circuit-size lower bound also needs
an upper bound on the number of small circuits.
-/

@[expose] public section

namespace MathlibExt.Complexity.ShannonCounting

/-- There are `2 ^ (2 ^ n)` Boolean functions of `n` variables. -/
theorem card_bool_functions (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- If a descriptor class has fewer than `2 ^ (2 ^ n)` members, some Boolean
function of `n` variables is not `eval d` for any descriptor `d`. -/
theorem exists_not_computed {Desc : Type*} [Fintype Desc] (n : ℕ)
    (eval : Desc → ((Fin n → Bool) → Bool))
    (h : Fintype.card Desc < 2 ^ (2 ^ n)) :
    ∃ f, ∀ d, eval d ≠ f := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective eval := fun f => hcon f
  have hle := Fintype.card_le_of_surjective eval hsurj
  rw [card_bool_functions n] at hle
  omega

end MathlibExt.Complexity.ShannonCounting
