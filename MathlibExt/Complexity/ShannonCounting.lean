/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card

/-!
# Shannon counting for Boolean functions

There are `2 ^ (2 ^ n)` Boolean functions of `n` variables, so
any descriptor class with fewer members fails to compute some
function. This is the counting core of Shannon's circuit
lower bound; the circuit model itself is not formalized here.
-/

@[expose] public section

/-- Shannon counting, core of MOD-49: there are `2 ^ (2 ^ n)`
Boolean functions of `n` variables. -/
theorem card_bool_functions (n : ℕ) :
    Fintype.card ((Fin n → Bool) → Bool) = 2 ^ (2 ^ n) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

/-- If a descriptor class has fewer than `2 ^ (2 ^ n)` members,
some Boolean function is not computed by any descriptor: most
functions need large circuits. -/
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

end
