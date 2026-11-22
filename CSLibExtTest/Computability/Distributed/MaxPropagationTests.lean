/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.MaxPropagation
public import Mathlib.Data.Fin.VecNotation

/-!
# Tests for synchronous maximum propagation

* A ring of four nodes with the predecessor map `pred4` and the values `3, 7, 1, 5`: the explicit
  states after one, two and three rounds, the window formula `maxStep_iterate_apply` at one node,
  and `maxStep_iterate_eq_sup` with an explicit orbit-coverage proof, so that after four rounds
  every node holds `7`.
* A one-node ring: after one round the only node keeps its value, which is the maximum.
* The orbit hypothesis is needed: with `ρ = id` on two nodes, the values never move, and after
  two rounds node `0` still holds `1` while the maximum is `2`.
-/

@[expose] public section

namespace Cslib.Distributed.MaxPropagation.Tests

/-- The predecessor map on a ring of four nodes. -/
def pred4 (i : Fin 4) : Fin 4 := i - 1

/-- Nonconstant values on the four-node ring. -/
def v4 : Fin 4 → ℕ := ![3, 7, 1, 5]

/-- After one round each node holds the maximum of itself and its predecessor. -/
example : (maxStep pred4)^[1] v4 = ![5, 7, 7, 5] := by decide

/-- After two rounds the maximum `7` has moved two steps, to nodes `1`, `2` and `3`. -/
example : (maxStep pred4)^[2] v4 = ![5, 7, 7, 7] := by decide

/-- After three rounds every node holds `7`. -/
example : (maxStep pred4)^[3] v4 = ![7, 7, 7, 7] := by decide

/-- The window formula at node `3` after two rounds: the maximum of the values at `3, 2, 1`. -/
example : ((maxStep pred4)^[2] v4) 3 = 7 := by
  rw [maxStep_iterate_apply]
  decide

/-- Explicit orbit coverage: from every node, every node is reached within four steps. -/
theorem pred4_covers : ∀ i j : Fin 4, ∃ k ≤ 4, pred4^[k] i = j := by decide

/-- After four rounds every node holds the maximum `7`, by `maxStep_iterate_eq_sup`. -/
example : ∀ i, ((maxStep pred4)^[4] v4) i = 7 := by
  intro i
  rw [maxStep_iterate_eq_sup pred4 v4 pred4_covers i]
  decide

/-- A one-node ring: after one round the only node holds the maximum of all values. -/
example (ρ : Fin 1 → Fin 1) (v : Fin 1 → ℕ) :
    ((maxStep ρ)^[1] v) 0 = Finset.univ.sup v :=
  maxStep_iterate_eq_sup ρ v (fun _ _ => ⟨0, Nat.zero_le 1, Subsingleton.elim _ _⟩) 0

/-- Without orbit coverage the maximum need not spread: with `ρ = id` on two nodes, node `0`
still holds `1` after two rounds, while the maximum value is `2`. -/
example : ((maxStep (id : Fin 2 → Fin 2))^[2] ![1, 2]) 0 = 1 ∧
    Finset.univ.sup (![1, 2] : Fin 2 → ℕ) = 2 := by
  decide

end Cslib.Distributed.MaxPropagation.Tests
