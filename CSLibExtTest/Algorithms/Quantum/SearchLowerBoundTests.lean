/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.SearchLowerBound

@[expose] public section

/-!
# Tests for the hybrid argument and the quantum search lower bound

The hypotheses of `card_le_of_forall_success` are jointly satisfiable: with one item, no
workspace beyond a single state and no query, the identity algorithm started at the basis
state `|0, 0⟩` finds the item with probability one. The tests also check the corollary that a
zero-query algorithm cannot search more than four items.
-/

namespace Cslib.QuantumSearchLowerBound.Tests

open Finset

/-- The basis state `|(), ()⟩` of `ℓ²(Unit × Unit)`. -/
noncomputable def e₀ : EuclideanSpace ℂ (Unit × Unit) := EuclideanSpace.single ((), ()) 1

theorem norm_e₀ : ‖e₀‖ = 1 := by simp [e₀]

/-- The hypotheses of the concrete lower bound hold for the trivial search over one item. -/
example : ∀ y : Unit, (1 / 2 : ℝ) ≤
    ∑ w : Unit,
      ‖queryRun (fun _ => LinearIsometry.id) (markingOracle (W := Unit) y) e₀ 0 (y, w)‖ ^ 2 := by
  intro y
  simp [queryRun, e₀]
  norm_num

example : (Fintype.card Unit : ℝ) ≤ 16 * (0 : ℕ) ^ 2 + 4 :=
  card_le_of_forall_success (W := Unit) (fun _ => LinearIsometry.id) e₀ norm_e₀ 0 (fun y => by
    simp [queryRun, e₀]
    norm_num)

/-- With no query, an algorithm that finds every item with probability `≥ 1/2` has at most four
items. -/
example {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W]
    (U : ℕ → EuclideanSpace ℂ (ι × W) →ₗᵢ[ℂ] EuclideanSpace ℂ (ι × W))
    (ψ₀ : EuclideanSpace ℂ (ι × W)) (hψ₀ : ‖ψ₀‖ = 1)
    (hsucc : ∀ y, 1 / 2 ≤ ∑ w, ‖queryRun U (markingOracle y) ψ₀ 0 (y, w)‖ ^ 2) :
    Fintype.card ι ≤ 4 := by
  have := card_le_of_forall_success U ψ₀ hψ₀ 0 hsucc
  norm_num at this
  exact_mod_cast this

end Cslib.QuantumSearchLowerBound.Tests
