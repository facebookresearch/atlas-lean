/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Algebra.Group.Hom.Defs

/-! Finite ordered word chains carry a sequence through its exact successive actions. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- A chronological chain accumulates each new group factor on the left. -/
def generatedAxisGlobalWordChain {G : Type*} [Monoid G] (e : ℕ → G) : ℕ → G
  | 0 => 1
  | n + 1 => e n * generatedAxisGlobalWordChain e n

/-- A checked finite sequence of actions identifies the action of its full literal word. -/
theorem generatedAxisGlobalWordChain_action {G X : Type*} [Monoid G] [MulAction G X]
    (e : ℕ → G) (u : ℕ → X) (n : ℕ)
    (hs : ∀ j, j < n → e j • u j = u (j + 1)) :
    generatedAxisGlobalWordChain e n • u 0 = u n := by
  induction n with
  | zero => simp [generatedAxisGlobalWordChain]
  | succ n ih =>
    rw [generatedAxisGlobalWordChain, mul_smul, ih (fun j hj => hs j (by omega))]
    exact hs n (by omega)

/-- A group homomorphism transports every factor of the same chronological word. -/
theorem generatedAxisGlobalWordChain_map {G K : Type*} [Monoid G] [Monoid K]
    (f : G →* K) (e : ℕ → G) (n : ℕ) :
    f (generatedAxisGlobalWordChain e n) =
      generatedAxisGlobalWordChain (fun j => f (e j)) n := by
  induction n with
  | zero => exact f.map_one
  | succ n ih => rw [generatedAxisGlobalWordChain, map_mul, ih, generatedAxisGlobalWordChain]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
