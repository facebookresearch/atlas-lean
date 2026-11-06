/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite group order bounds from an actual orbit injection and its actual stabilizer. -/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- An actual finite orbit injection bounds the group order by candidate and stabilizer orders. -/
theorem y322FiniteAction_card_le_of_orbit {G X Y : Type*} [Group G]
    [MulAction G X] [Finite Y] (point : X) (candidate : MulAction.orbit G point → Y)
    (injective : Function.Injective candidate) :
    Nat.card G ≤ Nat.card Y * Nat.card (MulAction.stabilizer G point) := by
  have h : Nat.card (MulAction.orbit G point) * Nat.card (MulAction.stabilizer G point) =
      Nat.card G := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G point)
  rw [← h]
  exact Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective candidate injective)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
