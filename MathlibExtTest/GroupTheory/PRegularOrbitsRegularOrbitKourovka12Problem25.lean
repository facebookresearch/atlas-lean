/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.PRegularOrbitsRegularOrbitKourovka12Problem25
import Mathlib.Algebra.Group.Subgroup.Finite

open MathlibExt.GroupTheory.PRegularOrbitsRegularOrbitKourovka12Problem25Wanted

-- Every prime can be avoided, even though every stabilizer order has a prime divisor.
example : ∃ (G X : Type) (_ : Group G) (_ : Finite G) (_ : MulAction G X),
    (∀ p : ℕ, p.Prime → ∃ x : X, (Nat.card (MulAction.stabilizer G x)).Coprime p) ∧
    (∀ x : X, ∃ p : ℕ, p.Prime ∧ p ∣ Nat.card (MulAction.stabilizer G x)) := by
  by_contra h
  apply pRegularOrbitsImplyRegularOrbit_refuted
  intro F _ _ V _ _ _ _ G _ _ _ _ _ _ hp
  by_contra hreg
  apply h
  refine ⟨G, V, inferInstance, inferInstance, inferInstance, hp, fun v ↦ ?_⟩
  exact Nat.exists_prime_and_dvd fun hcard ↦ hreg ⟨v, Subgroup.eq_bot_of_card_eq _ hcard⟩
