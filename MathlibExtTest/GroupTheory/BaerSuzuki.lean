/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.BaerSuzukiBinaryFinite
import Mathlib.Algebra.Group.ULift
import Mathlib.Data.Fintype.Perm

open MathlibExt.GroupTheory.BaerSuzukiWanted.GroupTheory

-- The two-element group, lifted out of `Type 0`, satisfies the criterion at `p = 2`.
example (x g : ULift.{1} (Equiv.Perm (Fin 2))) :
    x ∈ Defs.pCore 2 (ULift.{1} (Equiv.Perm (Fin 2))) ∧
      IsPGroup 2 (Subgroup.closure {x, g * x * g⁻¹}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG : IsPGroup 2 (ULift.{1} (Equiv.Perm (Fin 2))) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_congr Equiv.ulift, Nat.card_eq_fintype_card, Fintype.card_perm,
      Fintype.card_fin]
    rfl
  have hx := (baer_suzuki (p := 2) x).2 fun k ↦
    hG.to_subgroup (Subgroup.closure {x, k * x * k⁻¹})
  exact ⟨hx, (baer_suzuki x).1 hx g⟩
