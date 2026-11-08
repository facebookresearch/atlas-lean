/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.Order.DenseLinearOrder
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace MathlibExtTest.SetTheory.Order.DenseLinearOrder

open MetaMathlibExt

-- Logic 20: Dense linear order without endpoints

/- Check A (positive, exercises all four clauses): `ℚ` is a DLO without endpoints. -/

example : IsDenseLinearOrderWithoutEndpoints (· < · : ℚ → ℚ → Prop) := by
  refine ⟨inferInstance, fun a b h => exists_between h, ?_, ?_⟩
  · exact fun a => ⟨a - 1, by linarith⟩
  · exact fun a => ⟨a + 1, by linarith⟩

/- Check B (negative): `ℕ` is not — it has a least element. -/

example : ¬ IsDenseLinearOrderWithoutEndpoints (· < · : ℕ → ℕ → Prop) := by
  rintro ⟨-, -, hmin, -⟩
  obtain ⟨b, hb⟩ := hmin 0
  exact absurd hb (Nat.not_lt_zero b)

end MathlibExtTest.SetTheory.Order.DenseLinearOrder

end
