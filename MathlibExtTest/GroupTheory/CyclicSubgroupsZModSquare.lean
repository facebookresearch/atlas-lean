/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.CyclicSubgroupsZModSquare

@[expose] public section

/-- The source statement, with its original binders. -/
private theorem exactSource (n : ℕ) [NeZero n] :
    Nat.card {H : AddSubgroup (ZMod n × ZMod n) // IsAddCyclic H ∧ Nat.card H = n}
      = ArithmeticFunction.dedekindPsi n :=
  ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi n

example : Nat.card {H : AddSubgroup (ZMod 6 × ZMod 6) // IsAddCyclic H ∧ Nat.card H = 6}
    = 12 := by
  have h := ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi 6
  rw [h]
  have h6 : ArithmeticFunction.dedekindPsi (2 * 3)
      = ArithmeticFunction.dedekindPsi 2 * ArithmeticFunction.dedekindPsi 3 :=
    ArithmeticFunction.isMultiplicative_dedekindPsi.map_mul_of_coprime (by decide)
  norm_num [show (6 : ℕ) = 2 * 3 by decide, h6,
    ArithmeticFunction.dedekindPsi_prime (by decide : Nat.Prime 2),
    ArithmeticFunction.dedekindPsi_prime (by decide : Nat.Prime 3)]

example : Nat.card (ProjectiveLine (ZMod 2)) = 3 := by
  rw [card_projectiveLine_zmod 2 (by decide)]
  exact ArithmeticFunction.dedekindPsi_prime (by decide)
