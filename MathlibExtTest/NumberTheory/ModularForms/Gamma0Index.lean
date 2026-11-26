/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.Gamma0Index

@[expose] public section

open CongruenceSubgroup
open scoped MatrixGroups

/-- Consumer with the original binders: the index formula. -/
private theorem exactSource (N : ℕ) [NeZero N] :
    (CongruenceSubgroup.Gamma0 N).index = ArithmeticFunction.dedekindPsi N :=
  ModularCurve.Gamma0_index N

/-- Consumer with the original binders: the quotient cardinality formula. -/
private theorem exactSourceCard (N : ℕ) :
    Nat.card (𝒮ℒ ⧸ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)).subgroupOf 𝒮ℒ) =
      (CongruenceSubgroup.Gamma0 N).index :=
  ModularCurve.card_quotient_gamma0_eq_index N

example : (CongruenceSubgroup.Gamma0 2).index = 3 := by
  have h := ModularCurve.Gamma0_index 2
  rw [ArithmeticFunction.dedekindPsi_prime (by decide)] at h
  exact h

example : (CongruenceSubgroup.Gamma0 1).index = 1 := by
  have h := ModularCurve.Gamma0_index 1
  simpa using h

example : (CongruenceSubgroup.Gamma0 6).index = 12 := by
  have h := ModularCurve.Gamma0_index 6
  have hpsi : ArithmeticFunction.dedekindPsi 6 = 12 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num,
      ArithmeticFunction.isMultiplicative_dedekindPsi.map_mul_of_coprime (by decide),
      ArithmeticFunction.dedekindPsi_prime (by decide),
      ArithmeticFunction.dedekindPsi_prime (by decide)]
    norm_num
  rw [hpsi] at h
  exact h

/-- A level divisible by the square of a prime: `ψ(12) = ψ(2 ^ 2) * ψ(3) = 6 * 4 = 24`. -/
example : (CongruenceSubgroup.Gamma0 12).index = 24 := by
  have h := ModularCurve.Gamma0_index 12
  have hpsi : ArithmeticFunction.dedekindPsi 12 = 24 := by
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
      ArithmeticFunction.isMultiplicative_dedekindPsi.map_mul_of_coprime (by decide),
      ArithmeticFunction.dedekindPsi_prime_pow (p := 2) (k := 2) Nat.prime_two (by norm_num),
      ArithmeticFunction.dedekindPsi_prime (by decide)]
    norm_num
  rw [hpsi] at h
  exact h
