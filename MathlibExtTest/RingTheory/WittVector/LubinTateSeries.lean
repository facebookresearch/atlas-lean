/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.WittVector.LubinTateSeries

@[expose] public section

open MvPowerSeries

/-- Consumer with the original binders. -/
example (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (τ : Type) [Finite τ] (c : τ → WittVector p k) :
    ∃! φ : MvPowerSeries τ (WittVector p k),
      MvPowerSeries.constantCoeff φ = 0 ∧
      (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) φ = c s) ∧
      MvPowerSeries.C (p : WittVector p k) * φ + φ ^ Fintype.card k =
        MvPowerSeries.subst
          (fun s => MvPowerSeries.C (p : WittVector p k) * MvPowerSeries.X s +
            MvPowerSeries.X s ^ Fintype.card k) φ :=
  WittVector.existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
    p k τ c

/-- Higher-universe consumer: the coefficient type `k` in `Type 1` and the
index type `τ` in `Type 1`. -/
example (p : ℕ) [Fact p.Prime] (k : Type 1) [Field k] [Fintype k] [CharP k p]
    (τ : Type 1) [Finite τ] (c : τ → WittVector p k) :
    ∃! φ : MvPowerSeries τ (WittVector p k),
      MvPowerSeries.constantCoeff φ = 0 ∧
      (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) φ = c s) ∧
      MvPowerSeries.C (p : WittVector p k) * φ + φ ^ Fintype.card k =
        MvPowerSeries.subst
          (fun s => MvPowerSeries.C (p : WittVector p k) * MvPowerSeries.X s +
            MvPowerSeries.X s ^ Fintype.card k) φ :=
  WittVector.existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
    p k τ c

/-- Boundary example: with no variables, the unique series is `0`, and the
prescribed linear condition is vacuous. -/
example (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
    (c : Empty → WittVector p k) :
    ∃! φ : MvPowerSeries Empty (WittVector p k),
      MvPowerSeries.constantCoeff φ = 0 ∧
      (∀ s, MvPowerSeries.coeff (Finsupp.single s 1) φ = c s) ∧
      MvPowerSeries.C (p : WittVector p k) * φ + φ ^ Fintype.card k =
        MvPowerSeries.subst
          (fun s => MvPowerSeries.C (p : WittVector p k) * MvPowerSeries.X s +
            MvPowerSeries.X s ^ Fintype.card k) φ :=
  WittVector.existsUnique_mvPowerSeries_coeff_single_eq_and_C_mul_add_pow_card_eq_subst
    p k Empty c
