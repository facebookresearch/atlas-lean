/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for `MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing` -/

open MathlibExt.Probability.Finance.FundamentalTheoremAssetPricing

namespace MathlibExtTest.FundamentalTheoremAssetPricing

/-- Complete market on two states with one risky asset (`g = ![1, -1]`): the normalized
state-price vector `![1/2, 1/2]` is unique. -/
example : ∃! q : Fin 2 → ℝ, (∀ ω, 0 < q ω) ∧ ∑ ω, q ω = 1 ∧
    ∀ a : Unit, ∑ ω, q ω * (fun (_ : Unit) => ![(1 : ℝ), -1]) a ω = 0 := by
  refine (one_period_second_fundamental_theorem_asset_pricing
    (fun (_ : Unit) => ![(1 : ℝ), -1]) ?_).mp ?_
  · refine (one_period_fundamental_theorem_asset_pricing_general
      (fun (_ : Unit) => ![(1 : ℝ), -1])).mpr ⟨![1/2, 1/2], ?_, ?_, ?_⟩
    · rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor <;> norm_num
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
    · intro a
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      norm_num
  · intro x
    refine ⟨(x 0 + x 1) / 2, fun _ => (x 0 - x 1) / 2, ?_⟩
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · simp only [Fintype.sum_unique, Matrix.cons_val_zero]
      ring
    · simp only [Fintype.sum_unique, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring

/-- Incomplete market: with zero gains, both `![1/2, 1/2]` and `![1/3, 2/3]` are normalized
state-price vectors, so uniqueness fails. -/
example : ¬ ∃! q : Fin 2 → ℝ, (∀ ω, 0 < q ω) ∧ ∑ ω, q ω = 1 ∧
    ∀ a : Unit, ∑ ω, q ω * (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) a ω = 0 := by
  have hvec : ∀ u v : ℝ, 0 < u → 0 < v → u + v = 1 →
      (∀ ω, 0 < (![u, v] : Fin 2 → ℝ) ω) ∧ (∑ ω, (![u, v] : Fin 2 → ℝ) ω = 1) ∧
      (∀ a : Unit, ∑ ω, (![u, v] : Fin 2 → ℝ) ω *
        (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) a ω = 0) := by
    intro u v hu hv huv
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hu, hv⟩
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact huv
    · intro a
      simp
  rintro ⟨q, hq, huniq⟩
  have h1 : (![1/2, 1/2] : Fin 2 → ℝ) = q :=
    huniq _ (hvec _ _ (by norm_num) (by norm_num) (by norm_num))
  have h2 : (![1/3, 2/3] : Fin 2 → ℝ) = q :=
    huniq _ (hvec _ _ (by norm_num) (by norm_num) (by norm_num))
  have hcon : (![1/2, 1/2] : Fin 2 → ℝ) 0 = (![1/3, 2/3] : Fin 2 → ℝ) 0 := by
    rw [h1, h2]
  simp only [Matrix.cons_val_zero] at hcon
  norm_num at hcon

/-- Converse direction: a zero-gain market with two states is not complete, because its
strictly positive normalized state price is not unique. -/
example : ¬ ∀ x : Fin 2 → ℝ, ∃ c : ℝ, ∃ h : Unit → ℝ, ∀ ω : Fin 2,
    x ω = c + ∑ a : Unit, h a * (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) a ω := by
  have hNA : ¬ ∃ h : Unit → ℝ,
      (∀ ω : Fin 2, 0 ≤ ∑ a : Unit, h a * (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) a ω) ∧
      (∃ ω : Fin 2, 0 < ∑ a : Unit, h a * (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) a ω) := by
    rintro ⟨h, -, ⟨ω, hpos⟩⟩
    simp at hpos
  have hvec : ∀ u v : ℝ, 0 < u → 0 < v → u + v = 1 →
      (∀ ω, 0 < (![u, v] : Fin 2 → ℝ) ω) ∧ (∑ ω, (![u, v] : Fin 2 → ℝ) ω = 1) ∧
      (∀ a : Unit, ∑ ω, (![u, v] : Fin 2 → ℝ) ω *
        (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) a ω = 0) := by
    intro u v hu hv huv
    refine ⟨?_, ?_, ?_⟩
    · rw [Fin.forall_fin_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hu, hv⟩
    · rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact huv
    · intro a
      simp
  have hNonuniq : ¬ ∃! q : Fin 2 → ℝ, (∀ ω, 0 < q ω) ∧ ∑ ω, q ω = 1 ∧
      ∀ a : Unit, ∑ ω, q ω * (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) a ω = 0 := by
    rintro ⟨q, hq, huniq⟩
    have h1 : (![1/2, 1/2] : Fin 2 → ℝ) = q :=
      huniq _ (hvec _ _ (by norm_num) (by norm_num) (by norm_num))
    have h2 : (![1/3, 2/3] : Fin 2 → ℝ) = q :=
      huniq _ (hvec _ _ (by norm_num) (by norm_num) (by norm_num))
    have hcon : (![1/2, 1/2] : Fin 2 → ℝ) 0 = (![1/3, 2/3] : Fin 2 → ℝ) 0 := by
      rw [h1, h2]
    simp only [Matrix.cons_val_zero] at hcon
    norm_num at hcon
  intro hComplete
  exact hNonuniq ((one_period_second_fundamental_theorem_asset_pricing
    (fun (_ : Unit) (_ : Fin 2) => (0 : ℝ)) hNA).mp hComplete)

end MathlibExtTest.FundamentalTheoremAssetPricing
