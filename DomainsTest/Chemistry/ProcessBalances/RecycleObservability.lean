/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.ProcessBalances.RecycleObservability
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Tests for the two-unit recycle flowsheet -/

open Chemistry.ProcessBalances MathlibExt.LinearAlgebra

private abbrev feed : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
private abbrev onward : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 1
private abbrev recycle : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 2
private abbrev product : (Fin 4 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 3
private abbrev balances := (feed + recycle - onward).prod (onward - recycle - product)
private abbrev meters := feed.prod product
private abbrev readings := balances.prod meters
private abbrev direction : Fin 4 → ℝ := ![0, 1, 1, 0]

-- The feed meter fixes the feed on the fiber through any reference flow.
example (x₀ : Fin 4 → ℝ) :
    ∀ x, readings x = readings x₀ → feed x = feed x₀ := by
  apply (flowsheet_observability balances meters feed (x₀ := x₀) rfl).2.mpr
  intro v hv
  exact LinearMap.mem_ker.mpr (congrArg (fun d => d.2.1) (LinearMap.mem_ker.mp hv))

-- The flow (1, 2, 1, 1) satisfies both balances. A negative perturbation of the
-- recycle and onward flows keeps all streams positive without changing the readings.
example :
    let x : Fin 4 → ℝ := ![1, 2, 1, 1]
    let y := x + (-1 / 2 : ℝ) • direction
    balances x = (0, 0) ∧ (∀ i, 0 < y i) ∧ readings y = readings x ∧
      recycle y ≠ recycle x ∧ Function.Injective (readings.prod recycle) := by
  intro x y
  have hx (i : Fin 4) : 0 < x i := by
    fin_cases i <;> norm_num [x]
  have hsmall : |(-1 / 2 : ℝ)| < min (x 1) (x 2) := by
    norm_num [x, abs_of_neg (show (-1 / 2 : ℝ) < 0 by norm_num), lt_min_iff]
  obtain ⟨hpos, hsame, hchange⟩ := two_unit_recycle_observability.2.2.1 x (-1 / 2) hx hsmall
  refine ⟨?_, hpos, hsame, hchange (by norm_num), two_unit_recycle_observability.2.2.2⟩
  norm_num [balances, feed, recycle, onward, product, x, LinearMap.coe_prod,
    Function.prod_apply, LinearMap.add_apply, LinearMap.sub_apply]
