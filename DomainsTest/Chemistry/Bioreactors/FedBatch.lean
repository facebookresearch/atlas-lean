/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.Bioreactors.FedBatch
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Tests for the fed-batch bioreactor balances: an explicit solution with a sterile inoculum
(`X = 0`) fed at a constant rate, as a non-vacuity witness of the account theorem; and a
constant solution with negative substrate, which shows that `S(0) ≥ 0` cannot be dropped. -/

open Set Chemistry.Bioreactors.FedBatch
open MathlibExt.Biology.Dynamics.MichaelisMenten (mmRate)

namespace DomainsTest.Chemistry.Bioreactors.FedBatch

/-- With `V(0) = 1`, `F = 1`, `S_in = 2`, `S(0) = 0` and no biomass, the reactor fills linearly,
`V(t) = 1 + t`, and the substrate mixes in as `S(t) = 2 t / (1 + t)`, for any Monod rate and
yield. -/
theorem sterileFeed_isSolution (μm Ks Y : ℝ) :
    IsSolution (mmRate μm Ks) 2 Y (fun _ ↦ 1) (Ici 0) (fun t ↦ 1 + t)
      (fun t ↦ 2 * t / (1 + t)) (fun _ ↦ 0) where
  hasDerivWithinAt_volume t _ := ((hasDerivAt_id' t).const_add 1).hasDerivWithinAt
  hasDerivWithinAt_substrate t ht := by
    have ht' : (1 + t) ≠ 0 := by simp only [mem_Ici] at ht; linarith
    have h := ((hasDerivAt_id' t).const_mul 2).div ((hasDerivAt_id' t).const_add 1) ht'
    convert h.hasDerivWithinAt using 1
    field_simp
    ring
  hasDerivWithinAt_biomass t _ := by
    simpa using (hasDerivWithinAt_const t (Ici 0) (0 : ℝ))

/-- The account theorem applies to the sterile feed: the volume grows, the substrate stock
`V S = 2 t` grows at `F S_in = 2`, and the substrate stays nonnegative. -/
example (t : ℝ) (ht : 0 ≤ t) :
    1 + (0 : ℝ) ≤ 1 + t ∧
    HasDerivWithinAt (fun t ↦ (1 + t) * (2 * t / (1 + t)) + (1 + t) * 0 / 3) (1 * 2) (Ici 0) t ∧
    0 ≤ 2 * t / (1 + t) := by
  obtain ⟨h1, h2, h3⟩ := (sterileFeed_isSolution 1 1 3).substrate_biomass_account ordConnected_Ici
    self_mem_Ici one_pos one_pos zero_le_two three_pos (fun _ _ _ ↦ zero_le_one) (by norm_num)
    (by norm_num) le_rfl
  exact ⟨h1 t ht ht, h2 t ht ht, (h3 t ht ht).1⟩

/-- Without feed or biomass, every constant substrate level is a solution, a negative one
included: the hypothesis `S(0) ≥ 0` cannot be dropped from the nonnegativity clause. -/
theorem constant_isSolution (μ : ℝ → ℝ) (Sin Y S₀ : ℝ) (I : Set ℝ) :
    IsSolution μ Sin Y (fun _ ↦ 0) I (fun _ ↦ 1) (fun _ ↦ S₀) (fun _ ↦ 0) where
  hasDerivWithinAt_volume t _ := hasDerivWithinAt_const t I 1
  hasDerivWithinAt_substrate t _ := by simpa using hasDerivWithinAt_const t I S₀
  hasDerivWithinAt_biomass t _ := by simpa using hasDerivWithinAt_const t I (0 : ℝ)

/-- All other hypotheses of the account theorem hold for the constant solution `S = -1`, and
the substrate is negative at every time. -/
example : IsSolution (mmRate 1 1) 0 1 (fun _ ↦ 0) (Ici 0) (fun _ ↦ 1) (fun _ ↦ -1) (fun _ ↦ 0) ∧
    ∀ t ∈ Ici (0 : ℝ), (fun _ : ℝ ↦ (-1 : ℝ)) t < 0 :=
  ⟨constant_isSolution _ 0 1 (-1) _, fun _ _ ↦ by norm_num⟩

end DomainsTest.Chemistry.Bioreactors.FedBatch
