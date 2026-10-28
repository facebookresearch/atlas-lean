/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQSupportUpper
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthTensorNonzero
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthQTriviality

/-! Genuine supported odd and tensor coefficients finish the original extraspecial kernel count. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The only free original quotient direction is literally the actual Omega translation. -/
theorem generatedTenth_Q_free_projection_column :
    (fun i => generatedTenthQSupportFreeProjection i 0) = Pi.single (11 : Fin 24) 1 := by
  decide +kernel

/-- Every full-axis original Q fixer has an Omega-only quotient. -/
theorem generatedTenth_Q_fixed_Omega_base (q : Q)
    (hq : rhoLocal (inclQ q) generatedTenthAxis = generatedTenthAxis) :
    ∃ b : ZMod 2, toAdd q.base = b • (Pi.single (11 : Fin 24) 1) := by
  let b := (generatedTenthQSupportFreeMatrix *ᵥ toAdd q.base) 0
  have h := generatedTenth_Q_support_free_quotient q hq
  have hv (v : Fin 1 → ZMod 2) :
      generatedTenthQSupportFreeProjection *ᵥ v =
        v 0 • (fun i => generatedTenthQSupportFreeProjection i 0) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.smul_apply,
      smul_eq_mul]
    exact mul_comm _ _
  rw [hv, generatedTenth_Q_free_projection_column] at h
  exact ⟨b, h.symm⟩

/-- Genuine nonzero odd and tensor coordinates eliminate every nonidentity original Q fixer. -/
theorem generatedTenth_Q_fixed_eq_one (q : Q)
    (hq : rhoLocal (inclQ q) generatedTenthAxis = generatedTenthAxis) : q = 1 := by
  obtain ⟨b, hb⟩ := generatedTenth_Q_fixed_Omega_base q hq
  exact generatedTenth_Q_eq_one_of_Omega_quotient generatedTenthAxis q hq b hb
    generatedTenth_odd_short_exists_nonzero generatedTenth_tensor_ne_zero

/-- The actual original full-axis extraspecial stabilizer is trivial. -/
theorem generatedTenth_axis_Q_stabilizer_eq_bot :
    generatedTenthAxisQStabilizer = ⊥ := by
  apply le_antisymm
  · intro q hq
    exact (Subgroup.mem_bot).mpr (generatedTenth_Q_fixed_eq_one q hq)
  · exact bot_le

/-- The genuine entire original extraspecial kernel has exactly one element. -/
theorem generatedTenth_axis_Q_stabilizer_card :
    Nat.card generatedTenthAxisQStabilizer = 1 := by
  rw [generatedTenth_axis_Q_stabilizer_eq_bot]
  simp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
