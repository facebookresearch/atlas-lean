/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2Linear
public import Mathlib.Tactic.FinCases

/-! Exact span comparisons for three roots with a nondegenerate signed relation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Two distinct roots span the whole triple when both relation coefficients are nonzero. -/
theorem leechSeventh_span_triple_pair (u : Fin 3 → V) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hw : u 2 = a • u 0 + b • u 1) (j k : Fin 3) (hjk : j ≠ k) :
    Submodule.span ℝ (Set.range u) = Submodule.span ℝ {u j, u k} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i,rfl⟩
    have h0 : u j ∈ Submodule.span ℝ {u j,u k} := Submodule.subset_span (by simp)
    have h1 : u k ∈ Submodule.span ℝ {u j,u k} := Submodule.subset_span (by simp)
    have hv : u 1 = b⁻¹ • (u 2 - a • u 0) := by
      rw [hw, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hb, one_smul]
    have hu : u 0 = a⁻¹ • (u 2 - b • u 1) := by
      rw [hw, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ha, one_smul]
    fin_cases j <;> fin_cases k <;> try contradiction
    all_goals fin_cases i <;> dsimp only at h0 h1 ⊢ <;> first
      | exact h0
      | exact h1
      | (exact hw.symm ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ h0)
          (Submodule.smul_mem _ _ h1))
      | (exact hw.symm ▸ Submodule.add_mem _ (Submodule.smul_mem _ _ h1)
          (Submodule.smul_mem _ _ h0))
      | (exact hv.symm ▸ Submodule.smul_mem _ _
          (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h0)))
      | (exact hv.symm ▸ Submodule.smul_mem _ _
          (Submodule.sub_mem _ h0 (Submodule.smul_mem _ _ h1)))
      | (exact hu.symm ▸ Submodule.smul_mem _ _
          (Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h0)))
      | (exact hu.symm ▸ Submodule.smul_mem _ _
          (Submodule.sub_mem _ h0 (Submodule.smul_mem _ _ h1)))
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl|rfl
    · exact Submodule.subset_span ⟨j,rfl⟩
    · exact Submodule.subset_span ⟨k,rfl⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
