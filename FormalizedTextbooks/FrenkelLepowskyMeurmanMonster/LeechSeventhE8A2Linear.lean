/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A finite sum of root outer products detects its actual real span. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix

/-- The ordinary real sum of rank-one operators associated with a finite root family. -/
def leechSeventhRootOuterSum {ι n : Type*} [Fintype ι] [Fintype n]
    (u : ι → n → ℝ) : Module.End ℝ (n → ℝ) :=
  ∑ j, (dotProductBilin ℝ ℝ (u j)).smulRight (u j)

/-- The finite root outer sum acts by its actual scalar inner products. -/
theorem leechSeventhRootOuterSum_apply {ι n : Type*} [Fintype ι] [Fintype n]
    (u : ι → n → ℝ) (x : n → ℝ) :
    leechSeventhRootOuterSum u x = ∑ j, (u j ⬝ᵥ x) • u j := by
  simp [leechSeventhRootOuterSum]

/-- Every image of the genuine root outer sum belongs to the span of those roots. -/
theorem leechSeventhRootOuterSum_mem {ι n : Type*} [Fintype ι] [Fintype n]
    (u : ι → n → ℝ) (x : n → ℝ) :
    leechSeventhRootOuterSum u x ∈ Submodule.span ℝ (Set.range u) := by
  rw [leechSeventhRootOuterSum_apply]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- A nonzero scalar root eigenvalue makes the outer sum recognize the actual root span. -/
theorem leechSeventhRootOuterSum_span_iff {ι n : Type*} [Fintype ι] [Fintype n]
    (u : ι → n → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hroot : ∀ j, leechSeventhRootOuterSum u (u j) = c • u j) (x : n → ℝ) :
    x ∈ Submodule.span ℝ (Set.range u) ↔ leechSeventhRootOuterSum u x = c • x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact hroot j
    | zero => simp
    | add y z hy hz ihy ihz => simp only [map_add, ihy, ihz, smul_add]
    | smul a y hy ih => simp only [map_smul, ih, smul_smul, mul_comm]
  · intro hx
    have hm := (Submodule.span ℝ (Set.range u)).smul_mem c⁻¹
      (leechSeventhRootOuterSum_mem u x)
    rwa [hx, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
