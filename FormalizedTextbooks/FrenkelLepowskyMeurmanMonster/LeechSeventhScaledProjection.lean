/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhE8A2FlagTransport

/-! A nonzero scalar multiple of a symmetric projection is determined by its actual image. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- A scaled projection acts by its scale on the image of any operator with contained image. -/
theorem leechSeventh_scaledProjection_mul {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℝ) (c : ℝ) (hP : P * P = c • P)
    (hr : LinearMap.range (Matrix.toLin' Q) ≤ LinearMap.range (Matrix.toLin' P)) :
    P * Q = c • Q := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := hr (LinearMap.mem_range_self (Matrix.toLin' Q) x)
  change (P * Q) *ᵥ x = (c • Q) *ᵥ x
  rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
  change P *ᵥ y = Q *ᵥ x at hy
  rw [← hy, Matrix.mulVec_mulVec, hP, Matrix.smul_mulVec]

/-- Two symmetric nonzero scaled projections with the same actual image are equal. -/
theorem leechSeventh_scaledProjection_unique {n : Type*} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℝ) (c : ℝ) (hc : c ≠ 0)
    (hPs : P.transpose = P) (hQs : Q.transpose = Q)
    (hP : P * P = c • P) (hQ : Q * Q = c • Q)
    (hr : LinearMap.range (Matrix.toLin' P) = LinearMap.range (Matrix.toLin' Q)) : P = Q := by
  have hPQ := leechSeventh_scaledProjection_mul P Q c hP hr.symm.le
  have hQP := leechSeventh_scaledProjection_mul Q P c hQ hr.le
  have ht := congrArg Matrix.transpose hPQ
  simp only [Matrix.transpose_mul, Matrix.transpose_smul, hPs, hQs] at ht
  exact (smul_right_injective _ hc) (hQP.symm.trans ht)

/-- Actual orthogonal conjugation sends an operator's image to its genuine spatial image. -/
theorem leechSeventh_matrixAction_range (g : leechIsomSubgroup)
    (P : Matrix (Fin 24) (Fin 24) ℝ) :
    LinearMap.range (Matrix.toLin' (conwayMatrixAction g P)) =
      (LinearMap.range (Matrix.toLin' P)).map g.val.toLinearMap := by
  have hf : (Matrix.toLin' (conwayMatrixAction g P)).comp g.val.toLinearMap =
      g.val.toLinearMap.comp (Matrix.toLin' P) := by
    apply LinearMap.ext
    intro x
    exact conwayMatrixAction_mulVec g P x
  have h := congrArg LinearMap.range hf
  have hg : LinearMap.range g.val.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr g.val.surjective
  rw [LinearMap.range_comp, hg, Submodule.map_top, LinearMap.range_comp] at h
  exact h

/-- Fixing a genuine nonzero symmetric scaled projection is equivalent to fixing its image. -/
theorem leechSeventh_scaledProjection_fixed_iff (g : leechIsomSubgroup)
    (P : Matrix (Fin 24) (Fin 24) ℝ) (c : ℝ) (hc : c ≠ 0)
    (hPs : P.transpose = P) (hP : P * P = c • P) :
    conwayMatrixAction g P = P ↔
      (LinearMap.range (Matrix.toLin' P)).map g.val.toLinearMap =
        LinearMap.range (Matrix.toLin' P) := by
  constructor
  · intro h
    rw [← leechSeventh_matrixAction_range, h]
  · intro h
    apply leechSeventh_scaledProjection_unique _ P c hc
    · rw [← conwayMatrixAction_transpose, hPs]
    · exact hPs
    · rw [← conwayMatrixAction_mul, hP, map_smul]
    · exact hP
    · rw [leechSeventh_matrixAction_range, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
