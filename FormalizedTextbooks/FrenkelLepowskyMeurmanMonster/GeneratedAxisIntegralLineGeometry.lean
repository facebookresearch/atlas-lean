/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineGeometry

/-! Actual integral lattice lines, with both orientations retained in their stabilizers. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The full physical outer matrix of an actual integral Leech lattice vector. -/
def generatedIntegralLineMatrix (u : leechIntegral) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.vecMulVec (leechCoordinateEmbedding u.val) (leechCoordinateEmbedding u.val)

/-- Four-times integral directions give twice their integer outer matrices physically. -/
theorem generatedIntegralLineMatrix_four_coordinates (u : leechIntegral)
    (f : Fin 24 → ℤ) (hu : ∀ i, u.val i = 4 * f i) (i j : Fin 24) :
    generatedIntegralLineMatrix u i j = 2 * (f i : ℝ) * (f j : ℝ) := by
  change ((u.val i : ℝ) / Real.sqrt 8) * ((u.val j : ℝ) / Real.sqrt 8) = _
  rw [hu i, hu j]
  push_cast
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
  ring

/-- Every nonzero integral vector has a nonzero original physical embedding. -/
theorem generatedIntegralLineVector_ne_zero (u : leechIntegral) (hu : u ≠ 0) :
    leechCoordinateEmbedding u.val ≠ 0 := by
  intro h
  apply hu
  apply Subtype.ext
  apply leechCoordinateEmbedding_injective
  simpa using h

/-- Fixing the actual physical outer matrix is exactly preserving the two lattice orientations. -/
theorem generatedIntegralLineMatrix_fix_iff (e : leechIsomSubgroup)
    (u : leechIntegral) (hu : u ≠ 0) :
    conwayMatrixAction e (generatedIntegralLineMatrix u) = generatedIntegralLineMatrix u ↔
      leechIntegralAction e u = u ∨ leechIntegralAction e u = -u := by
  unfold generatedIntegralLineMatrix
  rw [conwayMatrixAction_vecMulVec, ← leechIntegralAction_embedding]
  constructor
  · intro h
    rcases (generatedNormEight_outer_eq_iff _ _
      (generatedIntegralLineVector_ne_zero u hu)).mp h.symm with h | h
    · left
      exact Subtype.ext (leechCoordinateEmbedding_injective h)
    · right
      rw [← leechCoordinateEmbedding.map_neg] at h
      exact Subtype.ext (leechCoordinateEmbedding_injective h)
  · rintro (h | h)
    · rw [h]
    · rw [h]
      simp only [Submodule.coe_neg, map_neg]
      ext i j
      simp [Matrix.vecMulVec]

/-- A nonzero scalar multiple has precisely the same actual line stabilizer. -/
theorem generatedIntegralLineMatrix_smul_fix_iff (e : leechIsomSubgroup)
    (u : leechIntegral) (hu : u ≠ 0) (c : ℝ) (hc : c ≠ 0) :
    conwayMatrixAction e (c • generatedIntegralLineMatrix u) = c • generatedIntegralLineMatrix u ↔
      leechIntegralAction e u = u ∨ leechIntegralAction e u = -u := by
  rw [map_smul]
  constructor
  · intro h
    exact (generatedIntegralLineMatrix_fix_iff e u hu).mp
      ((smul_right_injective _ hc) h)
  · intro h
    rw [(generatedIntegralLineMatrix_fix_iff e u hu).mpr h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
