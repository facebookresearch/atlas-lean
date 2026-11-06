/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagStabilizer
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisNormEightLineGeometry
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.CentralizerGeometryShortLines

/-! The actual flag matrix recognizes the full genuine section-line stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- The genuine coordinate section projection. -/
def generatedAxisE8ShortProjection (o : Fin 759) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.diagonal (fun i => if golayOctadWord o i = 0 then 0 else 1)

/-- The genuine short-line outer matrix. -/
def generatedAxisE8ShortOuter (r : GriessShortIndex) : Matrix (Fin 24) (Fin 24) ℝ :=
  Matrix.vecMulVec (griessShortVector r) (griessShortVector r)

/-- The actual short line is recognized exactly by its physical outer matrix. -/
theorem generatedAxisE8ShortOuter_fix_iff (g : leechIsomSubgroup) (r : GriessShortIndex) :
    conwayMatrixAction g (generatedAxisE8ShortOuter r) = generatedAxisE8ShortOuter r ↔
      griessShortPermutation g r = r := by
  unfold generatedAxisE8ShortOuter
  rw [conwayMatrixAction_short_outer]
  constructor
  · intro h
    have he := (generatedNormEight_outer_eq_iff _ _
      (centralizer_shortVector_ne_zero r)).mp h.symm
    exact centralizer_shortVector_sign_unique _ _ he
  · intro h
    rw [h]

/-- The coordinate projection is idempotent in the actual matrix ring. -/
theorem generatedAxisE8ShortProjection_square (o : Fin 759) :
    generatedAxisE8ShortProjection o * generatedAxisE8ShortProjection o =
      generatedAxisE8ShortProjection o := by
  have hd (c : Fin 24 → ZMod 2) :
      Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) *
          Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) =
        Matrix.diagonal (fun i => if c i = 0 then (0 : ℝ) else 1) := by
    rw [Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    by_cases h : c i = 0 <;> simp [h]
  exact hd (golayOctadWord o)

/-- Squaring the actual short outer matrix multiplies it by its physical squared norm four. -/
theorem generatedAxisE8ShortOuter_square (r : GriessShortIndex) :
    generatedAxisE8ShortOuter r * generatedAxisE8ShortOuter r =
      (4 : ℝ) • generatedAxisE8ShortOuter r := by
  have hn : griessShortVector r ⬝ᵥ griessShortVector r = 4 := griessShortVector_norm_sq r
  unfold generatedAxisE8ShortOuter
  rw [Matrix.vecMulVec_mul_vecMulVec, hn]
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- An incident actual short line has no physical coordinate outside the section. -/
theorem generatedAxisE8Short_incident_zero (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o)))
    (i : Fin 24) (hi : golayOctadWord o i = 0) : griessShortVector r i = 0 := by
  have hz : griessShortIntegral r i = 0 := hr i hi
  simp [griessShortVector, hz]

/-- The section projection acts as identity on the incident short outer matrix on the left. -/
theorem generatedAxisE8ShortProjection_mul_outer (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    generatedAxisE8ShortProjection o * generatedAxisE8ShortOuter r =
      generatedAxisE8ShortOuter r := by
  ext i j
  simp only [generatedAxisE8ShortProjection, Matrix.diagonal_mul]
  by_cases hi : golayOctadWord o i = 0
  · simp [hi, generatedAxisE8ShortOuter, Matrix.vecMulVec_apply,
      generatedAxisE8Short_incident_zero o r hr i hi]
  · simp [hi]

/-- The section projection also acts as identity on the right. -/
theorem generatedAxisE8ShortOuter_mul_projection (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    generatedAxisE8ShortOuter r * generatedAxisE8ShortProjection o =
      generatedAxisE8ShortOuter r := by
  ext i j
  simp only [generatedAxisE8ShortProjection, Matrix.mul_diagonal]
  by_cases hj : golayOctadWord o j = 0
  · simp [hj, generatedAxisE8ShortOuter, Matrix.vecMulVec_apply,
      generatedAxisE8Short_incident_zero o r hr j hj]
  · simp [hj]

/-- The concrete physical flag matrix fixes exactly the full actual flag stabilizer. -/
theorem generatedAxisE8ShortFlagMatrix_stabilizer_iff (o : Fin 759) (r : GriessShortIndex)
    (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) (g : leechIsomSubgroup) :
    conwayMatrixAction g (generatedAxisE8ShortFlagMatrix
        (generatedAxisE8ShortProjection o) (generatedAxisE8ShortOuter r)) =
      generatedAxisE8ShortFlagMatrix
        (generatedAxisE8ShortProjection o) (generatedAxisE8ShortOuter r) ↔
      g ∈ generatedAxisE8ShortFlagStabilizer o r := by
  rw [generatedAxisE8ShortFlagMatrix_fix_iff g _ _
    (generatedAxisE8ShortProjection_square o) (generatedAxisE8ShortOuter_square r)
    (generatedAxisE8ShortProjection_mul_outer o r hr)
    (generatedAxisE8ShortOuter_mul_projection o r hr),
    generatedAxisE8ShortOuter_fix_iff, generatedAxisE8ShortFlagStabilizer_mem]
  unfold generatedAxisE8ShortProjection
  rw [generatedAxisE8_matrix_action_iff_section_stabilizer]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
