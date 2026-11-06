/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingEighthExplicitFrameTransport
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagRecognition

/-! Exact actual spatial and projection matrices for the explicit one-eighth transport. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Independently recorded denominator-four matrix of the genuine spatial word. -/
def generatedFeasibleEighthExplicitSpatialNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
![
  ![3, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1],
  ![-1, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1],
  ![0, 0, 1, 1, 1, -1, 1, -1, 1, -1, -1, 1, 0, 0, 1, 1, -1, 0, 0, -1, 1, 0, 1, 0],
  ![0, 0, -1, 1, 1, 1, -1, 1, 1, 1, -1, 1, 0, 0, 1, -1, 1, 0, 0, -1, 1, 0, -1, 0],
  ![0, 0, 1, 1, -1, -1, -1, -1, 1, 1, 1, 1, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0, -1, 0],
  ![0, 0, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1, 0, 0, 1, 1, -1, 0, 0, -1, -1, 0, -1, 0],
  ![0, 0, -1, 1, -1, -1, 1, -1, -1, -1, 1, -1, 0, 0, 1, -1, 1, 0, 0, -1, 1, 0, -1, 0],
  ![0, 0, -1, -1, 1, -1, -1, 1, 1, -1, 1, -1, 0, 0, -1, -1, -1, 0, 0, -1, 1, 0, 1, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 3, -1, 0, 0, -1, 0, -1],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, -1, 0, 0, -1, 0, 3],
  ![0, 0, 1, -1, -1, -1, -1, 1, -1, -1, -1, 1, 0, 0, -1, 1, 1, 0, 0, -1, 1, 0, -1, 0],
  ![0, 0, -1, -1, -1, 1, 1, -1, -1, 1, -1, 1, 0, 0, -1, -1, -1, 0, 0, -1, 1, 0, 1, 0],
  ![0, 0, 1, -1, 1, -1, -1, -1, -1, 1, -1, -1, 0, 0, 1, -1, -1, 0, 0, 1, 1, 0, -1, 0],
  ![0, 0, -1, 1, -1, 1, -1, -1, 1, -1, -1, -1, 0, 0, -1, 1, -1, 0, 0, 1, 1, 0, -1, 0],
  ![0, 0, 1, -1, 1, 1, 1, -1, 1, 1, 1, -1, 0, 0, -1, 1, 1, 0, 0, -1, 1, 0, -1, 0],
  ![0, 0, 1, 1, -1, 1, -1, 1, -1, 1, 1, -1, 0, 0, 1, 1, -1, 0, 0, -1, 1, 0, 1, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 3, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1],
  ![0, 0, 1, 1, 1, 1, -1, -1, -1, -1, 1, 1, 0, 0, -1, -1, 1, 0, 0, 1, 1, 0, 1, 0],
  ![-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, -3, 0, 0, 1, 0, 1],
  ![0, 0, 1, -1, -1, 1, -1, -1, 1, -1, -1, -1, 0, 0, 1, -1, 1, 0, 0, -1, -1, 0, 1, 0],
  ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, -1, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1],
  ![0, 0, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 0],
  ![0, 0, -1, 1, 1, -1, -1, -1, -1, 1, -1, -1, 0, 0, -1, 1, 1, 0, 0, -1, -1, 0, 1, 0],
  ![-1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 0, -3, 0, 1]
]

/-- Independently recorded denominator-sixteen image of the original section projector. -/
def generatedFeasibleEighthExplicitProjectionNumerator : Matrix (Fin 24) (Fin 24) ℤ :=
![
  ![10, -6, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 2, 0, 0, -2],
  ![-6, 10, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 2, 0, 0, -2],
  ![0, 0, 6, -2, 2, -2, 2, -2, 0, 0, -2, -2, 2, -2, 2, -2, 0, 2, 0, -2, 0, -2, 2, 0],
  ![0, 0, -2, 6, -2, 2, -2, 2, 0, 0, -2, -2, -2, 2, -2, 2, 0, 2, 0, -2, 0, -2, 2, 0],
  ![0, 0, 2, -2, 6, -2, 2, -2, 0, 0, 2, -2, 2, 2, -2, 2, 0, 2, 0, 2, 0, 2, 2, 0],
  ![0, 0, -2, 2, -2, 6, -2, 2, 0, 0, -2, 2, 2, 2, 2, -2, 0, 2, 0, 2, 0, 2, 2, 0],
  ![0, 0, 2, -2, 2, -2, 6, -2, 0, 0, -2, 2, -2, 2, -2, -2, 0, -2, 0, -2, 0, 2, 2, 0],
  ![0, 0, -2, 2, -2, 2, -2, 6, 0, 0, 2, -2, 2, -2, -2, -2, 0, -2, 0, -2, 0, 2, 2, 0],
  ![2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 2, 0, 0, -2],
  ![2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 2, 0, 0, -2],
  ![0, 0, -2, -2, 2, -2, -2, 2, 0, 0, 6, -2, 2, -2, -2, 2, 0, -2, 0, 2, 0, 2, -2, 0],
  ![0, 0, -2, -2, -2, 2, 2, -2, 0, 0, -2, 6, -2, 2, 2, -2, 0, -2, 0, 2, 0, 2, -2, 0],
  ![0, 0, 2, -2, 2, 2, -2, 2, 0, 0, 2, -2, 6, -2, 2, -2, 0, 2, 0, 2, 0, 2, 2, 0],
  ![0, 0, -2, 2, 2, 2, 2, -2, 0, 0, -2, 2, -2, 6, -2, 2, 0, 2, 0, 2, 0, 2, 2, 0],
  ![0, 0, 2, -2, -2, 2, -2, -2, 0, 0, -2, 2, 2, -2, 6, -2, 0, 2, 0, 2, 0, -2, -2, 0],
  ![0, 0, -2, 2, 2, -2, -2, -2, 0, 0, 2, -2, -2, 2, -2, 6, 0, 2, 0, 2, 0, -2, -2, 0],
  ![2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 2, 0, 0, -2],
  ![0, 0, 2, 2, 2, 2, -2, -2, 0, 0, -2, -2, 2, 2, 2, 2, 0, 6, 0, 2, 0, -2, 2, 0],
  ![-2, -2, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, -2, 0, 2, 0, -2, 0, 0, 2],
  ![0, 0, -2, -2, 2, 2, -2, -2, 0, 0, 2, 2, 2, 2, 2, 2, 0, 2, 0, 6, 0, 2, -2, 0],
  ![2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 0, -2, 0, 2, 0, 0, -2],
  ![0, 0, -2, -2, 2, 2, 2, 2, 0, 0, 2, 2, 2, 2, -2, -2, 0, -2, 0, 2, 0, 6, 2, 0],
  ![0, 0, 2, 2, 2, 2, 2, 2, 0, 0, -2, -2, 2, 2, -2, -2, 0, 2, 0, -2, 0, 2, 6, 0],
  ![-2, -2, 0, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0, -2, 0, 2, 0, -2, 0, 0, 2]
]

/-- Every actual coordinate frame has the displayed image under the exact integral word. -/
theorem generatedFeasibleEighthExplicitSpatialNumerator_frames : ∀ i j : Fin 24,
    generatedFeasibleEighthExplicitIntegerAction (Pi.single j 8) i =
      2 * generatedFeasibleEighthExplicitSpatialNumerator i j := by
  decide +kernel

/-- The entire actual real spatial matrix is the recorded integer numerator divided by four. -/
theorem generatedFeasibleEighthExplicitSpatialNumerator_actual (i j : Fin 24) :
    leechIsomMatrix generatedFeasibleEighthExplicitSpatialWord i j =
      (generatedFeasibleEighthExplicitSpatialNumerator i j : ℝ) / 4 := by
  have h := congrFun (leechIntegralAction_embedding
    generatedFeasibleEighthExplicitSpatialWord (leechCoordinateFrameLattice j)) i
  have hn : leechCoordinateEmbedding (leechCoordinateFrameLattice j).val =
      (8 / Real.sqrt 8 : ℝ) • (Pi.single j 1 : Fin 24 → ℝ) := by
    funext k
    by_cases hk : k = j <;>
      simp [leechCoordinateEmbedding, leechCoordinateFrameLattice,
        leechCoordinateFrameVector, hk]
  rw [hn, map_smul] at h
  rw [generatedFeasibleEighthExplicitIntegerAction_actual] at h
  change (generatedFeasibleEighthExplicitIntegerAction (Pi.single j 8) i : ℝ) /
      Real.sqrt 8 = (8 / Real.sqrt 8) *
        leechIsomMatrix generatedFeasibleEighthExplicitSpatialWord i j at h
  rw [generatedFeasibleEighthExplicitSpatialNumerator_frames] at h
  push_cast at h
  have hs : Real.sqrt 8 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp at h ⊢
  linarith

/-- Every projector entry is exactly the sum of the first eight original spatial columns. -/
theorem generatedFeasibleEighthExplicitProjectionNumerator_certificate : ∀ i j : Fin 24,
    (∑ k : Fin 24, (if (golayEncodedMask 2063).testBit k.val then (1 : ℤ) else 0) *
      generatedFeasibleEighthExplicitSpatialNumerator i k *
        generatedFeasibleEighthExplicitSpatialNumerator j k) =
          generatedFeasibleEighthExplicitProjectionNumerator i j := by
  decide +kernel

/-- The actual image of the original E8 projection has every recorded rational coordinate. -/
theorem generatedFeasibleEighthExplicitProjectionNumerator_actual (i j : Fin 24) :
    conwayMatrixAction generatedFeasibleEighthExplicitSpatialWord
      (Matrix.diagonal (fun k : Fin 24 =>
        if (golayEncodedMask 2063).testBit k.val then (1 : ℝ) else 0)) i j =
          (generatedFeasibleEighthExplicitProjectionNumerator i j : ℝ) / 16 := by
  rw [generatedFeasibleContaining_projection_entry]
  simp_rw [generatedFeasibleEighthExplicitSpatialNumerator_actual]
  have hn : (∑ k : Fin 24,
      (if (golayEncodedMask 2063).testBit k.val then (1 : ℝ) else 0) *
        (generatedFeasibleEighthExplicitSpatialNumerator i k : ℝ) *
          (generatedFeasibleEighthExplicitSpatialNumerator j k : ℝ)) =
      (generatedFeasibleEighthExplicitProjectionNumerator i j : ℝ) := by
    exact_mod_cast generatedFeasibleEighthExplicitProjectionNumerator_certificate i j
  calc
    _ = (∑ k : Fin 24,
      (if (golayEncodedMask 2063).testBit k.val then (1 : ℝ) else 0) *
        (generatedFeasibleEighthExplicitSpatialNumerator i k : ℝ) *
          (generatedFeasibleEighthExplicitSpatialNumerator j k : ℝ)) / 16 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hn]

private theorem pairing_values :
    ∀ s : Fin 2, ∀ a b : Fin 24, a < b →
      (generatedFeasibleEighthExplicitProjectionNumerator a a +
        generatedFeasibleEighthExplicitProjectionNumerator b b +
        2 * (if s = 0 then (-1 : ℤ) else 1) *
          generatedFeasibleEighthExplicitProjectionNumerator a b = 32 ↔
      s = 0 ∧ (a, b) = (0, 1)) := by
  decide +kernel

/-- The only original coordinate pair contained in this actual section is the first minus root.
-/
theorem generatedFeasibleEighthExplicitProjectionNumerator_pair_characterization :
    ∀ s : Fin 2, ∀ p : Fin 276,
      generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).1 (griessCoordinatePair p).1 +
        generatedFeasibleEighthExplicitProjectionNumerator
          (griessCoordinatePair p).2 (griessCoordinatePair p).2 +
        2 * (if s = 0 then (-1 : ℤ) else 1) *
          generatedFeasibleEighthExplicitProjectionNumerator
            (griessCoordinatePair p).1 (griessCoordinatePair p).2 = 32 ↔
      s = 0 ∧ griessCoordinatePair p = (0, 1) := by
  intro s p
  exact pairing_values s _ _ (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
