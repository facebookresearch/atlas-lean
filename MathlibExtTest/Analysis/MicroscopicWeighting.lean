/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.MicroscopicWeighting

/-! # Tests for microscopic weightings of finite metric spaces -/

open MathlibExt.Analysis.MicroscopicWeightingWanted Matrix Filter

variable (X : Type*) [Fintype X] [DecidableEq X] [MetricSpace X]

-- On a singleton, the weighting is identically one at every scale.
example [Unique X] : HasMicroscopicWeighting X := by
  have h (t : ℝ) : similarityMatrix X t = 1 := by
    ext i j
    simp [similarityMatrix, Subsingleton.elim i j, Matrix.one_apply]
  refine ⟨1, ?_⟩
  change Tendsto (fun t => (similarityMatrix X t)⁻¹ *ᵥ 1) _ _
  simp [h]

-- The same singleton has a unit mass gauging with potential zero.
example [Unique X] : IsGauging X (distanceMatrix X) 1 0 := by
  constructor
  · simp
  · funext i
    simp [distanceMatrix, mulVec, dotProduct, Function.const, Subsingleton.elim i default]

-- At scale zero, two distinct rows coincide and the totalized inverse gives zero weighting.
example [Nontrivial X] : weighting X 0 = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne X
  have hdet : (similarityMatrix X 0).det = 0 := det_zero_of_row_eq hij (by
    funext k
    simp [similarityMatrix])
  rw [weighting, nonsing_inv_apply_not_isUnit _ (by simp [hdet]), zero_mulVec]
