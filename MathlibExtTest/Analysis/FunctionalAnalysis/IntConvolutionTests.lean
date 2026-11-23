/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.IntConvolution
import Mathlib.Analysis.Normed.Lp.lpSpace

@[expose] public section

namespace MathlibExtTest.Analysis.FunctionalAnalysis.IntConvolution

open MathlibExt.Analysis.FunctionalAnalysis.IntConvolution
open scoped ENNReal lp

-- The unit sequence acts as the identity on a coordinate vector in `ℓ²`.
example : l1Conv l1Delta (lp.single (E := fun _ : ℤ => ℂ) 2 3 (2 : ℂ))
    = lp.single (E := fun _ : ℤ => ℂ) 2 3 (2 : ℂ) :=
  l1Conv_delta_left _

-- The unit sequence acts as the identity on a coordinate vector in `ℓ^∞`.
example : l1Conv l1Delta (lp.single (E := fun _ : ℤ => ℂ) ⊤ 5 (3 : ℂ))
    = lp.single (E := fun _ : ℤ => ℂ) ⊤ 5 (3 : ℂ) :=
  l1Conv_delta_left _

-- Convolution of coordinate vectors: positions add, coefficients multiply.
example : l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 1 (2 : ℂ))
    (lp.single (E := fun _ : ℤ => ℂ) 2 2 (3 : ℂ))
    = lp.single (E := fun _ : ℤ => ℂ) 2 3 (6 : ℂ) := by
  have h := l1Conv_single_single (p := (2 : ℝ≥0∞)) 1 2 (2 : ℂ) (3 : ℂ)
  rw [show (1 : ℤ) + 2 = 3 from rfl, show (2 : ℂ) * 3 = 6 from by norm_num] at h
  exact h

-- The same computation at `p = ∞`.
example : l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 (-2) (2 : ℂ))
    (lp.single (E := fun _ : ℤ => ℂ) ⊤ 5 (3 : ℂ))
    = lp.single (E := fun _ : ℤ => ℂ) ⊤ 3 (6 : ℂ) := by
  have h := l1Conv_single_single (p := (⊤ : ℝ≥0∞)) (-2) 5 (2 : ℂ) (3 : ℂ)
  rw [show (-2 : ℤ) + 5 = 3 from rfl, show (2 : ℂ) * 3 = 6 from by norm_num] at h
  exact h

-- Convolution is commutative on the test vectors.
example : l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 1 (2 : ℂ))
    (lp.single (E := fun _ : ℤ => ℂ) 1 2 (3 : ℂ))
    = l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 2 (3 : ℂ))
      (lp.single (E := fun _ : ℤ => ℂ) 1 1 (2 : ℂ)) :=
  l1Conv_comm _ _

-- Convolution is associative on the test vectors.
example : l1Conv (l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 1 (2 : ℂ))
      (lp.single (E := fun _ : ℤ => ℂ) 1 2 (3 : ℂ)))
    (lp.single (E := fun _ : ℤ => ℂ) 1 (-1) (4 : ℂ))
    = l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 1 (2 : ℂ))
      (l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 2 (3 : ℂ))
        (lp.single (E := fun _ : ℤ => ℂ) 1 (-1) (4 : ℂ))) :=
  l1Conv_assoc _ _ _

-- The norm of a convolution of coordinate vectors is the product of the norms.
example : ‖l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 0 (2 : ℂ))
    (lp.single (E := fun _ : ℤ => ℂ) 2 1 (3 : ℂ))‖ = 6 := by
  have h := l1Conv_single_single (p := (2 : ℝ≥0∞)) 0 1 (2 : ℂ) (3 : ℂ)
  rw [show (0 : ℤ) + 1 = 1 from rfl, show (2 : ℂ) * 3 = 6 from by norm_num] at h
  rw [h, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  norm_num

-- The norm bound `‖f * g‖ ≤ ‖f‖ * ‖g‖` on the test vectors.
example : ‖l1Conv (lp.single (E := fun _ : ℤ => ℂ) 1 0 (2 : ℂ))
    (lp.single (E := fun _ : ℤ => ℂ) ⊤ 1 (3 : ℂ))‖
    ≤ ‖lp.single (E := fun _ : ℤ => ℂ) 1 0 (2 : ℂ)‖
      * ‖lp.single (E := fun _ : ℤ => ℂ) ⊤ 1 (3 : ℂ)‖ :=
  norm_l1Conv_le _ _

-- The convolution action has operator norm at most `1`, on `ℓ²`.
example : ‖l1ConvCLM (p := (2 : ℝ≥0∞))‖ ≤ 1 := norm_l1ConvCLM_le

-- The convolution action applied to test vectors is the convolution.
example : l1ConvCLM (lp.single (E := fun _ : ℤ => ℂ) 1 1 (2 : ℂ))
    (lp.single (E := fun _ : ℤ => ℂ) 2 2 (3 : ℂ))
    = lp.single (E := fun _ : ℤ => ℂ) 2 3 (6 : ℂ) := by
  rw [l1ConvCLM_apply]
  have h := l1Conv_single_single (p := (2 : ℝ≥0∞)) 1 2 (2 : ℂ) (3 : ℂ)
  rw [show (1 : ℤ) + 2 = 3 from rfl, show (2 : ℂ) * 3 = 6 from by norm_num] at h
  exact h

end MathlibExtTest.Analysis.FunctionalAnalysis.IntConvolution
