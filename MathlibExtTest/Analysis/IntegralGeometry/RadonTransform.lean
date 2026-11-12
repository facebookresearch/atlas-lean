/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Analysis.IntegralGeometry.RadonTransform

@[expose] public section

open scoped ENNReal

namespace MathlibExtTest.Analysis.IntegralGeometry.RadonTransform

open MetaMathlibExt

-- Analysis 383: Euclidean Radon Transform

theorem euclideanRadonTransform_zero
    {n : ℕ}
    (ξ : EuclideanSpace ℝ (Fin n))
    (t : ℝ) :
    euclideanRadonTransform
        (fun _ : EuclideanSpace ℝ (Fin n) => 0) ξ t = 0 := by
  simp [euclideanRadonTransform]

-- Analysis 384: Sectional Volume Function

theorem sectionalVolume_neg_direction_neg_offset
    {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (ξ : EuclideanSpace ℝ (Fin n))
    (t : ℝ) :
    sectionalVolume K (-ξ) (-t) =
      sectionalVolume K ξ t := by
  simp [sectionalVolume]

end MathlibExtTest.Analysis.IntegralGeometry.RadonTransform

end
