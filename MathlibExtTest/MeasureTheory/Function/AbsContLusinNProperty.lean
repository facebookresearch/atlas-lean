/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.Function.AbsContLusinNProperty
import Mathlib.Analysis.Calculus.ContDiff.Operations

open MeasureTheory
open MathlibExt.MeasureTheory.AbsContLusinNPropertyWanted

-- Squaring need not be globally Lipschitz; no measurability or boundedness of `s` is assumed.
example (s : Set ℝ) (hs : volume s = 0) : volume ((fun x : ℝ => x ^ 2) '' s) = 0 := by
  have hSmooth : ContDiff ℝ 1 (fun x : ℝ => x ^ 2) := contDiff_id.pow 2
  exact volume_image_eq_zero_of_absolutelyContinuous _
    (fun _ _ => hSmooth.contDiffOn.absolutelyContinuousOnInterval) s hs
