/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.MeasureTheory.ConvolutionIntegrandIntegrableEuclidean
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open MathlibExt.MeasureTheory.ConvolutionIntegrandIntegrableEuclideanWanted

-- Two different nonzero functions on the real line, whose integrand lives on ℝ².
example :
    let f := (Icc (0 : Fin 1 → ℝ) 1).indicator (fun _ => (2 : ℝ))
    let g := (Icc (1 : Fin 1 → ℝ) 3).indicator (fun _ => (-1 : ℝ))
    Integrable (fun p : Fin (1 + 1) → ℝ =>
      f (fun i : Fin 1 => p (Fin.castAdd 1 i) - p (Fin.natAdd 1 i)) *
      g (fun i : Fin 1 => p (Fin.natAdd 1 i))) := by
  dsimp only
  apply integrable_comp_sub_mul_of_integrable_fin_append (d := 1)
  all_goals
    apply (integrable_indicator_iff measurableSet_Icc).2
    refine integrableOn_const ?_ (by simp)
    rw [Real.volume_Icc_pi]
    simp
