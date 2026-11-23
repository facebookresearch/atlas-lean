/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Pow
import MathlibExt.Analysis.Complex.ContourIntegral

open MathlibExt.Analysis.Complex.ContourIntegralWanted

-- Integrating the derivative of z² from 0 to i gives i² = -1.
example :
    curveIntegral (fun z : ℂ => (2 * z) • ContinuousLinearMap.id ℂ ℂ)
      (Path.segment 0 Complex.I) = -1 := by
  have hγ : ContDiffOn ℝ 1 (Path.segment 0 Complex.I).extend (Set.Icc 0 1) :=
    (AffineMap.contDiff_lineMap _ _).contDiffOn.congr (Path.eqOn_extend_segment _ _)
  have hω : Continuous (fun z : ℂ => (2 * z) • ContinuousLinearMap.id ℂ ℂ) := by fun_prop
  have h := contourIntegral_of_hasDerivAt (F := fun z => z ^ 2) (f := fun z => 2 * z)
    isOpen_univ (Set.subset_univ _) (fun z _ => by simpa using hasDerivAt_pow 2 z)
    hγ (hω.continuousOn.curveIntegrable_of_contDiffOn (s := Set.univ) hγ (by simp))
  simpa using h

-- The integral of dz vanishes on every closed C¹ path.
example {a : ℂ} (γ : Path a a) (hγ : ContDiffOn ℝ 1 γ.extend (Set.Icc 0 1)) :
    curveIntegral (fun _ => ContinuousLinearMap.id ℂ ℂ) γ = 0 := by
  have h := contourIntegral_of_hasDerivAt (F := id) (f := fun _ => 1)
    isOpen_univ (Set.subset_univ _) (fun z _ => hasDerivAt_id z) hγ
    (continuousOn_const.curveIntegrable_of_contDiffOn (s := Set.univ) hγ (by simp))
  simpa using h
