/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Control.Brockett
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MathlibExt.Analysis.Control
open scoped ContDiff

-- Brockett's condition rules out continuous stationary stabilisation of the integrator.
example : ¬ IsLocallyAsymptoticallyStabilizable nonholonomicIntegrator := by
  intro hstab
  apply not_brockettCondition_nonholonomicIntegrator
  refine NonlinearControlWanted.brockettCondition_of_isLocallyAsymptoticallyStabilizable
    nonholonomicIntegrator ?_ ?_ hstab
  · refine contDiff_pi.2 fun i => ?_
    fin_cases i <;> simp [nonholonomicIntegrator] <;> fun_prop
  · funext i
    fin_cases i <;> simp [nonholonomicIntegrator]
