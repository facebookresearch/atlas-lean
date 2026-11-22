/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.PDE.HeatKernelInitialValueBenchmark

open MathlibExt.Analysis.HeatKernelWanted.Analysis.ODE

-- The original public namespace and formula remain usable after promotion.
example (t x : ℝ) : heatSolution (fun _ => (2 : ℝ)) t x = 2 := by
  rw [heatSolution_eq_kernel]
  exact MathlibExt.Analysis.PDE.HeatKernel.heatSolution_const _ _ _

example (f : ℝ → ℝ) (x : ℝ) : heatSolution f 0 x = f x := by
  rw [heatSolution_eq_kernel]
  exact MathlibExt.Analysis.PDE.HeatKernel.heatSolution_zero _ _

-- The former wanted declaration is now a theorem using only the usual Lean axioms.
#print axioms heat_kernel_solves_heat_equation
