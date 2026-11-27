/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.InnerProductSpace.NewtonianKernel

open MathlibExt.Analysis.Calculus.NormPowTwoSubDimHarmonicWanted

-- In dimension four the kernel is the inverse square of the norm, not the inverse norm.
example : InnerProductSpace.HarmonicOnNhd
    (fun x : EuclideanSpace ℝ (Fin 4) ↦ 1 / ‖x‖ ^ (2 : ℕ)) ({0}ᶜ) :=
  harmonicOnNhd_one_div_norm_pow_sub_two (m := 4) (by decide)
