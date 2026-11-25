/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.NewtonianKernel

/-!
# The function `1 / r` is harmonic in three dimensions away from `r = 0`

The flat Laplacian `Δ` of `y ↦ ‖y‖⁻¹` vanishes at every nonzero point of
`EuclideanSpace ℝ (Fin 3)`.

## i. Overview

In dimension three the Newtonian kernel `x ↦ 1 / ‖x‖ ^ (m - 2)` is `y ↦ ‖y‖⁻¹`, and a function
harmonic at a point has vanishing Laplacian near it. The result is therefore the case `m = 3` of
`harmonicOnNhd_one_div_norm_pow_sub_two`, which this module re-exports from
`MathlibExt.Analysis.InnerProductSpace.NewtonianKernel`.

## ii. Key results

- `MathlibExt.Analysis.laplacian_inv_norm_eq_zero`: `1 / r` is harmonic in
  three dimensions away from `r = 0`.

## iii. References

- `MathlibExt.Analysis.InnerProductSpace.NewtonianKernel`, which computes the Laplacian of the
  radial powers of the norm.
-/

@[expose] public section

open Laplacian

namespace MathlibExt.Analysis

/-- The function `1 / r` is harmonic in three dimensions away from `r = 0`:
its (flat) Laplacian vanishes at every nonzero point of
`EuclideanSpace ℝ (Fin 3)`. -/
theorem laplacian_inv_norm_eq_zero {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    Δ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖⁻¹) x = 0 := by
  have h := ((Calculus.NormPowTwoSubDimHarmonicWanted.harmonicOnNhd_one_div_norm_pow_sub_two
    (m := 3) (by norm_num)) x (Set.mem_compl_singleton_iff.mpr hx)).2.eq_of_nhds
  simpa only [Nat.reduceSub, pow_one, one_div, Pi.zero_apply] using h

end MathlibExt.Analysis
