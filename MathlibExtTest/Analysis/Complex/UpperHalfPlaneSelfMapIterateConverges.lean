/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapIterateConverges
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter MathlibExt.Analysis.Complex.UpperHalfPlaneSelfMapIterateConvergesWanted
open scoped Topology

/-- The affine map toward `I` with factor `7/8` satisfies the specified first iterate. -/
example : Tendsto (fun n : ℕ =>
    ((fun z : ℂ => (7 / 8 : ℂ) * z + (1 / 8 : ℂ) * Complex.I)^[n]) (2 * Complex.I))
    atTop (𝓝 Complex.I) := by
  let f (z : ℂ) := (7 / 8 : ℂ) * z + (1 / 8 : ℂ) * Complex.I
  apply tendsto_iterate_two_mul_I_of_fixed_I f
  · intro z hz
    dsimp only [f]
    norm_num [Complex.add_im, Complex.mul_im, Complex.div_re, Complex.div_im, Complex.normSq_apply]
    linarith
  · exact ((differentiableOn_const (7 / 8 : ℂ)).mul differentiableOn_id).add_const _
  · dsimp only [f]
    ring
  · dsimp only [f]
    ring
