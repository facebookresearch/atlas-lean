/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import MathlibExt.Analysis.Complex.DSlopeProd

set_option autoImplicit false

open Complex

-- The divided difference of `exp` is jointly continuous on `ℂ × ℂ` ...
example : ContinuousOn (fun p : ℂ × ℂ => dslope exp p.1 p.2) (Set.univ ×ˢ Set.univ) :=
  continuousOn_dslope_prod isOpen_univ differentiable_exp.differentiableOn

-- ... symmetric, equal to the derivative on the diagonal ...
example (z ζ : ℂ) : dslope exp z ζ = dslope exp ζ z := dslope_comm exp z ζ

example (z : ℂ) : dslope exp z z = exp z := by rw [dslope_same, Complex.deriv_exp]

-- ... and holomorphic in the first variable.
example (ζ₀ : ℂ) : DifferentiableOn ℂ (fun z => dslope exp z ζ₀) Set.univ :=
  differentiableOn_dslope_left isOpen_univ differentiable_exp.differentiableOn (Set.mem_univ ζ₀)

#print axioms continuousOn_dslope_prod
