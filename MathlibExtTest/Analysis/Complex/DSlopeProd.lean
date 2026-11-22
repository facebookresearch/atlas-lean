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

open Complex Function

-- All three conclusions for `exp` on `ℂ`.
example : ContinuousOn (uncurry (dslope exp)) (Set.univ ×ˢ Set.univ) ∧
    (∀ z ∈ Set.univ, DifferentiableOn ℂ (fun ζ => dslope exp z ζ) Set.univ) ∧
    (∀ ζ ∈ Set.univ, DifferentiableOn ℂ (fun z => dslope exp z ζ) Set.univ) ∧
    ∀ z ∈ Set.univ, ∀ ζ ∈ Set.univ, dslope exp z ζ = dslope exp ζ z :=
  dslope_continuousOn_differentiableOn_comm isOpen_univ differentiable_exp.differentiableOn

-- On the diagonal the divided difference is the derivative.
example (z : ℂ) : dslope exp z z = exp z := by rw [dslope_same, Complex.deriv_exp]

-- Symmetry holds for any function, holomorphic or not.
example (f : ℂ → ℂ) (a b : ℂ) : dslope f a b = dslope f b a := dslope_comm f a b

#print axioms dslope_continuousOn_differentiableOn_comm
