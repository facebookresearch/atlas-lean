/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.Gradient
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.FDeriv.Linear

open MetaMathlibExt
open scoped Gradient

-- The chain rule for gradients through a map between Euclidean spaces.
example (f : EuclideanSpace ℝ (Fin 2) → ℝ) (g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2))
    (x : EuclideanSpace ℝ (Fin 3)) (hf : DifferentiableAt ℝ f (g x))
    (hg : DifferentiableAt ℝ g x) :
    ∇ (f ∘ g) x = ContinuousLinearMap.adjoint (fderiv ℝ g x) (∇ f (g x)) :=
  gradient_comp hf hg

-- A linear map: the gradient of `f ∘ L` is `L†` of the gradient of `f`.
example (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3))
    (hf : DifferentiableAt ℝ f (L x)) :
    ∇ (f ∘ L) x = ContinuousLinearMap.adjoint L (∇ f (L x)) := by
  rw [gradient_comp hf L.differentiableAt, L.fderiv]

#print axioms gradient_comp
